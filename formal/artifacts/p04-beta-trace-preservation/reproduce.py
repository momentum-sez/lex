"""Validate the exact source snapshot in one fresh, isolated local build."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / "build"
SOURCES = BUILD / "sources"
EVIDENCE = BUILD / "evidence"
OWNED_EVIDENCE = False


def sha256(path):
    value = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def records(root):
    result = []
    for directory, dirs, files in os.walk(root, followlinks=True):
        dirs.sort()
        for name in sorted(files):
            path = Path(directory) / name
            result.append({"path": path.relative_to(root).as_posix(),
                           "size": path.stat().st_size,
                           "sha256": sha256(path)})
    return sorted(result, key=lambda entry: entry["path"])


def records_digest(entries):
    return hashlib.sha256(json.dumps(entries, sort_keys=True,
                                    separators=(",", ":")).encode()).hexdigest()


def identity_key(info):
    return {"compiler_version": info["compiler_version"],
            "checker_version": info["checker_version"],
            "binaries": {name: entry["sha256"] for name, entry in info["binaries"].items()},
            "libraries": {name: entry["tree_sha256"] for name, entry in info["libraries"].items()}}


def validate_input():
    manifest = json.loads((ROOT / "SOURCE-MANIFEST.json").read_text())
    for item in manifest["input_files"]:
        path = ROOT / item["path"]
        if not path.is_file() or sha256(path) != item["sha256"]:
            raise RuntimeError("Input hash mismatch: " + item["path"])
    expected = {entry["path"] for entry in manifest["proof_sources"]}
    actual = {path.relative_to(ROOT).as_posix()
              for folder in ["dependencies", "proof"]
              for path in (ROOT / folder).rglob("*.v")}
    if actual != expected:
        raise RuntimeError("The proof-source set differs from the manifest.")
    dependencies = json.loads((ROOT / "DEPENDENCIES.json").read_text())
    modules = dependencies["modules_in_build_order"]
    if len(modules) != 25 or {entry["path"] for entry in modules} != expected:
        raise RuntimeError("The module order does not cover the exact 25 sources.")
    if len({entry["module"] for entry in modules}) != len(modules):
        raise RuntimeError("The module order contains duplicate names.")
    for entry in modules:
        if sha256(ROOT / entry["path"]) != entry["sha256"]:
            raise RuntimeError("Dependency hash mismatch: " + entry["path"])
    return manifest, dependencies, modules


def build():
    global OWNED_EVIDENCE
    if sys.version_info < (3, 9):
        raise RuntimeError("Python 3.9 or later is required.")
    if Path.cwd().resolve() != ROOT:
        raise RuntimeError("Run this command from the extracted supplement directory.")
    manifest, dependencies, modules = validate_input()
    if BUILD.exists():
        raise RuntimeError("The build directory exists. Use a fresh extraction.")
    generated_suffixes = {".vo", ".vos", ".vok", ".glob", ".aux", ".cache"}
    if any(path.suffix in generated_suffixes for folder in ["dependencies", "proof"]
           for path in (ROOT / folder).rglob("*")):
        raise RuntimeError("The distributed source directories contain generated objects.")
    SOURCES.mkdir(parents=True, exist_ok=False)
    EVIDENCE.mkdir(exist_ok=False)
    OWNED_EVIDENCE = True
    for entry in manifest["proof_sources"]:
        target = SOURCES / entry["path"]
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / entry["path"], target)
    # A controlled system-only search path avoids private configuration directories.
    search_paths = ["/opt/homebrew/bin", "/usr/local/bin", "/usr/bin", "/bin",
                    "/usr/sbin", "/sbin", "/Library/Developer/CommandLineTools/usr/bin"]
    env = {"PATH": os.pathsep.join(search_paths), "LC_ALL": "C",
           "PYTHONDONTWRITEBYTECODE": "1", "TZ": "UTC"}
    write_json(EVIDENCE / "environment.json", {
        "variables": env,
        "compiler_startup_scripts": "Disabled by -q on every proof and assumption-audit compilation.",
        "working_directory": "build/sources",
        "preexisting_generated_objects": [],
        "source_input_manifest_sha256": sha256(ROOT / "SOURCE-MANIFEST.json")})
    commands = []

    def run(argv, name, output=EVIDENCE):
        output.mkdir(parents=True, exist_ok=True)
        start = time.monotonic()
        started = datetime.datetime.now(datetime.timezone.utc).isoformat()
        result = subprocess.run(argv, cwd=SOURCES, env=env, capture_output=True)
        stdout = output / (name + ".stdout")
        stderr = output / (name + ".stderr")
        stdout.write_bytes(result.stdout)
        stderr.write_bytes(result.stderr)
        entry = {"argv": argv, "cwd": "build/sources", "started_utc": started,
                 "elapsed_seconds": time.monotonic() - start,
                 "exit_code": result.returncode,
                 "stdout": stdout.relative_to(EVIDENCE).as_posix(),
                 "stderr": stderr.relative_to(EVIDENCE).as_posix(),
                 "stdout_sha256": sha256(stdout), "stderr_sha256": sha256(stderr)}
        commands.append(entry)
        write_json(EVIDENCE / "commands.json", commands)
        print(name, "exit", result.returncode, "seconds", round(entry["elapsed_seconds"], 2), flush=True)
        if result.returncode:
            raise RuntimeError("Command failed: " + name)
        return result.stdout, result.stderr, entry

    def toolchain(label):
        output = EVIDENCE / label
        output.mkdir(exist_ok=False)
        binaries = {}
        for name in ["coqc", "coqchk", "rocq", "rocqchk"]:
            found = shutil.which(name, path=env["PATH"])
            if found is None:
                raise RuntimeError("Missing executable: " + name)
            path = Path(found)
            binaries[name] = {"path": str(path), "resolved_path": str(path.resolve()),
                              "size": path.stat().st_size, "sha256": sha256(path)}
        version, _, _ = run([binaries["coqc"]["path"], "--version"], "compiler-version", output)
        checker, _, _ = run([binaries["coqchk"]["path"], "--version"], "checker-version", output)
        where, _, _ = run([binaries["coqc"]["path"], "-where"], "library-location", output)
        config, _, _ = run([binaries["coqc"]["path"], "-config"], "compiler-config", output)
        settings = dict(line.split("=", 1) for line in config.decode().splitlines() if "=" in line)
        coqlib = Path(where.decode().strip())
        locations = {"coqlib": coqlib, "runtime": Path(settings["COQCORELIB"]),
                     "stdlib": coqlib / "user-contrib/Stdlib"}
        libraries = {}
        for name, path in locations.items():
            if not path.is_dir():
                raise RuntimeError("Required library is absent: " + name)
            entries = records(path)
            write_json(output / (name + "-files.json"), entries)
            libraries[name] = {"path": str(path), "file_count": len(entries),
                               "tree_sha256": records_digest(entries),
                               "manifest": name + "-files.json"}
        info = {"compiler_version": version.decode(), "checker_version": checker.decode(),
                "binaries": binaries, "libraries": libraries,
                "platform": platform.platform(), "machine": platform.machine(),
                "python_version": sys.version, "python_executable": str(Path(sys.executable).resolve()),
                "python_sha256": sha256(Path(sys.executable).resolve())}
        write_json(output / "identity.json", info)
        return info

    before = toolchain("toolchain-before")
    pin = json.loads((ROOT / "PINNED-TOOLCHAIN.json").read_text())
    if identity_key(before) != pin:
        raise RuntimeError("The installed compiler or libraries differ from the exact pin.")
    flags = [item for entry in dependencies["logical_roots"]
             for item in ["-Q", entry["path"], entry["logical"]]]
    bindings = []
    reports = []
    for index, module in enumerate(modules, 1):
        source = SOURCES / module["path"]
        stdout, stderr, command = run([before["binaries"]["coqc"]["path"], "-q",
                                      *flags, module["path"]], "module-" + str(index).zfill(2))
        names = re.findall(r"^Print Assumptions\s+([\w.]+)\s*\.", source.read_text(), re.M)
        output_text = (stdout + stderr).decode()
        closed = len(re.findall(r"^Closed under the global context\s*$", output_text, re.M))
        if closed != len(names) or re.search(r"^Axioms:", output_text, re.M):
            raise RuntimeError("An assumption report is not closed: " + module["path"])
        objects = []
        for suffix in [".vo", ".vos", ".vok", ".glob"]:
            path = source.with_suffix(suffix)
            if not path.is_file():
                raise RuntimeError("Expected output absent: " + path.relative_to(SOURCES).as_posix())
            objects.append({"build_relative_path": path.relative_to(BUILD).as_posix(),
                            "size": path.stat().st_size, "sha256": sha256(path)})
        bindings.append({"source": module["path"], "source_sha256": sha256(source),
                         "module": module["module"], "generated_objects": objects,
                         "object_distribution": "Recorded by digest; generated objects are not distributed.",
                         "command": command, "compiler_sha256": before["binaries"]["coqc"]["sha256"],
                         "library_tree_sha256": {name: entry["tree_sha256"]
                                                 for name, entry in before["libraries"].items()}})
        reports.append({"source": module["path"], "module": module["module"],
                        "theorems_in_source_order": names, "closed_count": closed,
                        "axioms_heading": False, "command": command})
    exported_modules = ["P04BetaTrace.BetaTracePreservation", "P04BetaTrace.Examples"]
    kernel_reports = []
    for name, checked in [("kernel-exported", exported_modules),
                          ("kernel-all", [entry["module"] for entry in modules])]:
        stdout, stderr, command = run([before["binaries"]["coqchk"]["path"], "-silent", "-o",
                                      *flags, *checked], name)
        # The full raw checker output remains available for independent inspection.
        kernel_reports.append({"modules": checked, "command": command})
    expected = json.loads((ROOT / "ASSUMPTIONS.json").read_text())["expected_reports"]
    audit_lines = ["From P04BetaTrace Require Import BetaTracePreservation Examples."]
    audit_names = []
    for entry in expected:
        actual = next(report for report in reports if report["source"] == entry["source"])
        if actual["theorems_in_source_order"] != entry["closed_theorems"]:
            raise RuntimeError("The expected exported query list changed.")
        prefix = entry["module"]
        if prefix.endswith(".BetaTracePreservation"):
            prefix += ".BetaTracePreservation"
        for theorem in entry["closed_theorems"]:
            name = prefix + "." + theorem
            audit_names.append(name)
            audit_lines.extend(["Goal True. idtac \"BEGIN|" + name + "\". exact I. Qed.",
                                "Print Assumptions " + name + ".",
                                "Goal True. idtac \"END|" + name + "\". exact I. Qed."])
    audit_source = EVIDENCE / "AssumptionAudit.v"
    audit_source.write_text("\n".join(audit_lines) + "\n")
    stdout, stderr, audit_command = run([before["binaries"]["coqc"]["path"], "-q",
                                         *flags, "../evidence/AssumptionAudit.v"], "named-assumptions")
    output_lines = stdout.decode().splitlines()
    named = []
    for name in audit_names:
        start, end = "BEGIN|" + name, "END|" + name
        if output_lines.count(start) != 1 or output_lines.count(end) != 1:
            raise RuntimeError("A named assumption delimiter is absent or duplicated.")
        first, last = output_lines.index(start), output_lines.index(end)
        output = "\n".join(output_lines[first + 1:last]).strip()
        if output != "Closed under the global context":
            raise RuntimeError("An exported theorem has unexpected assumptions: " + name)
        named.append({"theorem": name, "output": output})
    write_json(EVIDENCE / "assumptions.json", reports)
    write_json(EVIDENCE / "named-assumptions.json", {
        "queries": named, "audit_source_sha256": sha256(audit_source), "command": audit_command})
    write_json(EVIDENCE / "source-object-bindings.json", bindings)
    write_json(EVIDENCE / "kernel-checks.json", kernel_reports)
    after = toolchain("toolchain-after")
    if identity_key(after) != identity_key(before):
        raise RuntimeError("The compiler or libraries changed during validation.")
    for entry in manifest["proof_sources"]:
        if sha256(SOURCES / entry["path"]) != entry["sha256"]:
            raise RuntimeError("A copied source changed during validation.")
    validate_input()
    if sum(report["closed_count"] for report in reports) != 119 or len(named) != 21:
        raise RuntimeError("The expected assumption report counts changed.")
    write_json(EVIDENCE / "result.json", {
        "schema": "lex-public-source-validation-v1", "status": "PASS",
        "source_input_manifest_sha256": sha256(ROOT / "SOURCE-MANIFEST.json"),
        "reproduction_wrapper_sha256": sha256(ROOT / "reproduce.py"),
        "source_modules": 25, "proof_module_compilations": 25,
        "separate_assumption_audit_compilations": 1, "kernel_checks": 2,
        "original_closed_assumption_reports": 119,
        "named_exported_closed_assumption_reports": 21,
        "source_files_unchanged": True, "toolchain_unchanged": True,
        "fresh_build_directory": True,
        "scope": "Fourteen-constructor source subrelation, with 42 excluded operational constructors.",
        "trace_scope": "Arbitrary finite traces under Formed.wf_context and Formed.has_type.",
        "historical_final_receipt_absent": True,
        "historical_object_reproduction_established": False,
        "cross_platform_binary_reproduction_established": False,
        "full_language_soundness_established": False,
        "compiler_runtime_correspondence_established": False,
        "public_immutable_locator": None})
    write_json(EVIDENCE / "GENERATED-FILES.json", records(BUILD))
    print("PASS: exact sources, fresh compilation, checker runs, assumptions and toolchain binding.", flush=True)


if __name__ == "__main__":
    try:
        build()
    except Exception as error:
        if OWNED_EVIDENCE:
            write_json(EVIDENCE / "FAILURE.json", {"error": str(error)})
        raise
