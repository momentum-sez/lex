# Lex source-trace proof supplement

This supplement supplies the source-conversion and finite-trace proofs cited in Section 11 of *Lex: A Logic for Jurisdictional Rules*.

The 25 proof modules retain their exact source bytes. `SOURCE-MANIFEST.json` records each source path and SHA-256 digest. `DEPENDENCIES.json` gives the complete import structure and compilation order. The eight dependency directories and `proof/` directory provide nine logical import roots.

The preserved result covers the fourteen-constructor source subrelation under `Formed.wf_context` and `Formed.has_type`. It applies to arbitrary finite traces of that relation. The constructor bound does not bound trace length. `COVERAGE.json` retains the exact fourteen included and forty-two excluded operational constructors. Full-language soundness and compiler/runtime correspondence remain open.

## Reproduce the source validation

Install Python 3.9 or later and the exact toolchain identified by `PINNED-TOOLCHAIN.json`. The recorded installation uses Rocq 9.1.1, compiled with OCaml 5.4.1. Its installed recipe names Stdlib 9.0.0. `TOOLCHAIN-REQUIREMENTS.json` supplies the installation requirements and exact source-release identifiers. A current package-manager installation or matching version string does not establish the required binary and library identities.

Extract the supplement into a new directory. Open a terminal in `lex-proof-supplement/`, then run:

```sh
python3 -I reproduce.py
```

The wrapper verifies all input hashes and the exact proof-source set before it creates `build/`. It rejects a pre-existing build directory. It copies the 25 source modules into `build/sources/` and compiles only those new copies. Every command uses relative source and import paths. The `-q` option disables user startup scripts for each compilation.

The wrapper checks the pinned compiler and installed-library bytes before and after compilation. It compiles all 25 source modules, checks both final modules and all 25 modules with the Rocq proof checker, and records 119 original assumption reports. A separate query driver records the 21 named exported reports. These 21 reports repeat exported source queries; they are not 21 additional theorem claims.

A successful run writes commands, raw command outputs, source/object bindings, compiler identities, complete installed-library manifests, assumption reports and `result.json` under `build/evidence/`. The result binds generated object hashes to the exact source bytes and compiler used. Generated objects stay in the local build directory and are not part of the distributed supplement.

## Recorded evidence

The distributed `evidence/` directory records one fresh extraction of this exact source and wrapper snapshot. Those records are distinct from a reader's later `build/evidence/`. `evidence/commands.json` supplies actual relative command arguments and their working-directory relation to the extracted package. Captured command outputs retain their exact recorded bytes. The public package omits old compiled objects, private source locations and raw historical custody records. Its source manifest permits a direct byte comparison with the inputs of the recorded build.

`evidence/assumptions.json` indexes all original source queries. `evidence/named-assumptions.json` identifies every exported query and its complete output. `evidence/source-object-bindings.json` records the newly generated object identities. Those objects are identified by digest, rather than bundled. Complete before/after library manifests identify the installed files used by the compiler.

The source retains one historical `Abort` for an abandoned proof attempt. Its replacement proof follows in the same file. This does not introduce an admitted lemma into the reported closed results.

## Limits and distribution

The historical final receipt remains absent. The present records do not establish earlier compiler/source/object bindings retroactively. Exact historical-object reproduction and cross-platform binary reproduction remain unestablished. Rebuilding requires the pinned installed toolchain; the supplement does not install or redistribute it.

The archive digest identifies the delivered bytes. A public immutable locator remains a separate publication requirement. Preparation of this supplement does not itself establish that it has been published. The recorded checks establish the stated finite formal-model results and their exact source evidence. They do not establish whole-language soundness, compiler/runtime correspondence, institutional execution or whole-paper acceptance.

The associated open-source repository is `https://github.com/momentum-sez/lex`. The archive remains self-contained through its explicit import paths and source manifest.

See `NOTICE.txt` for file-specific attribution and license coverage. `LICENSE` retains the terms furnished with the three inherited Lex files. `LICENSE-CONTRIBUTIONS.txt` contains the standard Apache-2.0 text for new contributions under the existing Lex contribution contract.
