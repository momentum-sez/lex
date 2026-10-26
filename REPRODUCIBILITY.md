# Reproducibility

Verify the source revision under review. Record its commit, tool versions,
commands, exit status, failures, and skipped checks with the result.
A historical test count does not define acceptance for a later revision.

## Source and toolchain

The public repository is <https://github.com/momentum-sez/lex> and uses Apache-2.0.
A normal clone is self-contained:

```bash
git clone https://github.com/momentum-sez/lex.git
cd lex
git rev-parse HEAD
rustc --version
cargo --version
```

For an existing checkout, follow the isolated-worktree contract in `AGENTS.md`
and `CLAUDE.md`. Use the selected source commit and a unique branch and path.
Do not replace that commit with a branch name from an old verification record.

`rust-toolchain.toml` pins Rust `1.93.0` with `rustfmt` and `clippy`.
`Cargo.toml` declares the minimum Rust version and workspace members:
`lex-core`, `lex-diag`, `lex-cli`, `lex-pack`, and `mez-canonical`.
The in-tree `crates/mez-canonical/` supplies the shared canonical wire types.
No sibling checkout is required.

Inspect the selected revision's workflow files when reproducing CI.
Record the effective toolchain instead of assuming the workflow matches a local
installation. The Rocq workflow uses the `rocq/rocq:9.1` container.
The Lean scaffold has no CI job.

## Rust checks

Run these commands from the repository root:

```bash
cargo check --workspace --all-targets
cargo test --workspace --all-targets
cargo test --workspace --doc
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --all -- --check
```

Each required command must exit successfully. Report ignored tests and checks
that could not run. A different test count alone is not a regression.
Use Cargo's current output to identify the tests, rather than a copied census:

```bash
cargo test --workspace -- --list
```

Start with the affected crate when investigating a failure. Changes to shared
syntax, types, or certificates require the affected workspace checks.

## Examples and executable boundaries

```bash
cargo run --example hello-lex -p lex-core
cargo test -p lex-core --test discretion_hole_contract
```

`crates/lex-core/examples/hello-lex.rs` implements a director-count example.
It constructs an AST, checks types, extracts obligations, and assembles a
certificate. It does not verify appointments or statutory applicability.
The separate `formal/coq/Lex/Examples/SeychellesS130.v` example models different
inputs. Its result is not interchangeable with the Rust example's result.

The discretion-hole tests preserve the surface examples and verify rejection
by the ordinary admissible checker. They do not prove full-calculus safety.
Use `docs/language-reference.md` and current source for executable boundaries.

For determinism checks, inspect `crates/mez-canonical/src/canonical.rs` and
`crates/mez-canonical/src/digest.rs` with their tests.
Fix the input fields when comparing certificate digests. A changed timestamp
changes the serialized input.

## Formal checks

Record `coqc --version` and `lean --version` when using the respective tools.
Run each command below from the repository root:

```bash
(cd formal/coq && coqc LexCore.v)
(cd formal/lean && lean LexCore.lean)
```

These commands check the narrow scaffolds. They do not build or prove the
paper-level development. `formal/README.md` records proof scope and remaining
obligations. Check the named declarations before propagating a proof claim.

The paper-level source list is `formal/coq/_CoqProject`.
Generate its makefile and build in an isolated worktree:

```bash
(cd formal/coq && coq_makefile -f _CoqProject -o Makefile && make -B)
```

A forced build checks source instead of accepting pre-existing compiled files.
A successful build verifies the supplied statements under their assumptions.
It does not discharge named premises or prove the Rust implementation correct.

## Benchmarks

```bash
cargo bench -p lex-core --bench lex_pipeline
```

The harness is `crates/lex-core/benches/lex_pipeline.rs`.
Record hardware, toolchain, source revision, inputs, and warm or cold build state.
CI does not enforce a committed timing baseline.

## Historical results

The [retired April 2026 guide](docs/archive/reproducibility-2026-04-23.md)
preserves the earlier test census and machine timings.
Its old branch, crate names, example description, and proof-status claims were
superseded by the current manifest, example source, and formal source.
Report failures against the selected revision with reproducible commands.
