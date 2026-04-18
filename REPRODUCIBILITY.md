# Reproducibility

This document specifies the exact procedure for reproducing every executable
claim in this repository. A reviewer with the listed hardware and toolchain
should obtain bit-identical or functionally-identical results.

## Repository

- URL: <https://github.com/momentum-sez/lex>
- Branch: `frontier/core-calculus`
- License: Apache-2.0 (`LICENSE`)

## Clone

```
git clone https://github.com/momentum-sez/lex.git
cd lex
git checkout frontier/core-calculus
```

The workspace is self-contained. `crates/mez-core-min` vendors the subset of
the kernel `mez-core` crate that Lex depends on (`CanonicalBytes`,
`sha256_digest`, `ComplianceDomain`), so a cold clone compiles without any
sibling kernel checkout.

An optional feature `kernel-integration` on `lex-core` swaps the vendored
types for the full kernel `mez-core` at `../../../kernel/mez/crates/mez-core`.
This feature is off by default. CI does not enable it. Enabling it requires a
sibling `kernel/` checkout and is useful only for ecosystem builds that want
byte-identical shared infrastructure across Lex and the kernel.

## Toolchain

Rust toolchain is pinned by `rust-toolchain.toml` at the repository root:

- Channel: `1.93.0` (stable)
- Components: `rustfmt`, `clippy`
- Profile: `minimal`

`rustup` honors this file automatically. The workspace MSRV declared in
`Cargo.toml` is `1.93`, matching the pin.

Coq mechanization is checked against:

- Rocq Prover `9.0+` (the container image `rocq/rocq:9.1` is used by CI).

## Expected results

### Rust workspace

```
cargo test --workspace
```

Expected: `742` tests pass across the four crates `lex-core`, `lex-diag`,
`lex-cli`, `mez-core-min`. Zero failures.

Breakdown by binary at the time this document was written:

| Binary | Passed | Notes |
|---|---|---|
| `lex-core` unit tests | 590 | |
| `lex-core` integration: `adgm_rules` | 12 | ADGM jurisdictional fiber |
| `lex-core` integration: `adversarial_attacks` | 31 | level self-application, cyclic priorities, unauthorised fills |
| `lex-core` integration: `cycle3_admissibility_properties` | 3 | |
| `lex-core` integration: `discretion_hole_contract` | 2 | frontier-boundary contract tests |
| `lex-core` integration: `proof_pipeline_e2e` | 1 | parse → elaborate → typecheck → obligations → certificate |
| `lex-core` integration: `proptest_typecheck` | 10 + 1 ignored | soundness proptests |
| `lex-core` integration: `seychelles_ibc_rules` | 22 | Seychelles IBC fiber |
| `lex-diag` unit tests | 20 | |
| `mez-core-min` unit tests | 44 | |
| `lex-core` doc-tests | 6 | |
| `mez-core-min` doc-tests | 1 | |

### Clippy and rustfmt

```
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --all -- --check
```

Expected: both exit `0` with no output.

### Hello-lex example

```
cargo run --example hello-lex -p lex-core
```

Expected: the example walks the Seychelles International Business Companies
Act 2016 s.66 — first-shareholder-meeting requirement — through the full Lex
pipeline, emits a certificate with a content-addressed digest, then
constructs a typed discretion hole for `fit_and_proper : Prop @ regulator`
and extracts two scope obligations (`DomainMembership`, `TemporalOrdering`).

The rule digest and certificate digest are content-addressed over canonical
serialization and are stable across runs on a fixed toolchain. The `issued
at` timestamp is clock-stamped and will vary per run.

### Discretion-hole contract tests

```
cargo test -p lex-core --test discretion_hole_contract
```

Expected:

```
running 2 tests
test surface_fill_example_is_preserved_then_rejected_by_main_checker ... ok
test surface_hole_example_is_preserved_then_rejected_by_main_checker ... ok

test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured
```

### Coq mechanization

```
cd formal/coq
coqc LexCore.v
```

Exits `0` with one deprecation warning on Rocq `9.1.1`
(`From Coq` → `From Stdlib`). The file admits the oracle-totality and
principle-termination obligations; proof strategies for each are declared in
`formal/README.md`.

A CI job runs the `coqc` command in the `rocq/rocq:9.1` container on every
push that touches `formal/coq/**`.

### Formal artifacts (Lean)

```
formal/lean/LexCore.lean
```

The Lean mirror is provided as a scaffold. A Lean toolchain is not wired into
CI.

## Benchmarks

```
cargo bench -p lex-core --bench lex_pipeline
```

The Criterion harness at `crates/lex-core/benches/lex_pipeline.rs` measures
parse, elaborate, typecheck, and obligation-extraction throughput on the
Seychelles IBC Act and ADGM fixtures. Absolute timings are hardware-dependent
and no committed baseline is enforced by CI.

## Hardware and timing

The numbers below are indicative. CI runs on `ubuntu-latest` GitHub-hosted
runners.

| Step | Cold (macOS M-series, 10-core) | Warm (macOS M-series, 10-core) |
|---|---|---|
| `cargo check --workspace` | ~40 s | ~3 s |
| `cargo test --workspace` (build + run) | ~90 s | ~6 s |
| `coqc LexCore.v` | ~4 s | ~4 s |
| `cargo run --example hello-lex -p lex-core` (first run) | ~10 s | <1 s |

Disk footprint for the compiled `target/` directory is ~1.2 GB.

## Determinism

- Canonical serialization (`CanonicalBytes`) and `sha256_digest` are exercised
  against golden vectors at `crates/mez-core-min/src/{canonical,digest}.rs`
  including a kernel-golden vector.
- `ComplianceDomain` wire-format round-trips through 44 unit tests; the 23
  domains are an invariant checked by `all_returns_23_domains` and
  `domain_count_invariant`.
- Certificate digests are reproducible across runs on a fixed toolchain for a
  fixed source (timestamps excluded).

## Environment

The workspace compiles and tests cleanly on:

- Ubuntu 22.04 / 24.04 (x86_64)
- macOS 13+ (Apple Silicon)

No network access is required after the initial `cargo fetch`. The workspace
has no network-dependent tests.

## Issues

If `cargo test --workspace` reports a count other than `742` passed, or if any
example deviates from the output above, please open an issue at the repository
with the full `rustc --version`, `cargo --version`, and platform information.
