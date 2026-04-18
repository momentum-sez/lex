# Attack Report

Date: 2026-04-17
Path chosen: B

## Verdict

Lex is materially closer to publication-readiness after this pass. The public
claim set is now aligned with what the repository actually executes, the formal
scaffolds close the obligations that are provable from the current definitions,
the repo has a canonical public language reference, and the slowest property
test is configurable. The remaining gaps are explicit rather than implied.

## Blocker Status

### Typed discretion holes in the main checker — NARROWED

The public docs now state the exact boundary:

- the surface parser and elaborator preserve `Hole` and `HoleFill`
- the main admissible checker rejects them
- the typed discretion-hole model lives in `core_calculus::hole`

Regression coverage now exercises the full parse -> elaborate -> check path on
`examples/discretion-hole-frontier.lex` and
`examples/discretion-hole-fill-frontier.lex`, and asserts the exact
admissibility failures. This closes the public contradiction without claiming
main-checker support that the current AST and checker do not yet provide.

### Frontier core calculus not load-bearing in production composition — NARROWED

`README.md`, `docs/language-reference.md`, and
`crates/lex-core/src/core_calculus/mod.rs` now say directly that:

- the frontier core calculus is opt-in
- `compose::evaluate_all_fibers` is still a stub that returns `Pending`
- the frontier calculus is not the production execution path yet

This removes the publication blocker created by implying the frontier calculus
already drives the shipped pipeline.

### Formal scaffold-grade proofs — NARROWED

Closed in both assistants:

- principle-balancing termination at the scaffold level
- oracle totality from the class/function definition

Remaining open:

- `mechanical_bit_correct`

Rationale: the theorem is false for the current formal record shape unless the
Rust builder invariant from `core_calculus/cert.rs` is modeled explicitly. The
file comments and formal README now say that directly.

### Canonical public language reference missing — CLOSED

Added:

- `README.md`
- `docs/language-reference.md`

Updated stale references in the core modules to point at the canonical language
reference instead of missing `docs/architecture/*` files. The frontier design
note now labels itself as a frontier document rather than the public language
reference.

### Long-running property test — NARROWED

`crates/lex-core/tests/proptest_typecheck.rs` now:

- reads `PROPTEST_CASES` from the environment
- lowers the checked-in default case counts across the property file
- disables file persistence for the property harness
- moves the recursive `depth_safety` search behind `#[ignore]`
- adds a deterministic default-suite smoke test for deep recursion

Baseline signal: the original `depth_safety` property emitted the Rust test
runner's "running for over 60 seconds" warning. After this change the stress
property is no longer part of the default test path, and CI can raise
`PROPTEST_CASES` plus run `--ignored depth_safety` when it wants heavier
coverage. The mitigation is in place; further tuning may still be useful once
the proptest binary is profiled directly outside this harness.

## Remaining Publication Gaps

- Main-checker support for typed holes still requires an executable hole
  environment plus a checker-visible PCAuth witness type.
- `compose::evaluate_all_fibers` still needs a real evaluation path.
- Certificate well-formedness still needs a formal model of the Rust builder.
