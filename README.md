# Lex

Lex is a typed rule language for jurisdictional compliance. The repository ships
the surface AST, lexer, parser, elaborator, admissible-fragment checker,
obligation extractor, and a frontier core calculus for typed discretion holes
and proof-carrying summaries.

## Public Documents

- `docs/language-reference.md` — canonical public language reference
- `docs/frontier-work/08-lex-core-calculus.md` — frontier design note for the
  core calculus and typed discretion-hole model
- `formal/README.md` — Coq and Lean scaffold status

## Current Execution Boundary

| Surface | Status |
| --- | --- |
| Lexer, parser, pretty-printer, elaborator | Shipped |
| Main admissible checker (`typecheck.rs`) | Shipped for the executable admissible fragment |
| Surface syntax for `? hole : T @ authority` and `fill(h, e, witness)` | Parsed and elaborated |
| Main admissible checker support for `Hole` and `HoleFill` | Not shipped; rejected as admissibility violations |
| Frontier typed discretion-hole model (`core_calculus::hole`) | Shipped as an opt-in research surface |
| Fiber composition entry point (`compose::evaluate_all_fibers`) | Stub; returns `Pending` verdicts |
| Formal scaffold | Coq and Lean compile; one certificate-invariant theorem remains open |

Typed discretion holes are a frontier core-calculus feature today. The surface
parser preserves the syntax, but the executable admissible checker still
rejects `Term::Hole` and `Term::HoleFill`. The canonical public statement of
that boundary is `docs/language-reference.md`.

## Repository Layout

```text
lex/
├── crates/
│   ├── lex-core/
│   ├── lex-diag/
│   └── lex-cli/
├── docs/
│   ├── language-reference.md
│   └── frontier-work/08-lex-core-calculus.md
├── examples/
├── formal/
├── ATTACK-REPORT.md
└── CLAUDE.md
```

## Examples

- `examples/discretion-hole-frontier.lex` — surface hole syntax preserved by
  parse and elaborate, then rejected by the main checker
- `examples/discretion-hole-fill-frontier.lex` — surface fill syntax preserved
  by parse and elaborate, then rejected by the main checker

## Build And Test

```bash
cargo check -p lex-core
cargo test -p lex-core
PROPTEST_CASES=20 cargo test -p lex-core --test proptest_typecheck -- --ignored depth_safety
```

The workspace currently expects a sibling `../kernel/mez/crates/mez-core`
checkout for `mez-core`.

## Formal Status

`formal/coq/LexCore.v` and `formal/lean/LexCore.lean` compile. The scaffold now
proves the oracle-totality and principle-termination obligations present in
this repository. The remaining open theorem is the certificate invariant that
ties `mechanical_check` to an empty discretion frontier; that theorem requires a
formal account of the Rust builder in `crates/lex-core/src/core_calculus/cert.rs`.

## License

Apache-2.0.
