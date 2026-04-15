# CLAUDE.md — Lex

Lex: A Logic for Jurisdictional Rules. Dependently-typed, effect-typed,
defeasible logic with temporal stratification, authority-relative interpretation,
and typed discretion holes.

## Repository Structure

This repo contains Lex as an independent language primitive. It is published
separately from the Mass kernel because Lex is a contribution to human knowledge
about legal logic — not a proprietary implementation detail.

```
lex/
├── crates/
│   ├── lex-core/     # The Lex language (parser, type checker, evaluator, proofs)
│   └── lex-diag/     # Structured diagnostic ontology for Lex elaboration errors
├── Cargo.toml        # Workspace root
└── CLAUDE.md         # This file
```

## Dependency on mez-core

Lex depends on `mez-core` for foundational types (`ComplianceDomain`, `EntityId`, etc.).
This is a path dependency to `../kernel/mez/crates/mez-core`. When Lex is published
as a crate, `mez-core` will be published first.

## Build

```bash
cargo check --workspace
cargo test --workspace
cargo clippy --workspace -- -D warnings
```

## License

Apache-2.0. This is an open-source contribution.
