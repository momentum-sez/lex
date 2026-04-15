# CLAUDE.md — Lex

Lex: A Logic for Jurisdictional Rules. Dependently-typed, effect-typed,
defeasible logic with temporal stratification, authority-relative interpretation,
and typed discretion holes.

**Paper:** "Lex: A Logic for Jurisdictional Rules" — research.momentum.inc

## Repository Structure

```
lex/
├── crates/
│   ├── lex-core/     # The Lex language — 22 modules, 470+ unit tests
│   │   ├── src/
│   │   │   ├── ast.rs           # Core AST types (Term, Sort, Level, Ident, QualIdent)
│   │   │   ├── certificate.rs   # Lex proof certificate issuance
│   │   │   ├── compose.rs       # Fiber composition
│   │   │   ├── debruijn.rs      # De Bruijn index assignment and substitution
│   │   │   ├── decide.rs        # Decision procedures
│   │   │   ├── decision_table.rs # Decision table compilation
│   │   │   ├── effects.rs       # Effect row algebra
│   │   │   ├── elaborate.rs     # Surface → core elaboration
│   │   │   ├── evaluate.rs      # Term evaluation
│   │   │   ├── fuel.rs          # Fuel-typed fibers (bounded evaluation budgets)
│   │   │   ├── levels.rs        # Universe level management
│   │   │   ├── lexer.rs         # Tokenizer
│   │   │   ├── obligations.rs   # Proof obligation tracking
│   │   │   ├── parser.rs        # Parser
│   │   │   ├── prelude.rs       # 363-symbol compliance prelude
│   │   │   ├── pretty.rs        # Pretty-printer
│   │   │   ├── principles.rs    # Principle conflict calculus
│   │   │   ├── smt.rs           # SMT integration
│   │   │   ├── temporal.rs      # Temporal stratification
│   │   │   ├── token.rs         # Token types
│   │   │   ├── tty.rs           # Accessibility text projection (screen readers)
│   │   │   └── typecheck.rs     # Bidirectional type checker
│   │   ├── tests/               # 5 integration test suites
│   │   └── benches/             # Criterion benchmarks
│   ├── lex-diag/     # Structured diagnostic ontology — 41 categories, 20 tests
│   └── lex-cli/      # Air-gapped command-line authoring tool
├── Cargo.toml        # Workspace root
└── CLAUDE.md         # This file
```

## Key Design Properties

1. **Defeasibility** — rules override other rules by priority (lex specialis, lex posterior)
2. **Temporal stratification** — stratum-0 (frozen historical) vs stratum-1 (derived legal)
3. **Authority-relative interpretation** — same rule text, different meaning per tribunal
4. **Typed discretion holes** — `? : T @ Authority` marks where computation stops and human judgment begins
5. **Principle conflict calculus** — acyclic priority DAG on PrincipleId × CaseCategory product graph
6. **Fuel-typed fibers** — bounded evaluation with Indeterminate verdict on exhaustion
7. **Effect typing** — path-indexed effect rows prevent privilege creep

## Dependency on mez-core

Lex depends on `mez-core` for foundational types (`ComplianceDomain`, `EntityId`, etc.).
This is a path dependency to `../kernel/mez/crates/mez-core`. When Lex is published
as a crate, `mez-core` will be published first.

## Test Suite

567 tests total:
- lex-core unit tests: 470+
- lex-core integration tests: 5 suites (ADGM rules, adversarial attacks, proof pipeline, proptest, Seychelles IBC)
- lex-diag: 20 tests
- Property-based testing via proptest (10 proptest tests verifying type soundness)

## Build

```bash
cargo check --workspace
cargo test --workspace
cargo clippy --workspace -- -D warnings
```

## lex-cli Commands

```bash
lex check <file.lex>           # Type-check a fiber
lex parse <file.lex>           # Parse and pretty-print AST
lex elaborate <file.lex>       # Surface → core elaboration
lex sign <file.lex> --key <k>  # Sign for air-gapped submission
lex verify <file.lex.signed>   # Verify signed fiber
lex check-principles <file>    # Check priority DAG acyclicity
```

## License

Apache-2.0. Lex is a contribution to human knowledge about legal logic —
not a proprietary implementation detail. Published as part of the Momentum
research programme at research.momentum.inc.
