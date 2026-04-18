# Lex

A logic for jurisdictional rules. Lex expresses legal rules as code in a
dependently-typed, effect-typed, defeasible calculus with temporal
stratification, authority-relative interpretation, and typed discretion holes.

A typed discretion hole is the primitive that makes Lex distinct from other
rule engines. When a rule reaches a point where no further mechanical inference
is sound and a human authority must decide, Lex marks that point with a hole
`? : T @ Authority`. The hole has a type, carries the authority required to
fill it, and appears explicitly in every proof. Machine derivation and human
judgment are separated in the object language, not after the fact.

Lex is Apache-2.0 and standalone — it has no runtime dependency on proprietary
infrastructure. The parser, type checker, evaluator, obligation tracker, and
CLI live in this repository. Lex takes foundational identifier and domain
types from `mez-core` (`EntityId`, `ComplianceDomain`), but the calculus, the
type system, and the proof pipeline are fully defined here.

## Design properties

- **Defeasibility.** Rules override other rules by priority. Lex specialis and
  lex posterior are first-class operators on a priority DAG; conflict
  resolution is a termination-bounded search, not a Prolog cut.
- **Temporal stratification.** Stratum 0 is frozen historical fact; stratum 1
  is derived legal state. Lift from 0 to 1 is total; demotion is not
  expressible.
- **Authority-relative interpretation.** The same rule text can mean different
  things under different tribunals. A `Proof<T, J, V, Tr>` carries
  `(Time, Jurisdiction, Version, Tribunal)` as phantom types; composition
  requires a matching 4-tuple or an explicit `TribunalCoercion` witness.
- **Typed discretion holes.** `Hole<T, A>` marks the frontier between
  computation and human judgment. A hole is filled only by a `HoleFill`
  signed by an authority whose jurisdiction matches `A`.
- **Principle conflict calculus.** Principles balance against each other on an
  acyclic DAG indexed by `(PrincipleId, CaseCategory)`. Cycles are detected
  at load time.
- **Fuel-typed fibers.** Every evaluation carries a finite fuel budget; an
  unverdict is a proper outcome of the calculus (`Indeterminate`), not a
  timeout exception.
- **Effect typing.** Effect rows are path-indexed. A fiber that reads
  `consent.level` cannot accidentally gain write access to `treasury.balance`
  through composition.

## Repository layout

```
lex/
├── crates/
│   ├── lex-core/             # Parser, type checker, evaluator, obligations, core calculus
│   │   ├── src/              # Library source
│   │   ├── tests/            # End-to-end ADGM, Seychelles IBC, adversarial, proptest suites
│   │   ├── benches/          # Criterion benchmarks
│   │   └── examples/         # Runnable examples (hello-lex)
│   ├── lex-diag/             # Structured diagnostic ontology with controlled-English messages
│   └── lex-cli/              # Command-line authoring tool with air-gapped signing
├── formal/
│   ├── coq/                  # Coq mechanisation of the nine design commitments
│   └── lean/                 # Lean 4 mirror of the Coq scaffold
├── docs/
│   ├── getting-started.md    # 5-minute cold-reader walk-through
│   ├── language-spec.md      # Language reference
│   └── frontier-work/        # Design notes for in-progress calculus extensions
├── Cargo.toml
└── LICENSE
```

## Quickstart

Clone, test, and run the end-to-end example in three commands:

```bash
git clone https://github.com/momentum-sez/lex.git
cd lex
cargo run --example hello-lex -p lex-core
```

The example walks a real statute (Seychelles International Business
Companies Act 2016 s.66) through the full Lex pipeline — AST construction,
De Bruijn indexing, temporal stratification, type checking, proof-obligation
extraction, obligation discharge, and content-addressed certificate issuance —
and then illustrates the typed discretion hole on a "fit and proper person"
judgment. Read the source at `crates/lex-core/examples/hello-lex.rs`.

The 5-minute cold-reader walk-through is at `docs/getting-started.md`. The
language reference is at `docs/language-spec.md`.

## Build

Lex requires Rust 1.93 or newer.

```bash
cargo check --workspace
cargo test --workspace
cargo clippy --workspace -- -D warnings
```

The crate layout uses a Cargo workspace with three members. `lex-core` is the
library; `lex-diag` is an optional structured-error layer that depends on
`lex-core`; `lex-cli` is the binary.

## Using the CLI

```bash
cargo build --release -p lex-cli
./target/release/lex check path/to/fiber.lex
./target/release/lex parse path/to/fiber.lex
./target/release/lex elaborate path/to/fiber.lex
./target/release/lex sign path/to/fiber.lex --key path/to/key
./target/release/lex verify path/to/fiber.lex.signed
./target/release/lex check-principles path/to/fiber.lex
```

The air-gapped workflow separates authoring from submission: write and
type-check a fiber on an offline machine, `lex sign` it with a hardware key,
transfer the signed artifact by physical media, and submit it to the target
kernel. `lex verify` checks the signature and the type before any kernel
accepts the fiber for evaluation.

## Examples

Runnable:

- `crates/lex-core/examples/hello-lex.rs` — the minimum-viable walk
  through every non-trivial calculus primitive. Run with
  `cargo run --example hello-lex -p lex-core`.

End-to-end test suites under `crates/lex-core/tests/`:

- `adgm_rules.rs` — Abu Dhabi Global Market rule fragments, exercising
  authority-relative interpretation.
- `seychelles_ibc_rules.rs` — International Business Companies rules,
  exercising temporal stratification across amendment histories.
- `proof_pipeline_e2e.rs` — parse → elaborate → typecheck → obligations →
  certificate for a multi-rule fiber.
- `adversarial_attacks.rs` — hostile inputs including level self-application,
  cyclic priorities, and unauthorised hole fills.
- `proptest_typecheck.rs` — property-based tests for type-system soundness.

## Formal mechanisation

`formal/coq/LexCore.v` and `formal/lean/LexCore.lean` declare the calculus's
nine design commitments as types in each proof assistant. The following
soundness lemmas are proved in both:

- Level non-self-application (no `Lt L L` inhabitant).
- Tribunal coercion shape (total refusal when canons diverge).
- Temporal lift totality (stratum 0 → stratum 1 is total; demotion is not
  expressible).
- Hole authorisation (a `HoleFill` witness implies signer jurisdiction
  matched the hole's authority).
- Summary preservation (obligations, verdict, and discretion frontier are
  preserved by `compile_summary`).
- Admissible-fragment decidability (both directions).

Three theorems remain admitted with declared proof strategies:
principle-balancing termination (Tarjan SCC), certificate well-formedness
(`WellFormedDC` predicate), and oracle boundedness (axiomatic, the oracle's
declared contract). Details in `formal/README.md`.

## Relation to Op

Op is Lex's dual — the operational effect language that AI agents use to
execute what Lex admits. Lex decides whether a state transition is admissible;
Op actually performs the transition, emitting syscalls against a kernel.
The two languages share effect rows and the proof-summary layer. Op has its
own repository at `github.com/momentum-sez/op`.

## Contributing

Pull requests and issues are welcome. Before submitting:

1. Run `cargo test --workspace` and `cargo clippy --workspace -- -D warnings`.
   Both must pass.
2. Add at least one test for any new calculus construct. New AST nodes
   require parser, elaborator, and type-checker coverage.
3. If you change a type rule, update `formal/coq/LexCore.v` and
   `formal/lean/LexCore.lean` to match. Admitted lemmas are acceptable for
   work-in-progress; regressions are not.
4. Commit messages describe intent, not implementation. The author is the
   human operator.

Discussion happens on GitHub issues. For larger design changes, open an issue
first so the direction can be discussed before the code lands.

## Citing

If you use Lex in academic work, cite the companion paper:

> *Lex: A Logic for Jurisdictional Rules.* Momentum research programme,
> research.momentum.inc.

## License

Apache-2.0. See [LICENSE](LICENSE).
