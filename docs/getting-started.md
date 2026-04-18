# Getting started with Lex

Five minutes, cold clone to running example.

Lex is a dependently-typed logic for jurisdictional rules. Its primitives —
defeasibility, temporal stratification, authority-relative interpretation,
and typed discretion holes — are first-class objects of the calculus. A rule
that type-checks in Lex composes correctly, separates machine derivation
from human judgment, and produces a content-addressed compliance certificate.

## Prerequisites

Rust 1.93 or newer.

```bash
rustc --version
```

If the installed toolchain is older, install `rustup` and run
`rustup install stable`.

## Clone and test

```bash
git clone https://github.com/momentum-sez/lex.git
cd lex
cargo test --workspace
```

The full suite runs the parser, type checker, evaluator, obligation
extractor, certificate builder, and the ADGM and Seychelles IBC rule
fragments. The admissible-fragment soundness proofs are mechanized in
`formal/coq/LexCore.v` and `formal/lean/LexCore.lean`.

## Run the end-to-end example

```bash
cargo run --example hello-lex -p lex-core
```

The example walks the Seychelles International Business Companies Act 2016
section 66 rule (minimum directors) end to end:

1. constructs the defeasible rule as an AST,
2. assigns De Bruijn indices and verifies temporal stratification,
3. type-checks the rule against the compliance prelude,
4. extracts proof obligations,
5. discharges the obligations against concrete incorporation facts,
6. issues a content-addressed compliance certificate,
7. illustrates a typed discretion hole — the Lex primitive that marks
   the frontier between machine derivation and human judgment — and the
   proof obligations emitted from the hole's scope.

Read `crates/lex-core/examples/hello-lex.rs` alongside the output. Every
line is either a construction step or a pipeline invocation; the
annotations in the source explain what each call does and why.

## Write the first rule

A Lex rule is a closed term of type
`IncorporationContext -> ComplianceVerdict` (or any other type in the
calculus; the compliance prelude gives common names standing). The
smallest meaningful rule is a defeasible match on a single accessor:

```rust
Term::Defeasible(DefeasibleRule {
    name: Ident::new("min_directors"),
    base_ty: Box::new(Term::pi(
        "ctx",
        Term::constant("IncorporationContext"),
        Term::constant("ComplianceVerdict"),
    )),
    base_body: Box::new(Term::lam(
        "ctx",
        Term::constant("IncorporationContext"),
        Term::match_expr(
            Term::app(Term::constant("director_count"), var("ctx", 0)),
            Term::constant("ComplianceVerdict"),
            vec![
                branch_ctor("Zero", Term::constant("NonCompliant")),
                branch_wildcard(Term::constant("Compliant")),
            ],
        ),
    )),
    exceptions: Vec::new(),
    lattice: None,
})
```

The term is a program. Pass it to `debruijn::assign_indices` to resolve
variable references, to `temporal::check_temporal_stratification` to
enforce the stratum-0 / stratum-1 barrier, to `typecheck::infer` to derive
its type under the compliance prelude, and to
`obligations::extract_obligations` to collect the structural proof
obligations the rule generates. Discharge each obligation via the
decision procedures in `decide` (finite-domain enumeration,
Presburger-arithmetic threshold checks, boolean checks). Hand the
discharged obligations to `certificate::build_certificate` and receive a
content-addressed, Ed25519-signable certificate.

## Mark a discretion point

When a rule reaches a point where mechanical inference is not sound and
a human authority must decide — "fit and proper person", "good cause"
for an extension, "adequate systems and controls" — Lex marks that
point with a typed hole:

```rust
Term::Hole(Hole {
    name: Some(Ident::new("fit_and_proper_director")),
    ty: Box::new(Term::constant("ComplianceVerdict")),
    authority: AuthorityRef::Named(QualIdent::new(
        ["authority", "fsa", "seychelles"].iter().copied(),
    )),
    scope: Some(ScopeConstraint {
        fields: vec![
            ScopeField::Jurisdiction(QualIdent::simple("SC")),
            ScopeField::TimeWindow { from, to },
        ],
    }),
})
```

The hole has a type (`ComplianceVerdict`), an authority entitled to fill
it, and an optional scope. It appears explicitly in every proof. The
obligation extractor produces DomainMembership and TemporalOrdering
obligations directly from the hole's scope. The hole is filled only by a
`HoleFill` whose signer matches the hole's authority.

## Next reads

- `README.md` — the public entry point, with the design-property summary.
- `docs/language-spec.md` — introductory reference for the core calculus.
- `docs/frontier-work/08-lex-core-calculus.md` — in-progress calculus
  extensions.
- `formal/coq/LexCore.v` and `formal/lean/LexCore.lean` — mechanized
  soundness proofs.
- The canonical paper at research.momentum.inc.

## Troubleshooting

`cargo test --workspace` fails with a `mez-core` path error: the
workspace `Cargo.toml` declares `mez-core` at `../kernel/mez/crates/mez-core`.
If the kernel repo is at a different location, set `CARGO_NET_GIT_FETCH_WITH_CLI=true`
and add a `[patch.crates-io]` table to the workspace `Cargo.toml` pointing
`mez-core` to the correct path.

`cargo run -p lex-cli` without a subcommand prints the orientation text
and the `cargo run --example hello-lex` line. Any subcommand
(`lex check`, `lex parse`, `lex sign`, …) runs the corresponding stage
of the toolchain; `--help` after any subcommand lists its flags.
