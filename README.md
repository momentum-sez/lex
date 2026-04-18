# Lex

Lex is a dependently-typed, effect-typed programming language for
jurisdictional compliance rules. The calculus has defeasible rules with typed
priority, two temporal sorts that syntactically separate frozen historical
time from derived legal time, tribunal modalities that index propositions by
the authority asserting them, and typed discretion holes that mark the
boundary at which machine derivation halts and a named authority must decide.
An admissible fragment of the calculus is identified in which type-checking
reduces to bounded weak-head reduction, and compilation produces a proof term
that separates mechanical derivation from discretionary inputs.

## What is new

Four features appear here as primitives of a single calculus; no prior
compliance language carries all four. Catala (Merigoux, Chataing, Protzenko,
*ICFP 2021*) has first-class defeasibility in a default calculus, but its
types are ML-family without dependence, it does not model multiple
interpreting authorities, and it offers no language-level construct for the
machine-vs-judgment boundary — when the law requires judgment, the Catala
author supplies a value and the distinction vanishes at compile time. Rego
and Datalog evaluate rules as logic programs over flat relations, without
dependent types, without a temporal sort distinction, and without a typed
interface across the discretion boundary. LegalRuleML (OASIS, 2013) is an
interchange schema with no execution semantics. Isabelle/HOL and Coq encode
rules in a general higher-order logic and push the encoding burden to the
user, one priority DAG and one temporal stratification at a time. Lex makes
all four primitive: **(1)** defeasible rules with a typing rule requiring
type agreement between base and exceptions — an invariant that untyped
defeasible logic programs in the Governatori–Prakken–Sartor tradition do not
enforce; **(2)** temporal sorts `Time_0` (frozen) and `Time_1` (derived) with
a directional coercion `lift_0 : Time_0 → Time_1` and no inverse, enforced
syntactically so that retroactive amendment touches derived consequence
without contaminating historical fact; **(3)** tribunal modals `[T] A` with
explicit `CanonBridge` witnesses, so divergent authority interpretations
surface as type obstructions rather than silent selection, and no aggregation
operator exists over tribunals; **(4)** typed discretion holes
`? h : T @ authority scope S`, which propagate a `discretion(authority)`
effect that is discharged only by a `fill(h, e, witness)` carrying a PCAuth
proof-carrying authorization. The published treatment of the core calculus,
the admissible fragment, the termination argument, and the position against
each of these prior systems is in the paper *Lex: A Logic for Jurisdictional
Rules* (research.momentum.inc).

## Why it matters

Compliance rules are already programs, executed today in Python, Java, SQL,
and Solidity. Those substrates collapse three distinctions the law holds open.
They conflate rule priority with control flow, so *lex specialis* and *lex
posterior* are indistinguishable from the order of `if` branches. They treat
time uniformly through mutable state, so the incorporation date of an entity
and the tolled filing deadline that derives from it share the same sort. They
have no language-level representation of the authority asserting a verdict,
so a program that consults an ADGM FSRA rule and a Seychelles FSA rule
produces a verdict with no traceable provenance. Above all, they have no
typed construct for the boundary between what the machine computed and what
a human approximated — "fit and proper person," "material adverse change,"
"good cause" become hard-coded booleans or inline heuristics, invisible to
every downstream consumer. An AI agent acting under these substrates either
oversteps into judgments no statute authorizes or understeps away from
mechanical evaluation that would have sufficed. Lex provides the
type-theoretic interface. The machine reduces the rule as far as the calculus
permits and halts at a typed hole that specifies the type of judgment
required, the authority that may supply it, and the scope in which the
judgment applies. The filled term enters the derivation trace with a
cryptographic authorization witness, and downstream auditors receive a proof
term that exposes the mechanical fragment and the discretionary fragment as
independently inspectable.

## Quickstart

Clone and run the end-to-end example in three commands:

```bash
git clone https://github.com/momentum-sez/lex.git
cd lex
cargo run --example hello-lex -p lex-core
```

The example walks the Seychelles International Business Companies Act 2016 s.66 — first-shareholder-meeting requirement — through the full Lex pipeline: AST construction, De Bruijn indexing, temporal stratification, type inference, proof-obligation extraction and discharge, certificate issuance. It then constructs a typed discretion hole for `fit_and_proper : Prop @ regulator` and extracts its scope obligations, demonstrating the judgment-boundary primitive that makes Lex distinct from other rule engines.

Further reading: [`docs/getting-started.md`](docs/getting-started.md) for a five-minute cold-reader walk; [`docs/language-spec.md`](docs/language-spec.md) for the language reference; the paper *Lex: A Logic for Jurisdictional Rules* (research.momentum.inc) for formal treatment.

## Instant run

```
$ cargo test -p lex-core --test discretion_hole_contract

running 2 tests
test surface_fill_example_is_preserved_then_rejected_by_main_checker ... ok
test surface_hole_example_is_preserved_then_rejected_by_main_checker ... ok

test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured
```

These are the repository's contract tests for the discretion-hole frontier.
Each loads a surface example, runs `lexer::lex`, `parser::parse`, and
`elaborate::elaborate`, and asserts that `Term::Hole` (or `Term::HoleFill`)
is preserved through every pre-checker stage as a typed object. Each then
calls `typecheck::infer` and asserts that the admissible checker rejects the
term with precisely the diagnostic `AdmissibilityViolation::UnfilledHole` (or
`HoleFillNotSupported`). The discretion hole crosses the surface pipeline as
a first-class typed term; the admissible fragment declines to discharge it
because sound discharge requires a PCAuth witness the frontier core calculus
supplies and the admissible checker does not yet consume. This is the exact
research boundary described in the paper.

The surface input `examples/discretion-hole-frontier.lex` is a single line:

```lex
? fit_and_proper : Prop @ regulator scope { jurisdiction : ADGM }
```

## Design properties

- **Defeasibility.** Rules override other rules by explicit numeric priority.
  The typing rule requires every exception body to inhabit the same type as
  the base body. Conflict resolution is a bounded search over the priority
  DAG, not a control-flow cut.
- **Temporal stratification.** `Time_0` and `Time_1` are distinct sorts at
  universe level 0. `lift_0 : Time_0 → Time_1` is the only coercion; no term
  demotes `Time_1` to `Time_0`. Retroactive rule change regenerates
  `Time_1`-indexed consequences from the unchanged `Time_0` record.
- **Authority-relative interpretation.** Propositions are indexed by tribunal
  through `[T] A`. Cross-tribunal coercion requires an explicit
  `CanonBridge(T1, T2, A)` witness; no implicit aggregation operates over
  tribunals.
- **Typed discretion holes.** `?h : T @ auth scope S` produces the
  `discretion(auth)` effect. `fill(h, e, w)` discharges the effect only if
  `w : PCAuth(auth, h)` — a dependent record carrying signer DID, role
  credential, scope witness, Time_0 timestamp, and an Ed25519 signature over
  the triple `(signer, h, value)`.
- **Effect rows.** Effects form a bounded semilattice under union. The
  `sanctions_query` effect is distinguished; the `branch_sensitive` wrapper
  prevents privilege escalation through branch composition.
- **Sanctions dominance.** A proof of sanctions non-compliance inhabits the
  bottom type. No defeasibility exception, tribunal coercion, or discretion
  hole overrides it.
- **Principle conflict calculus.** Principle balancing runs on an acyclic
  DAG indexed by `(PrincipleId, CaseCategory)`; cycles are rejected at load.

## Repository layout

```
lex/
├── crates/
│   ├── lex-core/     parser, elaborator, admissible type checker,
│   │                 obligations, prelude, decision procedures,
│   │                 certificate, frontier core calculus
│   ├── lex-diag/     structured diagnostic ontology
│   └── lex-cli/      command-line authoring shell for air-gapped workflows
├── docs/
│   ├── language-reference.md           canonical public language reference
│   └── frontier-work/
│       └── 08-lex-core-calculus.md     typed-hole frontier design note
├── examples/         surface fibers exercising the frontier boundary
├── formal/
│   ├── coq/          Coq mechanisation
│   └── lean/         Lean 4 mirror
├── Cargo.toml
└── LICENSE
```

## Reading path

| Artifact | Purpose |
| --- | --- |
| `docs/language-reference.md` | Surface grammar, the admissible fragment, small-step reduction, the pipeline, and the precise frontier boundary the main checker enforces |
| `docs/frontier-work/08-lex-core-calculus.md` | Frontier design note: level polymorphism, typed discretion holes, oracle totality, proof summaries, derivation certificates |
| `formal/coq/LexCore.v`, `formal/lean/LexCore.lean` | Mechanised oracle-totality and principle-termination obligations. One certificate-invariant theorem is open pending a formal account of the Rust certificate builder |
| `formal/README.md` | Mechanisation status, admitted lemmas with declared proof strategies |
| `crates/lex-core/tests/` | Integration tests: ADGM rules, Seychelles IBC rules, adversarial attacks (level self-application, cyclic priorities, unauthorised fills), proptest soundness, parse→elaborate→typecheck→obligations→certificate end-to-end |
| Paper | *Lex: A Logic for Jurisdictional Rules* at research.momentum.inc — full core calculus, admissibility argument, typing rules, worked examples, related work, open problems |

## Build

```
cargo check --workspace
cargo test --workspace
cargo clippy --workspace -- -D warnings
```

Rust 1.93 or newer. Self-contained build — no external repository checkouts
required. Foundational types (`CanonicalBytes`, `sha256_digest`,
`ComplianceDomain`) are provided by `crates/mez-core-min`, a standalone
vendor of the subset of Momentum's `mez-core` crate that Lex depends on.

Ecosystem builds that have the full `mez-core` checked out at
`../kernel/mez/crates/mez-core` may opt in with
`cargo check -p lex-core --features kernel-integration`; byte-for-byte
identical canonicalization, digests, and `ComplianceDomain` wire-format are
preserved across both configurations.

## CLI

```
lex check <file.lex>                 type-check a fiber against the admissible fragment
lex parse <file.lex>                 parse and pretty-print the AST
lex elaborate <file.lex>             surface → core elaboration with De Bruijn indices
lex sign <file.lex> --key <key>      Ed25519 sign for air-gapped submission
lex verify <file.lex.signed>         verify a signed fiber
lex check-principles <file>          priority DAG acyclicity check
```

The air-gapped workflow separates authoring from submission: write and
type-check a fiber on an offline machine, `lex sign` with a hardware key,
transfer the signed artifact by physical media, submit to the target kernel.

## Relation to Op

Op (github.com/momentum-sez/op) is the typed effectful workflow language Lex
feeds into. A Lex rule encodes a typed jurisdictional predicate and emits
proof obligations; an Op step references those obligations through `requires`
and `ensures` contracts and discharges them as part of its effect row. Lex
is the rule and proof layer; Op is the workflow layer. The interface is
preconditions, postconditions, and effect discharge; neither language
redefines the other's semantics.

## Contributing

Pull requests and issues welcome. Before opening a pull request, run
`cargo test --workspace` and `cargo clippy --workspace -- -D warnings` and
confirm both pass. New AST forms require parser, elaborator, type-checker,
and admissible-fragment coverage; a change to a type rule updates
`formal/coq/LexCore.v` and `formal/lean/LexCore.lean` in step. The
contribution most valued: rules from a concrete jurisdiction that stress the
admissible fragment. Every rule that fails to admit surfaces a design
question the paper treats as open work.

## Citing

> *Lex: A Logic for Jurisdictional Rules.* Momentum research programme,
> research.momentum.inc.

## License

Apache-2.0. See [LICENSE](LICENSE).
