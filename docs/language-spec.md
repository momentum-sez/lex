# Lex Language Spec

Lex is a dependently-typed logic for encoding administrative and regulatory
compliance rules. A Lex rule is a program: it has a type, it accepts
structured inputs, it produces a verdict, and the verdict carries a
machine-checkable proof that every intermediate obligation was discharged
by a named decision procedure.

This file is an explanatory overview. The executable boundary is canonical in
`docs/language-reference.md`.

Four primitives make Lex distinct. **Defeasibility**: rules override other
rules by explicit numeric priority on a DAG; *lex specialis* and *lex
posterior* are first-class operators rather than control flow.
**Temporal stratification**: stratum 0 is frozen historical fact, stratum 1
is derived legal state, and the coercion from 0 to 1 is total while the
reverse is not expressible. **Authority-relative interpretation**: the same
rule text can produce different verdicts under different tribunals, and
crossing between tribunals requires an explicit bridge witness.
**Typed discretion holes**: a hole `? : T @ Authority` marks the precise
point where machine derivation halts and human judgment begins. In the current
repository this is a full-calculus/frontier construct: the parser and
elaborator preserve it, the main checker rejects it, and the frontier
`core_calculus` module models the typed hole and fill records.

A Lex program is a closed term in the core calculus. The typing judgment
is `Γ ⊢ e : T ! E`, where `Γ` is the context, `T` is the result type, and
`E` is the effect row. Effects track `read`, `write(scope)`,
`attest(authority)`, `oracle(ref)`, `discretion(authority)`, `fuel(level,
amount)`, and the distinguished `sanctions_query` - a privileged effect
whose presence cannot be overridden by any tribunal or exception.

A small but complete rule, the Seychelles International Business Companies
Act 2016 section 66 minimum-directors requirement:

```text
defeasible min_directors : IncorporationContext -> ComplianceVerdict :=
  lambda (ctx : IncorporationContext).
    match director_count(ctx) return ComplianceVerdict with
    | Zero => NonCompliant
    | _    => Compliant
  priority 0
end
```

The same program constructed as a Rust AST appears in
`crates/lex-core/examples/hello-lex.rs`. The example runs the full
pipeline - De Bruijn indexing, temporal stratification, type checking,
obligation extraction, decision-procedure discharge, certificate assembly
- and prints the intermediate result of each stage.

Three design properties structure the calculus beyond the four primitives.
**Fuel-typed fibers**: every evaluation carries a finite budget, and the
meta-result `Indeterminate` (fuel exhausted) is a proper typed evaluation
status rather than a timeout exception; it is outside the paper's
five-element `ComplianceVerdict` lattice and must be re-queried at a higher
horizon before a compliance verdict is certified. **Principle conflict calculus**:
principles balance on an acyclic priority DAG indexed by
`(PrincipleId, CaseCategory)`; cycles are detected at load time.
**Admissible fragment**: a syntactic restriction of the full calculus whose
executable checker is implemented in Rust; recursion, sigma types, unfilled
holes, hole fills, modal forms, temporal coercions, principle balancing, and
unresolved content references are rejected by `typecheck::check_admissibility`
or the bidirectional checker.

## Grammar

The core grammar is defined in `crates/lex-core/src/ast.rs`. The public
types are `Term`, `Sort`, `Level`, `Effect`, `EffectRow`, `AuthorityRef`,
`TribunalRef`, `OracleRef`, `PrincipleRef`, `PrecedentRef`, `Pattern`,
`Branch`, `Hole`, `DefeasibleRule`, `Exception`, `ScopeConstraint`,
`ScopeField`, `TimeTerm`, and `TimeLiteral`.

A `Term` is one of: `Var { name, index }`, a universe sort, a constant
reference, a lambda, a Π-type, a Σ-type (non-admissible), an application,
a `let`-binding, a `rec`-definition (non-admissible), a match expression,
a literal, an annotation, a defeasible rule, a typed hole, a hole fill,
an evaluation of a principle-balancing step, or a temporal-lift
expression. Every binder carries an explicit domain annotation; there are
no implicit arguments in core form.

## Pipeline

A Lex rule flows through six stages before it produces a certificate:

1. **Parse.** The parser (`crates/lex-core/src/parser.rs`) accepts the
   surface syntax and produces a surface AST.
2. **Elaborate.** The elaborator (`crates/lex-core/src/elaborate.rs`)
   rewrites the surface AST into the core calculus, assigning explicit
   domain annotations to every binder and producing an elaboration
   certificate (`elaboration_cert.rs`) that records the rewrite witnesses.
3. **Index.** `debruijn::assign_indices` replaces named variables with
   De Bruijn indices. Variable references are resolved relative to their
   binders; free variables are errors.
4. **Temporal check.** `temporal::check_temporal_stratification` rejects
   terms that apply `lift_0` to a stratum-1 argument or otherwise violate
   the stratum-0 / stratum-1 directionality.
5. **Type-check.** `typecheck::infer` and `typecheck::check` implement
   bidirectional type checking against a `Context`. The compliance prelude
   (`prelude::compliance_prelude`) supplies the global signature of
   types, constructors, and accessors used in practical rule suites.
   `typecheck::check_admissibility` syntactically restricts a term to the
   decidable fragment.
6. **Extract obligations, discharge, certify.** `obligations::extract_obligations`
   walks the typed term and emits `ProofObligation` records for every
   structurally significant node. Each obligation is discharged by a
   decision procedure in `decide` (finite-domain enumeration,
   Presburger-arithmetic thresholds, boolean checks, SMT, temporal
   tableau). The discharged obligations are handed to
   `certificate::build_certificate`, which produces a content-addressed,
   Ed25519-signable `LexCertificate`.

## Admissible fragment

The admissible fragment is a syntactic restriction designed so that
termination and decidability hold without running an SMT solver on every
term. A term is admissible if it contains no `Rec`, no `Sigma`, no
unfilled `Hole`, and every `Match` scrutinee has an inductive type whose
constructor set is known at admissibility-check time. The compliance
prelude types (`ComplianceVerdict`, `Bool`, `Nat`, `SanctionsResult`,
`ComplianceTag`) all satisfy the latter condition, which is why the
practical rule suites fall inside the admissible fragment.

The scaffold-level `is_admissible` Boolean is proved decidable in
`formal/coq/LexCore.v` and `formal/lean/LexCore.lean`. This is not the
paper-level admissible-fragment theorem. The full paper-level decidability
claim still depends on the full-calculus metatheory for conversion,
confluence, preservation, and match exhaustiveness. The administrative WHNF
kernel `administrative_whnf_bounded_reduction` is Qed-closed in
`formal/coq/Lex/PaperMechanization.v`. The same file also closes
`administrative_whnf_sufficient_fuel` and
`administrative_whnf_canonical_bound_reduction`, which expose the reusable
fuel-bound form: any fuel at least `whnf_head_steps(t)`, including the
canonical `term_size(t) + let_depth(t)` bound, reaches a WHNF value for the
typed administrative weak-head fragment. See `formal/README.md` for the exact
frontier.

## Effects and the privilege-creep prevention rule

An effect row is either `Empty`, a list of individual `Effect` labels, a
row variable, a path-indexed join `row₁ ⊕ row₂`, or a branch-sensitive
wrapper. Path indexing is the mechanism that prevents privilege creep
under composition: a fiber that reads `consent.level` cannot accidentally
gain write access to `treasury.balance` by being composed with a fiber
that touches treasury state. The effect rows at the composition site are
joined pointwise; a subsumption mismatch is a type error.

The `sanctions_query` effect is distinguished. A rule that carries
`sanctions_query` in its effect row produces a verdict that cannot be
overridden by any tribunal coercion, defeasibility exception, or mutual
recognition agreement. This reflects legal reality: sanctions regimes
operate outside the normal hierarchy and admit no exception.

## Typed discretion hole

A hole has three named fields:

- **Type.** The value type the filler must supply.
- **Authority.** The principal entitled to fill the hole. An
  `AuthorityRef` is either a named identifier
  (`authority.fsa.seychelles`) or a content-addressed reference.
- **Scope.** An optional `ScopeConstraint` restricting the fill to a
  jurisdiction, entity class, time window, or corridor.

A hole fill is a full-calculus/frontier object. The shipped checker rejects
`HoleFill`. The Rust frontier API records a PCAuth-shaped witness and performs
a structural signer-key precheck; full cryptographic verification, revocation
checking, delegation-chain checking, and checker-visible effect discharge are
not wired into the executable admissible checker.

## Certificate

A `LexCertificate` contains the rule's content-addressed digest, the
jurisdiction, the legal basis, the verdict, the list of discharged
proof obligations (each naming its decision procedure), a content-address
of the certificate itself, and an ISO-8601 issuance timestamp. The
certificate is `CanonicalBytes`-serializable and Ed25519-signable.

## Runtime caveat fragment

`lex-core::predicate_runtime` is the executable first-order caveat primitive.
It decides closed propositions over request attributes: equality, ordering over
numbers and timestamps, set membership, boolean composition, and context-set
membership. `LexCaveat` adds a semantic kind tag so attenuation can use direct
monotone rules where the kind has a canonical order.

`lex-core::predicate_narrowing::caveats_narrow(parent, child)` checks that a
child capability narrows its parent. The positive result means `child` implies
`parent` for every request context in the supported fragment. Failure is
explicit: missing caveat kind, non-narrowing structural comparison,
propositional counterexample, or undecidable fallback.

## Relation to Op

Lex is the rule and proof layer. Op (`github.com/momentum-sez/op`) is the
operational effect language that performs the state transitions Lex admits.
Lex decides whether a transition is permitted; Op executes the transition
and emits calls against its execution host. The two languages share effect rows
and the proof-summary layer.

This repository does not currently ship a production Lex-owned `compile_to_op`
entry point. The public companion Op repository carries the executable
Lex-to-Op compiler surface and finite Coq verdict-agreement scaffolds for its
admissible skeleton. Lex's public obligation is to state the source-side
contract precisely enough that such a compiler can be accepted or rejected
without reinterpreting Lex semantics.

The intended Lex-to-Op admission envelope must bind, at minimum:

- the elaborated Lex source digest and rule-pack digest;
- the Lex certificate or proof-summary digest, including open obligations;
- the compiled Op payload digest;
- the input context digest and typed payload schema digest;
- the four-tuple authority for the rule decision;
- the compiler version digest and Op primitive-registry digest;
- the effect row and subject-indexed capability row, including freshness
  requirements;
- the gas schedule and any cardinality / bounded-search certificate digest;
- the PCAuth entries for filled discretion holes, each bound to the exact hole,
  value, scope, pack digest, context digest, and payload digest;
- the lists of failed, deferred, or host-required predicates.

Admission is fail-closed: any digest mismatch, untyped payload, unbound
primitive, non-empty failed predicate list, unverifiable receipt, missing
capability, stale authority, unaccepted hole fill, or exhausted bounded-search
certificate prevents the Op payload from being treated as Lex-authorized.

The compiler domain is narrower than the surface language. The current target
domain is the executable admissible core plus only those frontier constructs
with an explicit lowering and certificate rule. `Rec`, `Sigma`, unresolved
content references, and unchecked certificate discharge remain outside the
admitted compiler domain. Modal forms, temporal coercions, open holes, and
unchecked hole fills may enter the public `HoleExtension` admission mode only
with explicit residuals. Filled holes become fully discharged only after the
checker can verify the PCAuth payload and record the effect/capability
discharge in the certificate.

The adequate compiler theorem should state: if a Lex term is in the admitted
domain, the compiler emits a type-checked Op payload, and the admission
envelope is exact, then Op execution preserves the Lex verdict, does not
expand the Lex effect or capability rows, preserves extracted obligations, and
is replay-protected by the bound digests. The reverse direction, full
abstraction over arbitrary Op contexts, and paper-level adequacy for the full
calculus remain open obligations.

## See also

- `README.md` - public entry point with design-property summary.
- `docs/getting-started.md` - 5-minute cold-clone walk-through.
- `crates/lex-core/examples/hello-lex.rs` - end-to-end runnable example.
- `formal/coq/LexCore.v`, `formal/lean/LexCore.lean` - mechanized proofs.
- `docs/frontier-work/08-lex-core-calculus.md` - in-progress calculus extensions.
