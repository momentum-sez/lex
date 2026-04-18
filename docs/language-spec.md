# Lex Language Reference

Lex is a dependently-typed logic for encoding administrative and regulatory
compliance rules. A Lex rule is a program: it has a type, it accepts
structured inputs, it produces a verdict, and the verdict carries a
machine-checkable proof that every intermediate obligation was discharged
by a named decision procedure.

Four primitives make Lex distinct. **Defeasibility**: rules override other
rules by explicit numeric priority on a DAG; *lex specialis* and *lex
posterior* are first-class operators rather than control flow.
**Temporal stratification**: stratum 0 is frozen historical fact, stratum 1
is derived legal state, and the coercion from 0 to 1 is total while the
reverse is not expressible. **Authority-relative interpretation**: the same
rule text can produce different verdicts under different tribunals, and
crossing between tribunals requires an explicit bridge witness.
**Typed discretion holes**: a hole `? : T @ Authority` marks the precise
point where machine derivation halts and human judgment begins; the hole
has a type, names the authority entitled to fill it, and appears in every
proof.

A Lex program is a closed term in the core calculus. The typing judgment
is `Γ ⊢ e : T ! E`, where `Γ` is the context, `T` is the result type, and
`E` is the effect row. Effects track `read`, `write(scope)`,
`attest(authority)`, `oracle(ref)`, `discretion(authority)`, `fuel(level,
amount)`, and the distinguished `sanctions_query` — a privileged effect
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
pipeline — De Bruijn indexing, temporal stratification, type checking,
obligation extraction, decision-procedure discharge, certificate assembly
— and prints the intermediate result of each stage.

Three design properties structure the calculus beyond the four primitives.
**Fuel-typed fibers**: every evaluation carries a finite budget, and the
verdict `Indeterminate` (fuel exhausted) is a proper outcome of the
calculus rather than a timeout exception. **Principle conflict calculus**:
principles balance on an acyclic priority DAG indexed by
`(PrincipleId, CaseCategory)`; cycles are detected at load time.
**Admissible fragment**: a syntactic restriction of the full calculus for
which type-checking is decidable; recursion, sigma types, and unfilled
holes are excluded from the admissible fragment and rejected by
`typecheck::check_admissibility`.

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

The admissible-fragment decidability theorem is mechanized in
`formal/coq/LexCore.v` and `formal/lean/LexCore.lean`. The three theorems
still declared as admitted — principle-balancing termination
(Tarjan SCC), certificate well-formedness (WellFormedDC predicate), and
oracle boundedness (axiomatic declared contract) — have their proof
strategies recorded in `formal/README.md`.

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

A hole is filled by a `HoleFill` whose signer is verified against the
hole's authority. The filled term is content-addressed; the content
address appears in the certificate as part of the proof record.

## Certificate

A `LexCertificate` contains the rule's content-addressed digest, the
jurisdiction, the legal basis, the verdict, the list of discharged
proof obligations (each naming its decision procedure), a content-address
of the certificate itself, and an ISO-8601 issuance timestamp. The
certificate is `CanonicalBytes`-serializable and Ed25519-signable.

## Relation to Op

Lex is the rule and proof layer. Op (`github.com/momentum-sez/op`) is the
operational effect language that performs the state transitions Lex admits.
Lex decides whether a transition is permitted; Op executes the transition
and emits syscalls against a kernel. The two languages share effect rows
and the proof-summary layer.

## See also

- `README.md` — public entry point with design-property summary.
- `docs/getting-started.md` — 5-minute cold-clone walk-through.
- `crates/lex-core/examples/hello-lex.rs` — end-to-end runnable example.
- `formal/coq/LexCore.v`, `formal/lean/LexCore.lean` — mechanized proofs.
- `docs/frontier-work/08-lex-core-calculus.md` — in-progress calculus extensions.
