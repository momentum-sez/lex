# Frontier Work 08 — Lex Core Calculus

Status: frontier design note
Scope: typed frontier model for the nine PLATONIC-IDEAL §5.1 commitments
Audience: kernel engineers, formal-methods reviewers, and Lex paper authors

Canonical public reference: `docs/language-reference.md`

This note is not the canonical public language reference. It documents the
frontier `core_calculus` model. The executable admissible checker in
`crates/lex-core/src/typecheck.rs` still rejects surface `Term::Hole` and
`Term::HoleFill`, and `compose::evaluate_all_fibers` is still a stub. The
public claim set for those boundaries lives in `docs/language-reference.md`.

## 0. Motivation

The kernel exists to make multi-harbored entities possible. The logic that
tells an AI agent whether a transition is admissible — and where it must stop
and ask a human — is **Lex**. PLATONIC-IDEAL §5.1 specifies nine design
commitments that Lex must discharge before it is honest to call the kernel
"proof-producing." Until this frontier, Lex-core's surface was a rich term
language (AST, parser, elaborator, typechecker, obligations) but the nine
commitments were data records not type-system constraints. This frontier
lifts them to the type system.

The headline primitive inside the frontier core calculus is the **typed
discretion hole** `Hole<T, A>`. Every other commitment exists to make the
discretion hole tractable — levels so
that meta-holes can be distinguished from object holes, temporal stratification
so that "fit and proper person as of 2026-01-01" is a different hole from
"fit and proper person as of 2026-04-15", tribunal modality so that an ADGM
hole is not accidentally filled by an HKMA adjudicator, witness-supply oracles
so that the unbounded existentials inside the hole reduce to a bounded
mechanical part plus a declared residual, and a derivation certificate so that
downstream consumers can distinguish mechanical derivation from discretion.

## 1. Commitment map

| # | Commitment                             | Module                        |
|---|----------------------------------------|-------------------------------|
| 1 | Level-polymorphic rules                | `core_calculus::level`        |
| 2 | 4-tuple monotonicity                   | `core_calculus::monotone`     |
| 3 | Temporal stratification                | `core_calculus::temporal`     |
| 4 | Typed discretion holes                 | `core_calculus::hole`         |
| 5 | Proof summary layer                    | `core_calculus::summary`      |
| 6 | Principle balancing                    | `core_calculus::principle`   |
| 7 | Open-world closure with oracle         | `core_calculus::oracle`       |
| 8 | Derivation certificate                 | `core_calculus::cert`         |
| 9 | Formal scaffold (Coq/Lean)             | `formal/coq`, `formal/lean`   |

Pre-existing Lex modules (`ast.rs`, `typecheck.rs`, `obligations.rs`, etc.)
remain the runtime authority for the full surface language. The frontier
`core_calculus` module exposes the *nine commitments* as a narrow, strongly-typed
API that downstream consumers — kernel crates, proof assistants, agents —
can use without descending into the surface AST. It is still opt-in rather than
the production execution path.

## 2. Type-system encodings

### 2.1 Level-polymorphic schema (commitment 1)

`Rule<const LEVEL: u64>` is a phantom-typed newtype over the underlying
`ast::Term`. Meta-rules are `Rule<1>`, object rules are `Rule<0>`,
constitutional rules are `Rule<2>`, and so on. The invariant

```
meta-rule at level ℓ may only quantify over rules at levels strictly < ℓ
```

is enforced by the constructor `MetaRule::<L>::quantify_over::<B>(body)`
which has a `where` clause `B: Lt<L>` — `Lt<L>` is a sealed trait
implemented for exactly the levels `0..L`. Self-application produces a
compile-time error of the form

```
error[E0277]: the trait `Lt<2>` is not implemented for `Rule<2>`
```

Girard-style paradoxes collapse into Rust's type-checker rejection.

### 2.2 Curry-Howard monotonicity in 4-tuple (commitment 2)

Every `Proof<T, J, V, Tr>` carries the 4-tuple `(Time, Jurisdiction, Version,
Tribunal)` as phantom types. Composition is only well-typed at a fixed
4-tuple:

```rust
impl<T, J, V, Tr> Proof<T, J, V, Tr> {
    pub fn compose<U>(self, other: Proof<T, J, V, Tr, U>) -> Proof<T, J, V, Tr, (Self::Ty, U)>;
}
```

Cross-tribunal composition requires a `TribunalCoercion<From, To>` witness
returning `Option<Proof<..., To>>`. `None` is the honest answer when canons
diverge — we refuse to fabricate a proof that no tribunal would recognize.

### 2.3 Temporal stratification (commitment 3)

`Asof<const STRATUM: u8>` wraps a time literal. `Asof<0>` is frozen at
commit and is `const`-like — the inner value is behind a private field
accessible only via `into_frozen()` which returns the raw `TimeLiteral` but
produces a `FrozenToken` witness the caller must consume to mutate. `Asof<1>`
is derived via tolling or savings rewrites and carries a `RewriteWitness`.
Lift is `Asof<0> -> Asof<1>` total; demotion is impossible by construction.

### 2.4 Typed discretion holes (commitment 4) — HEADLINE

```rust
pub struct Hole<T, A: Authority> {
    name: Option<Ident>,
    ty: PhantomData<T>,
    authority: A,
    scope: Option<ScopeConstraint>,
    context: HoleContext,
}
```

Elaboration preserves holes through type-checking: the term `Hole<FitAndProper,
ADGMFSRA>` type-checks as if it inhabited `FitAndProper`, but the verifier
carries the hole forward. The filled form is `HoleFill<T, A>` which requires
a PCAuth witness from an authority satisfying `A`. Verification returns

```rust
pub struct DerivationCertificate {
    pub mechanical_check: bool,        // false if any unfilled hole remains
    pub discretion_steps: Vec<DiscretionStep>,
    pub discretion_frontier: BTreeSet<HoleId>,  // unfilled holes
    pub four_tuple: FourTuple,
    pub summary_digest: Blake3Digest,
}
```

`mechanical_check = true` iff the discretion frontier is empty AND every
`HoleFill` carries a valid PCAuth. The verifier **never** silently fills
holes. A hole is blocked until a signed filler arrives, and the certificate
records the filler's identity, the stratum-0 time at which it was supplied,
and the content-addressed digest of the filled term.

Three worked examples below (§4).

### 2.5 Proof summary (commitment 5)

`ProofSummary` is derived by verified compilation from a `DerivationCertificate`
and preserves three invariants (`summary_preservation` tests):

1. **Obligation preservation** — every obligation in the proof appears in the
   summary's obligation set (possibly aggregated but never elided).
2. **Verdict preservation** — the summary-level verdict equals the proof-level
   verdict.
3. **Discretion preservation** — every unfilled hole in the proof appears
   in the summary's discretion frontier (names and authorities preserved,
   bodies may be abstracted).

The reference implementation is pure and total; the compilation is mechanical,
so we can assert `summary(proof).obligations ⊇ proof.obligations` as a
property-based test.

### 2.6 Principle balancing (commitment 6)

`PrincipleBalancing` is a first-class term that cites precedents and carries
a verdict. The acyclicity check runs on `PrincipleId × CaseCategory` at
fiber-compile time. Collisions produce a structured `PrincipleDeadlock`
error with the cycle echoed in the diagnostic. We use Tarjan's SCC algorithm
on the product graph; the implementation runs in `O(|V| + |E|)` per fiber.

### 2.7 Witness-supply oracle (commitment 7)

```rust
pub trait WitnessSupplyOracle {
    type Query;
    type Witness;
    fn supply_bounded_horizon(
        &self,
        query: Self::Query,
        horizon: Horizon,
    ) -> OracleResponse<Self::Witness>;
}

pub struct OracleResponse<W> {
    pub witnesses: Vec<W>,
    pub exclusion_commitment: Blake3Digest,  // commits to the excluded set
    pub horizon_reached: Horizon,
    pub beyond_horizon: Option<DiscretionHoleId>,
}
```

Bounded-depth traversal + discretionary hole fallback: if the query's natural
depth exceeds the horizon, the oracle returns witnesses up to the horizon and
a discretion-hole handle for the residual. The exclusion commitment is a
Merkle digest of the set of elements the oracle searched and rejected — a
downstream verifier can check that no claimed-excluded element was later
supplied as a witness.

### 2.8 Derivation certificate (commitment 8)

Already sketched above. The certificate is content-addressed (Blake3) and
serializable via the existing `LexCertificate` route in `certificate.rs`.
`DerivationCertificate::into_lex_certificate(self)` converts to the legacy
record; `LexCertificate::to_derivation_certificate(&self)` is the inverse.

### 2.9 Formal scaffold (commitment 9)

`formal/coq/LexCore.v` declares the core calculus judgments in Coq and
states the decidability lemma for the admissible fragment with the forward
direction proved. `formal/lean/LexCore.lean` mirrors the same statements in
Lean 4. Open obligations are enumerated in §5 below.

## 3. Discretion hole semantics (detail)

The hole is a first-class term that type-checks as if it inhabited its
declared type. Its operational semantics:

- **At elaboration:** the hole is elaborated against the expected type. The
  expected type must match the hole's declared type exactly. Scope
  constraints propagate into the surrounding context.
- **At type-checking:** the hole is treated as a variable of its declared
  type. It is preserved; no unification fill occurs.
- **At evaluation:** the hole blocks reduction. If reduction requires the
  hole's value, evaluation pauses and the evaluator emits a request of
  type `(HoleId, T, Authority, ScopeConstraint)`.
- **At verification:** the verifier checks every filled hole against its
  PCAuth witness. Unfilled holes appear in the discretion frontier. The
  `mechanical_check` bit is true iff no holes remain.
- **At proof summary:** unfilled holes are preserved by name and authority.
  Downstream readers can inspect the discretion frontier without access to
  the proof body.

## 4. Three worked examples

### 4.1 "Fit and proper person" (ADGM FSRA)

```lex
def license_grant(app : Application) : Decision :=
  if has_capital_adequacy(app) ∧ has_risk_framework(app) then
    let fit_and_proper : FitAndProperJudgment @ ADGMFSRA :=
      ?fit_check : FitAndProperJudgment @ ADGMFSRA
                 scope { jurisdiction: ADGM; entity_class: Principal };
    verdict_from(fit_and_proper, app)
  else
    Denied
```

The hole `?fit_check` has type `FitAndProperJudgment` and is authorized
only by the ADGM FSRA. An AI agent evaluating `license_grant` computes
`has_capital_adequacy` and `has_risk_framework` mechanically, then halts at
`?fit_check` and emits a structured request. The FSRA officer files a
judgment (via PCAuth-signed `fill`), and the certificate records the officer's
identity, the stratum-0 time, and the digest of the filled term.

### 4.2 "Material adverse change" (loan covenant)

```lex
def covenant_breach(loan : Loan, asof : Asof<0>) : Prop :=
  ?mac_event : MaterialAdverseChange @ CreditAgreementAdjudicator
             scope { time_window: asof - 90_days .. asof;
                     entity_class: Borrower }
  ∨ hard_financial_covenant_breach(loan, asof)
```

The MAC hole is scoped to a 90-day window ending at `asof`. Only the
contractually-named adjudicator (e.g., an independent credit committee) may
fill it. Any AI agent evaluating the covenant either finds a hard covenant
breach (mechanical) or routes the MAC question to the adjudicator.

### 4.3 "Adequate systems and controls" (Basel III operational risk)

```lex
def operational_capital_adequacy(bank : Bank, asof : Asof<0>) : CapitalBuffer :=
  let baseline : CapitalBuffer := basic_indicator_approach(bank, asof) in
  let overlay : CapitalBuffer :=
    ?sys_controls : SystemsAndControlsAdjustment @ NationalRegulator
                 scope { time_window: asof - 365_days .. asof;
                         entity_class: DepositoryInstitution } in
  combine_buffers(baseline, overlay)
```

The `?sys_controls` hole is filled by the national regulator after on-site
inspection. Until filled, the operational capital adequacy is carried as a
partial proof. The certificate's discretion frontier prevents the buffer
from being treated as final.

## 5. Remaining proof obligations

### Mechanically stated in Coq/Lean, not yet proven:

1. **Level-strict subject reduction** — reduction at level ℓ preserves typing
   at level ≤ ℓ. (Straightforward; no impredicativity.)
2. **Discretion-hole soundness** — if a proof type-checks with holes
   `H₁, …, Hₙ` and each is filled by a PCAuth-valid filler of the declared
   type, the resulting closed proof is sound in the underlying type theory.
   (Requires a closing-substitution lemma; ≈ 1 week of Lean.)
3. **Temporal coherence** — any reduction sequence preserves the stratum-0
   `asof` of the original transition. (Direct by case analysis on the
   reduction rules.)
4. **Tribunal-coercion partiality** — the `TribunalCoercion<From, To>`
   trait admits `None` for canonical disagreements. (Honest statement —
   there is no totality theorem here; this is an honesty statement, not a
   theorem.)
5. **Summary-obligation preservation** — `summary(proof).obligations ⊇
   proof.obligations` as a semantic containment. Property-based in Rust;
   formal proof requires ≈ 2 weeks of Lean.
6. **Principle-balancing termination** — acyclic DAG check on the product
   graph terminates in `O(|V| + |E|)`. Classic Tarjan; a full proof is a
   textbook exercise.
7. **Witness-supply oracle boundedness** — every oracle returns in finite
   time given a finite horizon. (Axiomatic — the oracle is assumed to
   respect its declared horizon; we cannot prove this in the logic.)
8. **Certificate content-addressing** — `derive(p₁) = derive(p₂) ⇒ p₁ ≡ p₂`
   up to α-equivalence. (Direct from Blake3 preimage resistance as an
   assumed cryptographic property.)
9. **Admissible-fragment decidability** — the admissible fragment (no
   unbounded quantification, no unfilled holes, no unresolved principle
   collisions) has decidable type-checking in polynomial time. Forward
   direction: constructive type-checker in Rust witnesses termination.
   Reverse direction (completeness): requires normalization-by-evaluation.

### Scaffolded but not stated:

10. Meta-refinement-as-spans (links to §5.7 refinement work — separate frontier).

## 6. What this does NOT do

- The full Lex decidability theorem is NOT proved. Scaffold only.
- The Coq/Lean scaffolds contain `admit` and `sorry` where proofs are
  outstanding. Every `admit`/`sorry` is annotated with the expected proof
  strategy.
- The surface Lex parser and elaborator are NOT replaced — the frontier
  module is a strongly-typed *narrow waist* sitting between them and the
  proof kernel. Existing tests continue to pass.
- The bridge to `mez-lex` in the kernel is an **adapter** — it does not
  rewrite the kernel's parallel Lex implementation. Wire compatibility is
  preserved via `LexCertificate` serialization.

## 7. Files delivered

```
~/lex/crates/lex-core/src/core_calculus/
├── mod.rs
├── level.rs           — Rule<const LEVEL: u64>, Lt<L>, MetaRule
├── monotone.rs        — FourTuple, Proof, TribunalCoercion
├── temporal.rs        — Asof<const STRATUM: u8>, FrozenToken, lift0, derive1
├── hole.rs            — Hole<T, A>, HoleFill, Authority, ScopeConstraint
├── cert.rs            — DerivationCertificate, DiscretionStep
├── summary.rs         — ProofSummary, compile_summary
├── principle.rs       — PrincipleBalancing, acyclic_check, PrincipleDeadlock
├── oracle.rs          — WitnessSupplyOracle trait, OracleResponse, Horizon
└── tests.rs           — 40+ integration tests
~/lex/formal/coq/LexCore.v      — Coq scaffold
~/lex/formal/lean/LexCore.lean  — Lean 4 scaffold
~/lex/docs/frontier-work/08-lex-core-calculus.md  — this file
~/lex/REMAINING-WORK.md         — ledger
~/kernel/mez/crates/mez-lex/src/core_calculus_bridge.rs  — wire adapter
```

## 8. Acknowledgements

The Lex logic commitments are authored by Raeez Lorgat. This frontier
delivers the first-cut mechanization. Any formal-methods errors are the
implementer's; any lacunae in the design predate this frontier and should
be fed back to the Lex paper draft at `research.momentum.inc`.
