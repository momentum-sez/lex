# Lex - Formal Mechanisations

This directory carries two distinct mechanized artifacts. They address
different obligations at different levels of the language and should not be
conflated.

## Layout

**1. Frontier scaffold (narrow-waist types only).**

- `coq/LexCore.v` - Coq 8.18+ scaffold for Frontier 08
  (`docs/frontier-work/08-lex-core-calculus.md`).
- `lean/LexCore.lean` - Lean 4.14+ mirror.

These files declare the PLATONIC-IDEAL §5.1 commitments as types in the
respective proof assistant. They are scaffolds, not a full calculus
mechanization: admissibility here is the narrow-waist `is_admissible` on the
frontier API, not the full-calculus admissibility predicate of the paper.

**2. Full calculus mechanization (paper-level).**

- `coq/Lex/` - the full Lex core-calculus mechanization referenced by the
  Lex paper. `Lex/PaperMechanization.v` is the per-statement correspondence
  between paper theorems/propositions and their Rocq status.
- `coq/FlatAdmissibleSN.v` - strong normalization for the flat admissible
  fragment.
- `coq/NonAffineSN.v` - reducibility-candidate kernel for the non-affine
  simply typed lambda fragment.

## Status (scaffold; both assistants)

Proved at the scaffold level only:

- **Level non-self-application** - `Rule<L>` cannot appear in the body of
  `MetaRule<L>` (no `Lt L L` inhabitant).
- **Tribunal coercion shape** - `idCoercion` totally returns `Some`; the
  `noBridgeCoercion` totally returns `None` (honest refusal).
- **Temporal lift totality** - `lift_to : Asof 0 → Asof n` is total in the
  abstract scaffold API. The scaffold does not prove a global non-existence
  theorem for all possible Coq functions `Asof (S n) -> Asof n`; it records
  that no demotion operation is exposed by the object-language/Rust frontier
  API.
- **Hole authorisation (scaffold)** - the existence of a `HoleFill` witness
  implies the witness's signer matched the authority. Note: the executable
  admissible checker in `crates/lex-core/src/typecheck.rs` still rejects
  surface `Term::Hole` and `Term::HoleFill`, and `compose::evaluate_all_fibers`
  is a stub; see Frontier 08 §0.
- **Summary preservation** - obligations, verdict, and discretion frontier
  are preserved by `compile_summary`.
- **Principle balancing termination (scaffold)** - the frontier scaffold
  closes the local termination obligation present in this repository.
- **Oracle totality** - the witness-supply oracle theorem follows from the
  class/function definition.
- **Admissible-fragment decidability (scaffold)** - both directions proved
  for the scaffold `is_admissible` function. This is *not* the full-calculus
  admissibility decidability theorem; see next section.

Remaining open at the scaffold level:

1. **Certificate well-formedness** - the mechanical bit's correctness.
   Strategy: introduce a `WellFormedDC` predicate, then model the Rust builder
   in `crates/lex-core/src/core_calculus/cert.rs` and prove it preserves the
   invariant.

## Status (full calculus; paper-level)

Paper-level theorems and propositions are enumerated in the Lex paper's
Mechanization Status appendix (end of §5.1). `coq/Lex/PaperMechanization.v`
carries the direct correspondence for the original abstract targets, while
dedicated files in `coq/Lex/` close the finite-algebra and metatheory results.
The headline status and honest qualifications are:

- **Proof hygiene**: the default `formal/coq` build surface currently contains
  no live `Admitted.`, no live `admit`, and no top-level `Axiom`. Remaining
  frontiers are named `Prop` specifications or explicit scaffold
  `Parameter`s.
- **Temporal non-regression**: `coq/Lex/TemporalStratification.v` closes the
  object-language grade theorem (`temporal_non_regression`) and the no-retract
  path theorem (`no_temporal_retract`) with no global assumptions.
- **Pack re-evaluation soundness**: `coq/Lex/PackReevaluation.v` closes the
  derived-time replay theorem (`re_evaluation_soundness`) and source-history
  preservation (`source_history_reevaluate_derived`) with no global
  assumptions.
- **Effect monotonicity**: `coq/Lex/PaperMechanization.v` closes the
  finite effect-derivation tree theorem (`effect_monotonicity`) with no
  global assumptions: subderivation effects are subsumed by the enclosing
  row.
- **Receipt locality / no-laundering**: `coq/Lex/ReceiptAlgebra.v` closes
  the admission-host receipt theorem (`accepted_compose_iff`,
  `compliant_compose_iff`, `admission_locality`) with no global assumptions.
- **PCAuth quorum extraction**: `coq/Lex/PCAuthQuorum.v` closes the structural
  verifier theorem (`quorum_acceptance_unfolding`) with no global assumptions:
  accepted quorum bundles expose enough distinct valid signer attestations over
  the exact signed payload, including request, pack, and context digests.
- **Lex-to-Op admission envelope**: `coq/Lex/AdmissionEnvelope.v` closes the
  structural fail-closed carrier lemmas for a compiled Op payload: exact
  environment digest matching, receipt acceptance, empty failed/deferred
  predicates, PCAuth verification, and payload-digest equality. This is not
  full Lex-to-Op adequacy or cryptographic unforgeability.
- **Bridge coherence**: `coq/Lex/BridgeSemantics.v` closes the canonical
  strict function-bridge target (`function_bridge_strict_2functor_coherence`)
  with no global assumptions: bridge equality is pointwise equality, horizontal
  composition is ordinary function composition, and modal coercion is a strict
  action. The file also names the proof-relevant provenance layer and the
  partial admission layer so this strict theorem is not confused with raw
  bridge-certificate extraction or failed bridge admission.
- **Security and WHNF support kernels**: `coq/Lex/PaperMechanization.v`
  closes `finite_observation_event_union_bound` for finite event spaces and
  closes `administrative_whnf_bounded_reduction` for the typed administrative
  weak-head fragment by the explicit head-step measure `whnf_head_steps`. It
  also closes `administrative_whnf_sufficient_fuel` and
  `administrative_whnf_canonical_bound_reduction`: any fuel at least
  `whnf_head_steps(t)`, including `term_size(t) + let_depth(t)`, reaches the
  administrative WHNF result. The full cryptographic discretion-hole reduction
  and full admissible-calculus WHNF bound remain stronger obligations.
- **Flat admissible SN**: `coq/FlatAdmissibleSN.v` closes
  `flat_admissible_sn_ext` for the flat admissible fragment with affine
  lambdas and defeasible rules. The supporting theorem
  `step_decreases_size` proves each step strictly decreases size, and
  `nonempty_reduction_chain_strictly_decreases` exposes the reusable
  non-empty-chain form.
- **Non-affine SN kernel**: `coq/NonAffineSN.v` closes
  `non_affine_neutral_expansion_kernel`, the CR3 neutral-expansion lemma for
  the non-affine simply typed lambda calculus. The remaining obligation toward
  `sn_stlc` is the fundamental lemma connecting `Typed` derivations,
  environments, substitution, and `Red`.
- **Admissible-fragment decidability (full calculus)**: decidable type-checking
  for the full admissible fragment still depends on the full-calculus
  metatheory (`conv_eq_shift_compat_spec`, confluence, preservation, and match
  exhaustiveness). The administrative WHNF kernel above is Qed-closed; the full
  calculus claim is stronger and is not discharged unconditionally.
- **Weakening**: `weakening_property` is Qed-closed conditional on a single
  named Prop spec, `conv_eq_shift_compat_spec`. `coq/Lex/Confluence.v`
  now names the exact constructor-fire multi-substitution target
  (`par_subst_args_spec`) and Qed-closes the fold/scoping bridge from the
  stronger unary obligation (`par_subst_at_depth_spec`); the at-depth
  substitution theorem itself remains open.
- **Progress (CONDITIONAL — not delivered type safety)**: `progress` is
  Qed-closed over the full `Term` AST *only conditional on two named, currently
  undischarged Prop premises* (`confluence_property`,
  `match_exhaustiveness_property`). It is NOT an unconditional safety result:
  `confluence_property` is open (see Confluence below) and was provably FALSE
  for the pre-G1 step relation (`ConfluenceCounterexampleArchive.v`'s Qed-closed
  `confluence_property_refuted`); the G1 binder-congruence repair removes that
  specific counterexample but does not prove confluence, so the hypothesis
  remains undischarged. There is no `progress_unconditional` /
  `canonical_forms_pi_unconditional` / `Confluence.confluence_provable`
  artifact — earlier comments in `Typing_progress_skeleton.v` referred to such
  "unconditional" forms that do not exist; those comments are corrected.
  `Typing.v` also defines the stronger certificate target
  `match_coverage_property` and proves `match_coverage_implies_exhaustiveness`
  plus `progress_from_match_coverage` (which discharges only the
  exhaustiveness premise, not confluence); the remaining work is to make the
  checker or `T_Match` construct that coverage certificate AND to close
  confluence.
- **Preservation, confluence, strong normalization** (full calculus): open.
  Preservation is Qed-closed only conditional on the named `substitution_property`
  Prop spec. Confluence is open at the diamond-lemma level (`par_diamond_spec`):
  `Confluence.v` proves the parallel-reduction embeddings (`par_refl`,
  `step_implies_par`, `par_implies_steps`) and the composition theorem
  `confluence_from_par_star_diamond : par_star_diamond_spec -> confluence_spec`,
  but the substantive Tait-Martin-Löf diamond (`par_diamond_spec`, hence
  `par_star_diamond_spec`) is left as an open `Prop` specification. Confluence
  is therefore NOT proved (conditionally or otherwise); it is a stated open
  obligation, and every theorem that takes `confluence_property` as a hypothesis
  (progress, `canonical_forms_pi`, `conv_eq_trans`) is conditional on it.
  SN-admissible is stated as a conjecture. The current closed SN frontier is
  the flat affine theorem plus the non-affine neutral-expansion kernel, not the
  full admissible-fragment normalization theorem.
- **Presheaf-model adequacy**: paper-only proof sketch; mechanization open
  beyond the flat fragment.
- **Explicit tracked admits**: the tracked Coq/Rocq files currently contain no
  explicit `Admitted.` statements and no live `admit` tactics. This count is
  separate from named open `Prop` premises, abstract `Parameter` declarations,
  and Lean `axiom` declarations. A zero-`Admitted` count is NOT the same as
  unconditional soundness: the load-bearing metatheory (progress, preservation,
  conversion) is closed only modulo named open `Prop` hypotheses
  (`confluence_property`, `substitution_property`, `match_exhaustiveness_property`),
  and confluence's diamond lemma is itself an open `Prop` spec, so those
  hypotheses are undischarged.
- **Coq/Lean asymmetry on the certificate mechanical bit**: `mechanical_bit_correct`
  (the discretion-frontier-empty ⇔ mechanical-bit-true property of
  `DerivationCertificate`) is a Qed-closed `Theorem` in `coq/LexCore.v:297` but
  is declared as an `axiom` in `lean/LexCore.lean:225`. The two are not at the
  same strength: the Coq `Theorem` is derived trivially from a
  `dc_mechanical_sound` field carried inside the `DerivationCertificate` record
  (it re-exports a proof obligation the record already assumes), and both
  assistants ultimately push correctness onto the Rust BUILDER in
  `crates/lex-core/src/core_calculus/cert.rs` rather than proving the builder
  preserves the invariant. Neither form is a mechanized proof of the builder;
  the Lean `axiom` makes that explicit and the Coq `Theorem` hides it behind a
  record field.

For the per-statement status (including temporal non-regression, pack
re-evaluation soundness, the verdict Heyting algebra, PCAuth quorum extraction,
receipt locality,
priority-evaluator agreement, propagation-graph alignment, and the supporting
Qed-closed lemmas), consult `coq/Lex/PaperMechanization.v`, the
dedicated `coq/Lex/*.v` files, and the paper's §5.1 appendix.

## Lex-to-Op adequacy frontier

The public formal boundary is an admission contract, not a full compiler
correctness theorem. A compiled Op payload can be admitted only when the
envelope binds the elaborated Lex source, rule pack, context, compiler,
primitive registry, gas schedule, certificate/proof summary, effect row,
capability row, receipts, PCAuth-filled holes, and exact payload digest.

Currently supported formal components are:

- finite effect monotonicity for effect derivation trees;
- receipt locality / no-laundering for admission-host receipts;
- PCAuth quorum extraction over exact signed payload fields;
- structural admission-envelope lemmas that fail closed on payload mismatch,
  unaccepted receipts, unverified fills, and non-empty failed or deferred
  predicates.

Remaining adequacy obligations are:

- define the checked compiler domain as a source-side property over the current
  executable admissible fragment and any admitted frontier lowerings;
- prove lowering coverage for each admitted constructor and reject all other
  surface forms, including recursion, dependent pairs, modal forms, temporal
  coercions, unresolved content references, open holes, and unchecked fills;
- connect the Lex certificate builder to the admission envelope fields;
- prove emitted Op payloads typecheck against the bound primitive registry,
  payload schema, and gas schedule;
- prove verdict preservation, obligation preservation, and effect/capability
  non-expansion for typechecked emitted payloads;
- extract or check match-coverage certificates for fail-closed branch lowering;
- bind pause/resume or host-await evidence, if used, to typed receipts rather
  than ambient host state;
- close replay protection by requiring source, pack, context, compiler,
  registry, gas, and payload digest equality at admission.

## Building

### Coq

```
cd formal/coq
coqc LexCore.v
```

### Lean

```
cd formal/lean
lean LexCore.lean
```

(For the Lean scaffold, `mathlib` is optional; the file is self-contained.)

## Relation to the Rust reference

Every declaration in the formal scaffolds has a Rust counterpart in
`crates/lex-core/src/core_calculus/`:

| Formal construct            | Rust module                                 |
|-----------------------------|---------------------------------------------|
| `Rule` / `MetaRule` / `Lt`  | `core_calculus::level`                      |
| `FourTuple` / `Proof` / `TribunalCoercion` | `core_calculus::monotone`    |
| `Asof n`                    | `core_calculus::temporal`                   |
| `Hole` / `HoleFill` / `authorised` | `core_calculus::hole`                |
| `ProofBody` / `ProofSummary` / `compileSummary` | `core_calculus::summary` |
| `PriorityGraph`             | `core_calculus::principle`                  |
| `WitnessSupplyOracle` / `OracleResponse` | `core_calculus::oracle`        |
| `DerivationCertificate`     | `core_calculus::cert`                       |
| `AdmissibleWitness` / `isAdmissible` | `core_calculus::cert` (via mechanical_check) |
| admission-envelope fields   | certificate / admission-envelope target       |

The Rust implementation is the executable witness for the scaffold-level
forward direction only. Paper-level decidability remains conditional on the
full-calculus conversion, confluence, preservation, match-exhaustiveness, and
WHNF obligations described above.
