# Lex — Formal Mechanisations

This directory carries two distinct mechanized artifacts. They address
different obligations at different levels of the language and should not be
conflated.

## Layout

**1. Frontier scaffold (narrow-waist types only).**

- `coq/LexCore.v` — Coq 8.18+ scaffold for Frontier 08
  (`docs/frontier-work/08-lex-core-calculus.md`).
- `lean/LexCore.lean` — Lean 4.14+ mirror.

These files declare the nine PLATONIC-IDEAL §5.1 commitments as types in the
respective proof assistant. They are scaffolds, not a full calculus
mechanization: admissibility here is the narrow-waist `is_admissible` on the
frontier API, not the full-calculus admissibility predicate of the paper.

**2. Full calculus mechanization (paper-level).**

- `coq/Lex/` — the full Lex core-calculus mechanization referenced by the
  Lex paper. `Lex/PaperMechanization.v` is the per-statement correspondence
  between paper theorems/propositions and their Rocq status.
- `coq/FlatAdmissibleSN.v` — strong normalization for the flat admissible
  fragment.

## Status (scaffold; both assistants)

Proved at the scaffold level only:

- **Level non-self-application** — `Rule<L>` cannot appear in the body of
  `MetaRule<L>` (no `Lt L L` inhabitant).
- **Tribunal coercion shape** — `idCoercion` totally returns `Some`; the
  `noBridgeCoercion` totally returns `None` (honest refusal).
- **Temporal lift totality** — `lift_to : Asof 0 → Asof n` is total;
  demotion is not expressible.
- **Hole authorisation (scaffold)** — the existence of a `HoleFill` witness
  implies the witness's signer matched the authority. Note: the executable
  admissible checker in `crates/lex-core/src/typecheck.rs` still rejects
  surface `Term::Hole` and `Term::HoleFill`, and `compose::evaluate_all_fibers`
  is a stub; see Frontier 08 §0.
- **Summary preservation** — obligations, verdict, and discretion frontier
  are preserved by `compile_summary`.
- **Principle balancing termination (scaffold)** — the frontier scaffold
  closes the local termination obligation present in this repository.
- **Oracle totality** — the witness-supply oracle theorem follows from the
  class/function definition.
- **Admissible-fragment decidability (scaffold)** — both directions proved
  for the scaffold `is_admissible` function. This is *not* the full-calculus
  admissibility decidability theorem; see next section.

Remaining open at the scaffold level:

1. **Certificate well-formedness** — the mechanical bit's correctness.
   Strategy: introduce a `WellFormedDC` predicate, then model the Rust builder
   in `crates/lex-core/src/core_calculus/cert.rs` and prove it preserves the
   invariant.

## Status (full calculus; paper-level)

Paper-level theorems and propositions are enumerated in
`coq/Lex/PaperMechanization.v`. The Lex paper's Mechanization Status appendix
(end of §5.1) is the authoritative per-statement ledger; the headline numbers
and honest qualifications are:

- **Qed-closed**: seven of twenty-five non-conjectural paper-level statements
  (28%).
- **Admissible-fragment decidability (full calculus)**: decidable type-checking
  for the admissible fragment is Qed-closed *conditional* on the bounded-reduction
  hypothesis `whnf_bounded_reduction`, which is currently `Admitted` in the
  Rocq formalization. This is a stronger claim than the scaffold-level
  decidability above and is not discharged unconditionally.
- **Weakening**: `weakening_property` is Qed-closed conditional on a single
  named Prop spec, `conv_eq_shift_compat_spec`; the gating obligation is a
  new parallel multi-substitution primitive for `step_match_ctor_fire`, open.
- **Progress**: Qed-closed over the full `Term` AST conditional on two named
  Prop premises (`confluence_property`, `match_exhaustiveness_property`),
  both open.
- **Preservation, confluence, strong normalization** (full calculus): open.
  Confluence is open at the diamond-lemma level (`par_diamond_spec`);
  SN-admissible is stated as a conjecture.
- **Presheaf-model adequacy**: paper-only proof sketch; mechanization open
  beyond the flat fragment.

For the per-statement status (including the verdict Heyting algebra, priority-
evaluator agreement, propagation-graph alignment, and the nine Qed-closed
supporting lemmas), consult `coq/Lex/PaperMechanization.v` and the paper's
§5.1 appendix.

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

The Rust implementation is the executable witness for the forward direction
of the decidability lemma.
