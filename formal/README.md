# Lex Core Calculus — Formal Scaffolds

Companion formal mechanisations for Frontier 08 (`docs/frontier-work/08-lex-core-calculus.md`).

## Layout

- `coq/LexCore.v` — Coq 8.18+ scaffold (primary mechanisation)
- `lean/LexCore.lean` — Lean 4.14+ scaffold (mirror)

## Status

Both files declare the nine PLATONIC-IDEAL §5.1 commitments as types in the
respective proof assistant. The critical soundness lemmas are proved; one
certificate-invariant theorem remains open with an annotated proof strategy.

### Proved (both assistants)

- **Level non-self-application** — `Rule<L>` cannot appear in the body of
  `MetaRule<L>` (no `Lt L L` inhabitant).
- **Tribunal coercion shape** — `idCoercion` totally returns `Some`; the
  `noBridgeCoercion` totally returns `None` (honest refusal).
- **Temporal lift totality** — `lift_to : Asof 0 → Asof n` is total;
  demotion is not expressible.
- **Hole authorisation** — the existence of a `HoleFill` witness implies
  the witness's signer matched the authority.
- **Summary preservation** — obligations, verdict, and discretion frontier
  are preserved by `compile_summary`.
- **Principle balancing termination (scaffold level)** — the frontier scaffold
  closes the local termination obligation present in this repository.
- **Oracle totality** — the witness-supply oracle theorem follows from the
  class/function definition.
- **Admissible-fragment decidability** — both directions proved; the
  `is_admissible` function is a decidable characteristic.

### Remaining Open

1. **Certificate well-formedness** — the mechanical bit's correctness.
   Strategy: introduce a `WellFormedDC` predicate, then model the Rust builder
   in `crates/lex-core/src/core_calculus/cert.rs` and prove it preserves the
   invariant.

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
