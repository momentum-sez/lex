# Lex Core Calculus — Formal Scaffolds

Companion formal mechanisations for Frontier 08 (`docs/frontier-work/08-lex-core-calculus.md`).

## Layout

- `coq/LexCore.v` — Coq 8.18+ scaffold (primary mechanisation)
- `lean/LexCore.lean` — Lean 4.14+ scaffold (mirror)

## Status

Both files declare the nine PLATONIC-IDEAL §5.1 commitments as types in the
respective proof assistant. The critical soundness lemmas are proved; three
theorems carry `Admitted` / `axiom` with annotated proof strategies.

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
- **Admissible-fragment decidability** — both directions proved; the
  `is_admissible` function is a decidable characteristic.

### Admitted (with strategy)

1. **Principle-balancing termination** — Tarjan's SCC. Strategy: transcribe
   the algorithm, prove termination by strong induction on the edge list.
2. **Certificate well-formedness** — the mechanical bit's correctness.
   Strategy: introduce a `WellFormedDC` predicate, prove the builder
   preserves it.
3. **Oracle boundedness** — axiomatic (the oracle's declared contract).

## Building

### Coq

```
cd formal/coq
coqc LexCore.v
```

### Lean

```
cd formal/lean
lean --make LexCore.lean
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
