# Lex Substrate Interface

> **Status: draft v0.1 — not yet frozen.** This document specifies the interface contract that the Op typed bytecode (companion paper *Op: A Typed Bytecode for Compliance-Carrying Operations*) and other downstream consumers depend on. Per `ROADMAP.md` Phase E, v1.0 is frozen after the Phase A metatheory closures land and after one round of synchronous design with the Op paper author.

The substrate interface is the discipline that makes Lex a *load-bearing* substrate rather than a moving target. Downstream papers quote this interface, never Lex's internal representations. Lex internal evolution is unconstrained as long as the interface contract is preserved.

---

## 1. Purpose

A downstream paper consuming Lex needs to know exactly what it can rely on:

- *Which Lex types* are part of the public surface, with which universe levels.
- *Which Lex reduction relations* are exported, with which termination and confluence guarantees.
- *Which Lex theorems* are Qed-closed and may be quoted.
- *Which Lex effects* are inspectable downstream, and which are abstract.
- *Which Lex dependent records* (PCAuth, CanonBridge) are *opaque* to downstream — only Lex's verifier kernel decodes them.
- *Which Lex evolution paths* require an interface version bump (v2.0) and which do not.

This document specifies all of the above. It is the contract.

---

## 2. Versioning policy

- **v1.0** ships with the platonic-ideal Lex paper after `ROADMAP.md` Phase A and Phase B.2 deliverables land.
- **v1.x** (x > 0) absorbs *backward-compatible* additions: new Qed-closed theorems downstream may quote, new prelude types added without removing old, new admissible-fragment members added without changing the typing rules of existing members.
- **v2.0** is required if any of the following change:
  - The signature of any exported type (e.g., the universe level of `ComplianceVerdict`).
  - The semantics of any exported reduction relation (e.g., a defeasible-resolution rule's verdict).
  - The statement of any quoted theorem (e.g., progress's hypotheses).
  - The opaqueness boundary of PCAuth or CanonBridge.
- **No silent revisions of v1.0.** A bug in v1.0 that requires a semantics change is patched as v2.0 with explicit changelog. The v1.0 spec remains accessible (git tag `lex-substrate-v1.0`) for downstream papers that pinned to it.

The versioning replaces co-authorship coupling: Lex 1.0 ships first; Op 1.0 ships against v1.0; if Op 1.0 finds a load-bearing gap in v1.0, Lex publishes v2.0 with an explicit migration note.

---

## 3. Exported types (target v1.0)

The following are proposed substrate types, not a claim that these signatures already exist in the executable or Rocq exports. Check each name and universe against the implemented interface before freezing it.

### 3.1 Verdict and supporting prelude types

```
ComplianceVerdict : Type_0
  -- Bounded five-element chain ordered by legal restrictiveness
  -- Constructors: NonCompliant < Pending < NotApplicable < Exempt < Compliant
  -- Heyting structure proved (the proposed Lex manuscript §7.4, formal/coq/Lex/VerdictHeyting.v)

SanctionsResult : Type_0
  -- Two-valued: Clear, NotClear

Bool : Type_0
Nat : Type_0
ComplianceTag : Type_0
Time_0 : Type_0   -- Frozen historical time
Time_1 : Type_0   -- Derived legal time

IncorporationContext : Type_0
  -- The structured input to a compliance rule; record type with
  -- per-jurisdiction field families (FSRA fields for ADGM contexts,
  -- SIBA fields for BVI contexts, etc.)

Collection(T : Type_0) : Type_0
List(T : Type_0) : Type_0
Set(T : Type_0) : Type_0
Multiset(T : Type_0) : Type_0
```

### 3.2 Calculus types

```
Term : Type_0
  -- The core Lex term language; the constructor inventory is defined
  -- in formal/coq/Lex/Syntax.v

Branch : Type_0
  -- A match branch: pattern + body
Exception : Type_0
  -- A defeasible exception: guard + body + priority

EffectRow : Type_0
  -- The effect-row monoid; bounded semilattice with empty as unit

ContextEntry : Type_0
Context : Type_0
  -- Typing-context ribbons (de Bruijn)
```

### 3.3 Modal types

```
[T : Tribunal] (A : Prop) : Prop
  -- Tribunal-indexed modal proposition
  -- Two tribunals may assert contradictory propositions about identical facts

CanonBridge(T1 T2 : Tribunal, A : Prop) : Type_1
  -- Mutual-recognition witness; opaque to downstream
  -- (See §5 below for opaqueness commitment)

PCAuth(auth : Authority, h : HoleId) : Type_1
  -- Proof-carrying authorization witness; opaque to downstream
  -- Carries: signer DID, role attestation, scope witness, Time_0 timestamp,
  -- Ed25519 signature over (signer, hole-id, value)
```

### 3.4 Hole types

```
DiscretionHole(auth : Authority, h : HoleId, T : Type_l, S : Scope) : Type_l
  -- A typed discretion hole; carries effect discretion(auth)

MechanicalHole(T : Type_l) : Type_l
  -- A hole within the core of settled meaning; discharged by
  -- ordinary typing and reduction

UnsettledHole(dom : Domain) : Type_l
  -- Marks a domain where law has no disposition;
  -- clears only by rule-pack rewrite issued through legislative action
```

---

## 4. Exported reduction relations and termination guarantees (target v1.0)

The following are target reduction contracts. The full-calculus guarantees are obligations; the administrative WHNF result does not establish them.

### 4.1 Admissible-fragment WHNF reduction

```
whnf_admissible : Term → option Term
  -- Weak-head-normal-form reduction within the admissible fragment
  -- Target: total under a proved full-calculus bound; currently open

Theorem (WHNF-bounded reduction):
  ∀ t : Term, admissible t → ∃ k : Nat, whnf_k(t) terminates in WHNF
  -- Proposed full-calculus bound: requires proof; the administrative bound
  -- alone does not establish this statement
  -- (the proposed Lex manuscript §5; formal/coq/Lex/PaperMechanization.v whnf_bounded_reduction)
  -- Target v1.0 requirement: Qed-closed (per ROADMAP.md A.2)
```

### 4.2 Full-calculus reduction

```
step : Term → Term → Prop
  -- Single-step operational semantics; binder-congruence
  -- step rules plus head-step rules
  -- (formal/coq/Lex/Typing.v)

steps : Term → Term → Prop
  -- Reflexive transitive closure of step

par : Term → Term → Prop
  -- Tait-Martin-Löf parallel reduction
  -- (formal/coq/Lex/Confluence.v)

Theorem (confluence):
  ∀ t t1 t2, steps t t1 → steps t t2 → ∃ t', steps t1 t' ∧ steps t2 t'
  -- Target v1.0 requirement: Qed-closed (per ROADMAP.md A.3, dependent on par_diamond_spec)
```

### 4.3 Type-checking decidability

```
type_check : Context → Term → Type_l → option (HasType ctx t T)
  -- Bidirectional type checker for the admissible fragment
  -- Proposed new implementation target; this file does not currently exist

Theorem (admissible type-checking decidable):
  ∀ ctx t T, admissible t →
    Decidable (HasType ctx t T)
  -- A terminating sound-and-complete decision procedure is required.
  -- Merely returning Some or None does not establish decidability.
  -- Target v1.0 requirement: Qed-closed (depends on whnf_bounded_reduction; A.2)
```

---

## 5. Opaqueness commitments (target v1.0)

Two dependent record types are opaque to downstream consumers: Lex's verifier kernel is the sole decoder.

### 5.1 PCAuth opacity

This is a target boundary. The current `PCAuthVerifier` implementation contract and the distinction between structural checking, symmetric HMAC, and absent asymmetric verification are documented in `crates/lex-core/src/core_calculus/hole.rs`. A proposed opaque record does not certify those deployment guarantees.

`PCAuth(auth, h)` is a dependent record carrying signer DID, role attestation, scope witness, Time_0 timestamp, and Ed25519 signature over (signer, hole-id, value). Downstream consumers (Op, other institutional consumers, etc.) treat `PCAuth` as an opaque proof term:

- **What is exported.** The fact that a `PCAuth(auth, h)` witness exists for a given authority and hole-id; the fact that it discharges the `discretion(auth)` effect; the fact that the Lex verifier kernel can verify it against the credential chain rooted at the named authority.
- **What is NOT exported.** The internal structure of the dependent record. Downstream may not pattern-match on the signer DID, the timestamp, or the signature bytes. Downstream may verify only that a witness *exists* and *verifies* through Lex's kernel API.
- **Why.** The chosen cryptographic scheme and its verified implementation can evolve. Ed25519 and hybrid post-quantum admission are target requirements when selected by the deployment contract. Downstream consumers that depended on the internal structure would break under the cryptographic upgrade. Opaqueness preserves substrate evolution.

### 5.2 CanonBridge opacity

`CanonBridge(T1, T2, A)` is a mutual-recognition witness: a term proving two tribunals agree on a proposition `A`. Downstream consumers treat it as an opaque proof term:

- **What is exported.** The fact that a `CanonBridge(T1, T2, A)` witness exists; the fact that it permits the coercion `coerce[T1 => T2](e, w) : [T2] A`; the fact that the Lex verifier kernel can verify the bridge against both tribunals' credential roots.
- **What is NOT exported.** The internal structure of the bridge witness, which may include scope restrictions, validity windows, signature aggregation across multiple tribunal officers, and other internal cryptographic detail subject to evolution.
- **Why.** Same as PCAuth: bridge cryptography is evolving; opaqueness preserves substrate evolution.

---

## 6. Exported theorems (target v1.0)

The following table specifies proposed theorem exports for target v1.0. It is not an installed module or an assertion of present closure. Current status is in `formal/README.md`; full-calculus premises must be discharged before a consumer may rely on the corresponding unconditional guarantee.

| Theorem name | Statement (informal) | Rocq target | v1.0 status target |
|---|---|---|---|
| `weakening_property` | Adding a typing-context entry preserves typing | `formal/coq/Lex/Typing.v` | Qed-closed unconditionally (after A.1) |
| `confluence` | The step relation is confluent | `formal/coq/Lex/Confluence.v` | Qed-closed (after A.3) |
| `preservation_admissible` | Admissible-fragment reduction preserves typing | `formal/coq/Lex/Typing.v` | Qed-closed (after A.4) |
| `progress_admissible` | Well-typed admissible-fragment terms reduce or are values | `formal/coq/Lex/Typing.v` | Qed-closed unconditionally (after A.4) |
| `whnf_bounded_reduction` | WHNF reduction terminates under polynomial-bounded fuel | `formal/coq/Lex/PaperMechanization.v` | Qed-closed (after A.2) |
| `type_check_decidable_admissible` | Admissible-fragment type-checking is decidable | `formal/coq/Lex/TypeChecker.v` (new target) | Qed-closed (depends on `whnf_bounded_reduction`) |
| `verdict_is_heyting` | `ComplianceVerdict` carries a Heyting algebra structure | `formal/coq/Lex/VerdictHeyting.v` | Qed-closed (already in current state) |
| `defeasible_effect_join` | The defeasible-rule effect row is a join of base + exception rows | `formal/coq/Lex/PaperMechanization.v` | Qed-closed (already in current state) |
| `bridge_composition` | Composition of CanonBridge witnesses is a CanonBridge | `formal/coq/Lex/PaperMechanization.v` | Qed-closed (already in current state) |
| `bridge_identity_units` | Identity CanonBridge for self-tribunal coercion | `formal/coq/Lex/PaperMechanization.v` | Qed-closed (already in current state) |
| `feature_integration` | Four primitives compose without mutual interference | `formal/coq/Lex/Integration.v` (new) | Qed-closed (after A.6) |
| `expressiveness_boundary` | Lex captures rules satisfying mechanical-evaluability-modulo-typed-holes | `formal/coq/Lex/Boundary.v` (new) | Qed-closed (after A.7) |
| `discretion_hole_curry_howard` | Discretion holes correspond to control-operator-like terms in co-classical fragment | `formal/coq/Lex/CurryHoward.v` (new) | Qed-closed (after B.2) |

The proposed `Lex.Substrate.v1` export module must be implemented and checked before these names form a consumer contract.

---

## 7. Effect-row export

The effect-row vocabulary exported in v1.0:

```
read
write(scope : Scope)
attest(authority : Authority)
authority(ref : AuthorityRef)
oracle(ref : OracleRef)
fuel(level : Level, amount : Nat)
sanctions_query
discretion(authority : Authority)
```

Downstream consumers may inspect the effect row of a Lex term (read it, decompose it as a join, check membership of any specific effect). Downstream consumers may NOT extend the effect-row vocabulary: new effects require a Lex v2.0 interface bump.

The effect row is a bounded semilattice with the empty row as unit. Branch-sensitive markings are exported; downstream consumers that compose Lex terms with their own branches must respect the branch-sensitive privilege-elevation discipline.

---

## 8. What is NOT exported (substrate-internal)

The following are internal to Lex and not part of the substrate interface:

- **Source-language representations.** The Rust crate `lex-core`'s parser, elaborator, and surface syntax are internal. Downstream may consume only elaborated `Term` values.
- **Diagnostic messages.** The `lex-diag` controlled-English diagnostic ontology is internal; downstream consumers receive structured error codes, not message strings.
- **Pretty-printer output formats.** Internal.
- **The `Lex_erased` sub-calculus** and the `Prop`-erasure machinery: internal optimization, not substrate-visible.
- **Internal mechanization helpers.** `parallel_subst`, `shift_subst_commute_ws`, `subst_subst_ws`, etc. are internal proof primitives; downstream may not quote them.
- **The reducibility-candidates argument** for non-affine SN, the diamond-lemma proof, the par-relation infrastructure: all internal mechanization detail.

---

## 9. Cross-references

- **`PLATONIC-IDEAL.md`** §1 — the substrate principle: every design decision in Lex is judged against substrate strength.
- **`ROADMAP.md`** Phase E — the path from this draft to v1.0 freeze.
- **`SUPREMUM.md`** §12 — the public Lex-to-Op integration target and its evidence boundary.
- **`formal/coq/Lex/AdmissionEnvelope.v`** — the structural admission-envelope theorem; full Lex-to-Op adequacy remains a separate obligation.
- **Op companion paper** *Op: A Typed Bytecode for Compliance-Carrying Operations* — the primary downstream consumer of this interface.
- **`formal/coq/Lex/`** — the Rocq mechanization. Each exported theorem in §6 cross-references its Rocq target file.

---

## 10. Changelog

- **v0.1 (this document).** Initial draft, not yet frozen. Pending: Phase A.1–A.7 mechanization closures, Phase B.2 Curry-Howard correspondence, one round of synchronous design with Op author. After all of these, v0.1 → v1.0 with the freeze tag `lex-substrate-v1.0`.
