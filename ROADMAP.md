# Lex: Roadmap to the Platonic Ideal

> **Companion to `SUPREMUM.md` (current state) and `PLATONIC-IDEAL.md` (target state).** This document is the game plan: the phases that take Lex from current state to the platonic-ideal.

The roadmap has eight workstreams with logical dependencies. Preserve the full target while using actual runtime capacity and authorized resources. Parallel work is useful when dependencies and file ownership permit it. This plan does not authorize publication, outreach, or new standing goals.

---

## Dependency graph

```
                    Phase A
                 (Substrate Closure)
                        │
            ┌───────────┼───────────┐
            ▼           ▼           ▼
        Phase B     Phase C     Phase D
       (Curry-     (Position   (Categorical
        Howard)    Theorems)    & Modal)
            │           │           │
            └─────┬─────┴───────────┘
                  ▼
              Phase E
       (Substrate Interface)
                  │
        ┌─────────┼─────────┐
        ▼         ▼         ▼
    Phase F   Phase G   (continuous throughout)
   (Worked   (Writing &
   Examples) Visual Discipline)
                  │
                  ▼
              Phase H
        (Output Triple — sequenced last)
```

Phases F and G are *concurrent throughout* — worked examples are refined as the calculus stabilises, and writing tracks every other phase's outputs. Phase H is strictly last because the paper, companion, and book absorb everything that came before.

---

## Phase A — Substrate Closure

Phase A closes the integrated metatheory needed by later results. Current proof status is recorded in `formal/README.md` and the named Rocq declarations. A `Qed` ending proves its stated implication; it does not discharge that implication's hypotheses. Administrative WHNF bounds are closed. Full-calculus normalization, substitution, confluence, preservation, match coverage, and the resulting unconditional type-safety claims retain separate obligations. The Feature Integration and Expressiveness Boundary targets require precise statements before their proofs can be accepted.

### A.1 Close Defect 1 — `parallel_subst` primitive in `DeBruijn.v`

The current development proves weakening conditional on `conv_eq_shift_compat_spec`. `Confluence.v` identifies `par_subst_args_spec` and proves a fold/scoping bridge from the stronger `par_subst_at_depth_spec`. The at-depth substitution theorem remains open. Compare a parallel-substitution replacement with a proof of the existing fold under the precise required hypotheses; do not assume the historical proposed replacement has landed.

Reproduce the following proposed counter-witness against the exact historical reduction rule before using it to select a repair:
- `args = [v_0; v_5]`, `body = v_0`, outer cutoff `c = 0`, shift amount `d = 1`.
- Layered reduct yields `v_6`; shift-then-fire yields `v_0`.

One candidate resolution is a parallel multi-substitution primitive

```coq
parallel_subst : list Term → Term → Term
```

in `formal/coq/Lex/DeBruijn.v` with the appropriate shift-commutation lemmas, then, if that design closes the exact obligation, rewrite `step_match_ctor_fire`'s reduct to use that primitive.

**Deliverable A.1:** Constructor-fire substitution and shift compatibility proved for the selected representation; `conv_eq_shift_compat_spec` discharged; `weakening_property` Qed-closed unconditionally.

### A.2 Close `whnf_bounded_reduction`

`PaperMechanization.v` closes `administrative_whnf_bounded_reduction`, sufficient fuel, and the canonical bound for the administrative `WhnfTerm` fragment. The full admissible-calculus bound remains stronger. Two candidate routes toward that full bound are:

- **Constructive proof** of the bounded-reduction hypothesis directly.
- **Explicit polynomial bound** replacing the existential statement, with a proof that the bound suffices.

**Deliverable A.2:** `whnf_bounded_reduction` Qed-closed (or replaced with explicit-bound variant); combine this result with discharged substitution, confluence, preservation, and coverage obligations before claiming unconditional admissible-fragment decidability.

### A.3 Close confluence

`par_diamond_spec` is named as a Prop in `formal/coq/Lex/Confluence.v` but not Qed; the Tait–Martin-Löf parallel-reduction infrastructure is in place (`par`, `par_branch`, `par_exception` mutual inductives plus the bidirectional `step_implies_par` / `par_implies_steps` bridges, all already Qed). The diamond-lemma proof completes the chain. Once `par_diamond_spec` is Qed-closed, `par_star_diamond_spec` follows by standard induction; `confluence_spec = confluence_property` follows from the bridge between `par` and `steps`.

**Deliverable A.3:** `par_diamond_spec`, `par_star_diamond_spec`, `confluence_spec` all Qed-closed; the calculus is unconditionally confluent.

### A.4 Close preservation and progress for the full admissible fragment

Currently progress is Qed-closed *conditional on* `confluence_property` and `match_exhaustiveness_property`. Once A.3 closes, the confluence dependency is discharged. Match exhaustiveness is a separate obligation: tighten the typing rule `T_Match` to enforce that branches cover every constructor of the scrutinee's inductive type (an invariant separate from the weakening-related arity-shift refactor in §4.2), then progress closes outright.

Preservation is proved conditional on `substitution_property`; its unconditional full-calculus form remains open. The coverage certificate target and `progress_from_match_coverage` already separate the exhaustiveness premise from confluence. Construct the required coverage evidence and discharge both premises.

**Deliverable A.4:** `match_exhaustiveness_property` Qed-closed via the typing-rule tightening; preservation Qed-closed for the full admissible fragment with Pi-types, effect rows, and discretion holes; progress Qed-closed unconditionally.

### A.5 Close the full theorem ledger

Use the current declarations and `formal/README.md` to maintain a theorem-by-theorem ledger. Record the statement, source, assumptions, and proof status. Close the full paper-level obligations in dependency order, including targets that need new Rocq files.

**Deliverable A.5:** Every theorem claimed by the completed calculus has a checked proof with all advertised premises discharged. Conjectures retain their explicit classification. A percentage or count cannot substitute for the theorem ledger.

### A.6 Prove the Feature Integration Theorem

The target integrated calculus admits unconditional preservation, progress, decidability of admissible-fragment type-checking, and the Curry-Howard reading of Phase B, with no feature appearing as a side condition on another's metatheorem. Three sub-obligations (per `PLATONIC-IDEAL.md` §2):

- **(IFi) Type-rule confluence** between the four feature-specific typing rules (defeasibility, temporal stratification, tribunal modality, typed discretion holes).
- **(IFii) Reduction interleaving** without mutual interference: pairwise non-interference statements between every pair of features.
- **(IFiii) Effect-row composition** preserved across binders introduced by all four features.

**Deliverable A.6:** Feature Integration Theorem stated precisely; three sub-obligations Qed-closed; the theorem becomes the spine of the platonic-ideal Lex paper's central section.

### A.7 Prove the Lex Expressiveness Boundary Theorem

Per `PLATONIC-IDEAL.md` §3: for every legal rule `R = (input-types, output-type, evaluation-procedure)`, `R` is expressible as a closed Lex term iff (EBi)–(EBiii). Two directions:

- **"If" direction** (constructive): every rule satisfying (EBi)–(EBiii) admits a Lex term. Elaboration recipe.
- **"Only if" direction** (the limit theorem): rules failing any of (EBi)–(EBiii) cannot be expressed in Lex without an `UnsettledHole`. Proof obligation includes a precise definition of "legal rule" as a function from typed fact-bases to verdicts under a specified evaluation discipline.

**Deliverable A.7:** Lex Expressiveness Boundary Theorem stated precisely; both directions proved (or, in the platonic-ideal commitment, both Qed-closed in Rocq via a formalisation of the underlying rule-as-function definition).

---

## Phase B — Curry-Howard Completion

After Phase A closes the metatheory, Phase B completes the Curry-Howard story. Per `PLATONIC-IDEAL.md` §5: the discretion-hole correspondence is the centerpiece (target full mechanization); the other three (defeasibility-as-effects, temporal-stratification-as-modal, tribunal-as-multi-modal-MTT) are compatible-conjectured.

### B.1 Literature audit

Audit:
- **Murthy 1991** (classical computation as call/cc).
- **Griffin 1990** (call/cc and classical logic).
- **Krivine** and **Miquel** (realizability for classical proofs).
- **Kohlenbach** (proof mining).
- **Pfenning–Davies 2001** (judgmental S4).
- **Nanevski–Pfenning–Pientka 2008** (contextual modal type theory).
- **Levy 1999** and **Filinski 1994** (call-by-push-value, exception monads — for the defeasibility-as-effects compatible-conjectured correspondence).
- **Gratzer–Kavvos–Nuyts–Birkedal 2020** (multi-modal MTT — for the tribunal compatible-conjectured correspondence).

The audit's outcome positions PCAuth-as-attestation against the existing literature: as a conservative extension (likely), as an instance (possible), or as an independent correspondence (unlikely but possible).

**Deliverable B.1:** Literature audit document at `docs/architecture/CURRY-HOWARD-LITERATURE-AUDIT.md` with the position summary.

### B.2 Mechanize the discretion-hole Curry-Howard correspondence

Position PCAuth as a control-operator-like term in a co-classical fragment. The `fill(h, e, w)` rule is the control-operator activation; the witness `w : PCAuth(auth, h)` discharges the classical-style assumption that the proposition holds because a recognised authority asserts it. The resulting term inhabits the proposition `phi_h(value) ∧ authorized(h, signer) ∧ temporally-admissible(audit)` constructively, by attestation rather than mechanical derivation.

**Deliverable B.2:** Discretion-hole Curry-Howard correspondence stated and Qed-closed in `formal/coq/Lex/CurryHoward.v` (new file); §13.2 of the proposed manuscript closes; the proposed Lex manuscript central paper section absorbs the result.

### B.3 Conjecture-with-evidence the other three correspondences

For each of defeasibility-as-effects, temporal-stratification-as-modal, tribunal-as-multi-modal-MTT:

- State the correspondence precisely.
- Provide partial-evidence proof (e.g., a typing-rule embedding that preserves derivability on a sub-fragment).
- Name the obstruction to the full correspondence (typically: a feature-interference issue requiring Phase A.6 outputs, or a missing categorical-semantics ingredient requiring Phase D outputs).

**Deliverable B.3:** Three compatible-conjectured correspondences stated with partial-evidence proofs and named obstructions; recorded in `PLATONIC-IDEAL.md` §5 as the table entries.

---

## Phase C — Position Theorems

After Phase A. Phase C executes the three position theorems of `PLATONIC-IDEAL.md` §6 against frozen targets.

### C.1 Catala-2024 embedding and separation

Frozen target: Catala-2024 = Merigoux, Chataing, Protzenko (ICFP 2021) plus the publicly-specified extensions of the Catala-2024 implementation.

Translate every Catala-2024 program to a Lex term preserving verdict semantics on the common fragment. Exhibit a Lex program (with a non-trivial `PCAuth`-witnessed discretion hole or `CanonBridge` coercion) that no Catala-2024 program can simulate even under arbitrary computable preprocessing.

**Engagement:** invite Merigoux to co-author the Catala chapter, or solicit expert review (per `PLATONIC-IDEAL.md` §9 — co-authorship by expert preference, otherwise review with attribution).

**Deliverable C.1:** Catala-2024 embedding theorem and separation theorem stated, proved, and (target: Qed-closed in Rocq); robustness analysis of what would invalidate either direction; published as a chapter of the platonic-ideal Lex paper.

### C.2 Governatori-Antoniou 2004 faithful encoding

Frozen target: Governatori, Antoniou, Maher, Billington (AAAI 2000) plus Governatori 2005 parameterized-superiority extension.

Faithful encoding of DDL-2004 into Lex's priority-graph + Heyting-verdict-lattice semantics. Separation: typed-discretion-hole fragment of Lex has no encoding back into DDL-2004 because DDL-2004 is untyped.

**Engagement:** invite Governatori to co-author the defeasible-logic chapter, or solicit expert review.

**Deliverable C.2:** DDL-2004 faithful encoding stated, proved, target Qed-closed; published as chapter.

### C.3 L4 CCLAW 2022 translation in one direction

Frozen target: L4 specification of Lim et al. (2021) in the CCLAW core fragment as of 2022.

Translation of the regulatory-compliance fragment of L4 into Lex (the fragment that encodes statutory rules, excluding the deontic-contract fragment for bilateral obligations). Obstruction theorem: the contract fragment of L4 has no faithful encoding into Lex without explicit typed deontic operators.

**Engagement:** review by CCLAW.

**Deliverable C.3:** L4 translation stated, proved, target Qed-closed; obstruction theorem stated; published as chapter.

---

## Phase D — Categorical and Modal Completion

After Phase A. Phase D defines the new class of 2-modal logics (per `PLATONIC-IDEAL.md` §7) and completes the categorical/denotational semantics (per `PLATONIC-IDEAL.md` §8).

### D.1 Tribunal-modal-logic literature audit

Audit:
- **Mac Lane–Moerdijk** (1992) — *Sheaves in Geometry and Logic*: topos-internal modal logic.
- **Awodey** — modal HoTT, *Univalent Foundations* line.
- **Reyes** — functorial semantics of higher-order modal logic.
- **Pfenning–Davies 2001** — judgmental reconstruction of modal logic.
- **Nanevski–Pfenning–Pientka 2008** — contextual modal type theory.
- **Bénabou 1967** — bicategories.
- **Coecke–Kissinger** — 2-categorical reasoning frameworks.

Outcome:
- **Subsumption.** An existing class contains 2-modal-over-bridge-2-category as a fragment. Position Lex's tribunal modal as instance/specialisation; soundness/completeness inherited.
- **Conservative extension.** Define new class precisely; prove soundness and completeness for it.
- **Independence.** No existing class fits; define from scratch with explicit proof-theoretic motivation.

**Deliverable D.1:** Literature audit document at `docs/architecture/TRIBUNAL-MODAL-LOGIC-AUDIT.md` with positioning outcome.

### D.2 Define and prove the 2-modal logic over bridge 2-categories

Per the audit outcome:

- A 2-category `B` of authorities, with finite limits.
- A 2-functor `M : B → Cat` (or `Heyt` for propositional fragment).
- Modal operators `[T]_B : Prop → Prop` for each tribunal-object `T ∈ Ob(B)`, with bridge naturality.
- 2-cell coherence for every recognition 1-cell pair and every 2-cell between them.

State and prove (target Qed-closed):
- **Soundness:** every term-calculus derivation interprets to a valid 2-modal-logic proof.
- **Completeness:** every valid 2-modal-logic proof reflects to a term-calculus derivation.

**Deliverable D.2:** Definition and soundness/completeness theorems stated; published as chapter; target Qed-closed in `formal/coq/Lex/TribunalModalLogic.v`.

### D.3 Push categorical semantics to soundness and adequacy

Adequacy of the proposed presheaf model remains an open target. Push to fully Qed-closed for the full admissible fragment, with each per-constructor case (six Lex-specific cases beyond the standard CwF cases) discharged by its own proof.

**Deliverable D.3:** Adequacy of the presheaf model Qed-closed; the categorical semantics is unconditionally sound and adequate; full abstraction explicitly preserved as conjecture (per `PLATONIC-IDEAL.md` §8) with proof-relevant-game-semantics named as the technical-content target.

---

## Phase E — Substrate Interface (v1.0 freeze)

After Phases A and B. Phase E specifies and freezes the v1.0 substrate interface contract that Op (Paper 3 in the published series) and other downstream consumers can rest on.

### E.1 Define v1.0 interface

Specify in `SUBSTRATE-INTERFACE.md`:

- **Type-level guarantees** (which Lex types are exported, with what universe levels).
- **Operational guarantees** (which reduction relations are exported, with what termination/confluence properties).
- **Mechanized invariants** (which Qed-closed theorems downstream may quote).
- **Effect-row export** (which effects downstream may inspect; which are abstract).
- **Tribunal-bridge and PCAuth opacity** (downstream sees the dependent records as opaque; only Lex's verifier kernel decodes them).

### E.2 Co-design rounds with Op author

Brief synchronous design rounds with the Op paper author to confirm the interface satisfies Op's needs without leaking Lex internals. The output is a versioned interface, not a co-authored design.

### E.3 Freeze v1.0; document; publish

Freeze the interface with explicit semver. Op proceeds against v1.0. Lex 2.0 follows downstream feedback if Op identifies a load-bearing gap.

**Deliverable E.3:** `SUBSTRATE-INTERFACE.md` v1.0 published; semver tag `lex-substrate-v1.0` on `develop`; documented in the platonic-ideal Lex paper's appendix.

---

## Phase F — Worked Examples

Concurrent throughout. Phase F is not a discrete phase but a continuous obligation: as the calculus stabilises, the worked examples in the proposed Lex manuscript §7 (BVI director residency, ADGM-DIFC mutual recognition, Pakistan-directors tolling, ADGM fit-and-proper, the cross-jurisdictional rule with dependent types, the sanctions hard-block, the verdict lattice, the fill round-trip, the multi-feature example, the temporal stratification with tolling) are updated to remain valid.

### F.1 Verify existing examples close against final calculus

After each phase A.* deliverable lands, re-verify that every worked example in the proposed Lex manuscript §7 still typechecks and produces the expected verdict in the updated calculus. Existing mechanizations live in `formal/coq/Lex/Examples/*.v`.

**Deliverable F.1 (continuous):** Every worked example Qed-closed against the final calculus.

### F.2 Add an integration example

Add one new worked example that exercises all four features simultaneously (defeasibility, temporal stratification, tribunal modality, typed discretion hole) and demonstrates the Feature Integration Theorem on a concrete legal rule.

**Deliverable F.2:** New worked example in the proposed Lex manuscript §7 and corresponding Rocq mechanization in `formal/coq/Lex/Examples/Integration.v`.

---

## Phase G — Writing and Visual Discipline

Concurrent throughout. Phase G is the paper-writing track that consumes outputs from every other phase.

### G.1 Two introductions

Write two introductions for the platonic-ideal Lex paper:
- A *type-theoretic introduction* emphasizing the calculus, the metatheory, and the four primitives as type-theoretic constructs.
- A *legal-theoretic introduction* emphasizing Hart-Dworkin engagement, the four primitives as responses to the four structural deficiencies of compliance-as-code, and ADGM-DIFC mutual recognition as the canonical worked-rule.

The body of the paper is shared; the two introductions allow the paper to address both PL/type-theory communities (POPL, ICFP, LICS, FoSSaCS) and computational-legal-reasoning communities (ICAIL, JURIX, AAAI law track).

**Deliverable G.1:** Both introductions drafted; paper structure absorbs them as §0a (type-theoretic) and §0b (legal-theoretic) before §1.

### G.2 Single judgment-form notation; consistent rule-naming

Discipline:
- Single judgment-form notation across the paper (`Γ ⊢ e : T ! ρ` everywhere).
- Rule names follow `J-Form-Variant` convention (e.g., `T-LamCheck`, `R-DefeasibleResolve`, `S-TribunalLift`).
- Proof structure: theorem statement → proof sketch → mechanization pointer → discussion.
- Consistency over flourish.

**Deliverable G.2:** Notation pass complete; every rule name conformant; every theorem statement follows the four-part structure.

### G.3 Mechanization Methodology section

Add a §X (~5 pages) on what the Rocq mechanization revealed about the design. Cite POPLmark Challenge (Aydemir et al. 2005) as precedent. Document: the deep Defect 1 finding, the T_Match arity-shift refactor, the kickstart layered-form fix counter-witness. This documents the *process*, not the result.

**Deliverable G.3:** Mechanization Methodology section drafted; placed after metatheory, before related work.

### G.4 Refined open-problem catalogue

Per `PLATONIC-IDEAL.md` §11: each open problem stated as PROBLEM, ORIGIN, FORMAL STATEMENT, CURRENT BEST PARTIAL RESULT, CONJECTURED COMPLEXITY OR STATUS, PROPOSED ATTACK, WHY IT MATTERS FOR LEX. The current §13 partially does this; G.4 makes every entry uniform.

**Deliverable G.4:** §13 refined to the seven-field structure for every entry.

---

## Phase H — Output Triple

Sequenced last. Phase H produces three artifacts from the work of Phases A–G.

### H.1 Long paper

Length: 80–110 pages. Target venues: POPL, ICFP, LICS (conference); JLAP, LMCS (journal extended version). The full formal contribution.

**Deliverable H.1:** Long paper accepted at conference; journal extended version submitted.

### H.2 Short companion

Length: 12–20 pages. Target audience: practitioners (compliance engineers, legal-tech teams). Worked examples; tooling overview; intuitive explanation of the four primitives without the full formal apparatus.

**Deliverable H.2:** Short companion published after long paper accepted.

### H.3 Book

Length: 250–400 pages. Canonical tutorial reference covering the full contribution, all proofs, all mechanization, all examples, all comparative analysis. The book absorbs the long paper, the companion, and the additional material that the paper format does not accommodate.

**Deliverable H.3:** Book published over time as the field absorbs Lex.

---

## Cross-cutting commitments

### Co-authorship hybrid

For separately authorized outreach, seek expert review (not co-authorship) from Merigoux (Catala), Governatori (defeasible logic), Sozeau or Tabareau (Coq metatheory), Schauer or Tamanaha (legal theory). Default is review with attribution in acknowledgments; co-authorship by expert preference.

### Versioning replaces co-design coupling

Per `PLATONIC-IDEAL.md` §9: Lex 1.0 ships first with the Substrate Interface v1.0; Op 1.0 ships against v1.0; Lex 2.0 follows Op feedback if needed. Versioning replaces co-design coupling so that Lex paper development can complete without waiting for Op paper development.

### Honesty about classification

Every claim is classified as *proved*, *conjectured*, *open*, or *named-as-research-programme*, with the classification stated explicitly. The classification appears in the Mechanization Status appendix at the end of §5.1 of the paper, in `PLATONIC-IDEAL.md` Sections 2–10, and in this roadmap.

---

## Convergence criterion

The roadmap converges when:

1. All Phase A deliverables (A.1 through A.7) are achieved.
2. Phase B.2 deliverable (discretion-hole Curry-Howard correspondence Qed-closed) is achieved.
3. At least one of Phase C.1–C.3 deliverables (one position theorem proved) is achieved.
4. Phase D.2 deliverable (2-modal logic class defined; soundness/completeness proved) is achieved.
5. Phase E.3 deliverable (Substrate Interface v1.0 frozen and published) is achieved.
6. Phase F continuous deliverable (every worked example Qed-closed) is current.
7. Phase G deliverables (two introductions, notation discipline, mechanization methodology, refined open-problem catalogue) are integrated.
8. Phase H.1 deliverable (long paper) is published.

Once H.1 is achieved with the prior conditions, the platonic-ideal Lex paper exists. H.2 and H.3 follow.

---

## Falsifiers

The roadmap is wrong if any of the falsifiers in `PLATONIC-IDEAL.md` §12 fire:

- **(F1)** Integration theorem fails — Phase A.6 produces no proof, only an obstruction.
- **(F2)** Discretion-hole Curry-Howard correspondence has structural obstruction — Phase B.2 produces no Qed; demote to compatible-conjectured and promote temporal-stratification correspondence to centerpiece (Phase B.3 outputs become the new B.2).
- **(F3)** Catala-2025+ becomes more expressive than estimated — Phase C.1 separation direction degrades to equivalence on extended fragment.
- **(F4)** Full-fragment metatheory has barrier — Phase A.5 produces an undecidability theorem instead of decidability; admissible-fragment framing becomes permanent.
- **(F5)** Tribunal-modal-logic literature audit subsumes the contribution — Phase D.1 outcome is "subsumption"; Phase D.2 specialises rather than defines new class.
- **(F6)** Two simultaneous failures — fundamental redesign required; the platonic-ideal Lex paper acknowledges this risk in its introduction.

Each falsifier has a documented response. The roadmap survives any single falsifier and rebuilds against any pair.

---

## Cross-references

- **`PLATONIC-IDEAL.md`** — the converged conception of the target state.
- **`SUPREMUM.md`** — the current state.
- **`SUBSTRATE-INTERFACE.md`** — the proposed v1.0 interface contract.
- **`SUPREMUM-DISCIPLINE.md`** — the meta-principle.
- **`formal/README.md`** — current public proof status. The local target files and deliverables above specify this research programme.
- **`formal/coq/Lex/`** — the Rocq mechanization. Each Phase deliverable cross-references its Rocq target file.
