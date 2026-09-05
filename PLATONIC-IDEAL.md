# Lex: The Platonic-Ideal Conception

> **Companion to `SUPREMUM.md`.** `SUPREMUM.md` describes Lex *as it is*; this document describes Lex *as it ought to be*. The roadmap from one to the other is `ROADMAP.md`.

This document captures the converged vision of what the Lex paper, calculus, and substrate become at the supremum: the most complete, most verified, most load-bearing form Lex can take. Each section names a result the platonic-ideal Lex carries, the precondition that result rests on, the literature it adjoins, and whether the result is *proved*, *conjectured*, *open*, or *named-as-research-programme* in the current development. Honesty about that classification is part of what the supremum requires.

Convention: where we use the future tense ("Lex will carry…"), we describe a target the present development does not yet attain. Where we use the present tense ("Lex carries…"), the statement must be checked against its named source and the current status in `formal/README.md`. Present-tense descriptions of target interfaces do not establish shipped exports.

---

## 1. Substrate principle

Lex is the rule-logic substrate of a multi-paper, multi-layer system. Its role is not to be the most general logic of jurisdictional rules in the abstract, but to be the *unimpeachable substrate* on which the Op typed bytecode (companion paper *Op: A Typed Bytecode for Compliance-Carrying Operations*), the downstream institutional constructions, the sovereign-jurisdiction-network corridor protocol, and the intelligent-asset smart-asset VM all rest without conditional caveats.

Every design decision in Lex is judged against substrate strength along four axes:

1. **Compositional semantics.** Every Lex term has a semantic value computable locally; no downstream paper requires global flow analysis to quote a Lex property.
2. **Parametric stability.** Adding new tribunals, new defeasibility axes, or new effect operations does not break existing well-typed programs.
3. **Mechanized invariants.** Every property a downstream paper quotes is `Qed`-closed in the Rocq mechanization, or carries an explicit "conditional-on-Prop-spec" disclosure with the named premise.
4. **Explicit interface.** A proposed interface contract (`SUBSTRATE-INTERFACE.md`, target v1.0) specifies exactly what downstream papers may rely on. Lex versions evolve under that interface; Lex 2.0 follows downstream feedback rather than co-design.

Substrate strength is the load-bearing criterion. A choice that strengthens any axis is preferred over one that maximises an aesthetic or theoretical property.

---

## 2. Feature Integration Theorem

The platonic-ideal Lex centres on a single result:

> **Theorem (Feature Integration, conjectured and named as the central obligation).** The four typed primitives — defeasibility (priority graph + Heyting verdict lattice), temporal stratification (`Time_0` / `Time_1` + `lift_0` + `Toll`), tribunal modality (`[T] A` + `CanonBridge`), typed discretion holes (`?h : T @ authority scope S` + `PCAuth`) — compose in the Lex calculus without mutual interference. The integrated calculus admits unconditional preservation, progress, decidability of admissible-fragment type-checking, and the Curry-Howard reading of §5, with no feature appearing as a side condition on another's metatheorem.

Status: this theorem is *not* proved as stated. The current mechanization carries each feature's typing rules and the integrated `has_type` judgment, but preservation and progress for the full admissible fragment are open, decidability retains the full-calculus metatheory obligations summarized in `formal/README.md`, and the Curry-Howard reading is partial (Section 5 below). The theorem is named here because it is the load-bearing claim that downstream papers need: that Lex is *one calculus* with these four features, not four overlaid calculi with conditional behaviour at their joins.

The integration claim has three sub-obligations:

- **(IFi) Type-rule confluence.** No two feature-specific typing rules disagree on the type of a term that both can reach. Held by construction in the present grammar; would need an explicit non-overlap lemma if features were ever extended with overlapping eliminators.
- **(IFii) Reduction interleaving.** Reduction respects feature boundaries: defeasible-resolution does not interfere with `lift_0` direction, tribunal coercion does not violate Heyting verdict ordering, hole filling does not invalidate temporal non-regression. Each pairwise non-interference statement is currently an obligation, not a Qed.
- **(IFiii) Effect-row composition.** The effect rows of all four features compose into a single bounded semilattice with the empty row as unit, branch-sensitive markings preserved across feature-induced binders. The defeasible effect-join proposition (`defeasible_effect_join` in `PaperMechanization.v`) discharges one corner of this; the rest is a uniform claim that the bounded-semilattice structure is preserved by all binders introduced by the four features.

The platonic-ideal Lex paper centres its argumentative arc on the Feature Integration Theorem: motivate each feature legally (Section 2 of the paper, *What Kind of Law is Computable?*), define each feature formally (Sections 3 and 4), prove the integration theorem (the new central section), prove integrated metatheory (Section 5), demonstrate on worked examples (Section 7).

---

## 3. Lex Expressiveness Boundary Theorem

The platonic-ideal Lex is *honest about its limits as theorem*, not as prose. Section 2 of the proposed manuscript informally argues that Lex captures administrative-and-regulatory compliance rules but not constitutional reasoning, common-law principles, or jurisprudential questions about validity. The platonic-ideal version states this precisely:

> **Theorem (Lex Expressiveness Boundary, target statement).** For every legal rule `R = (input-types, output-type, evaluation-procedure)`, `R` is expressible as a closed Lex term iff:
> - **(EBi)** `R`'s evaluation procedure terminates on every well-typed input modulo typed holes;
> - **(EBii)** every non-mechanical step is annotated with a typed authority recognized in some tribunal of the bridge 2-category;
> - **(EBiii)** every authority annotation carries a witness that the supplied judgment satisfies a named decidable predicate on the input.
>
> The exclusion direction is a proposed obligation under the source-language and translation definitions below. It is not a proved classification of legal reasoning.

Status: open target, not an established characterization. Define a source rule language, observations, authority interfaces, and admissible translations first. Termination and authority annotations alone do not prove representability in the chosen Lex fragment. The forward construction must produce a typed term; the exclusion direction must give an obstruction relative to the fixed translation class.

The Boundary Theorem is what converts the §2 informal limit-discussion into theorematic precision. It also disciplines feature additions: any feature extension must preserve the boundary characterisation or else explicitly extend it with a corresponding conservativity statement.

---

## 4. The four primitives, refined

The four joint primitives are stable as listed in `SUPREMUM.md` §2. The platonic-ideal version refines each as follows.

### 4.1 Defeasibility

Status of the present formulation: *base-with-priority-list*, evaluated in the five-element Heyting verdict lattice `{NonCompliant < Pending < NotApplicable < Exempt < Compliant}`, with the priority-evaluator agreement `eval_sound` Qed-closed in `DefeasibilityPriority.v` and the verdict Heyting structure (thirteen laws) Qed-closed in `VerdictHeyting.v`.

Platonic-ideal refinement: *multi-axis defeasibility* (lex specialis × lex posterior × lex superior × jurisdiction), generalised from a single-DAG priority to a lattice/multi-axis structure. Two outcomes are equally welcome: (a) a *conservativity theorem* showing the multi-axis generalisation is conservative over the single-axis formulation on the common fragment, or (b) an *impossibility/separation theorem* showing the generalisation strictly extends the expressible space and naming a single-axis-inexpressible rule. Either outcome closes the question; punting is not platonic-ideal.

### 4.2 Temporal stratification

Status of the present formulation: two sorts (`Time_0`, `Time_1`) at universe level 0, total coercion `lift_0 : Time_0 → Time_1`, no inverse expressible in the grammar; `derive_1`, `Toll` (stacked), `EffectiveDate`, `Repeal`, embedded past/future temporal logic.

Platonic-ideal refinement: a precise *temporal non-interference theorem* in the Sabelfeld-Myers (2003) sense. Currently the temporal non-regression lemma states the structural invariant; the full non-interference theorem ("two well-typed terms differing only in their `Time_1` components produce identical `Time_0` observations under every well-typed context") is named as open in the paper's §11.12 and §13. The platonic-ideal version proves it.

### 4.3 Tribunal modality

Status: `PaperMechanization.v` closes bridge composition and identity laws for its specified model. `BridgeSemantics.v` also closes `function_bridge_strict_2functor_coherence` for strict function bridges. Proof-relevant provenance, certificate admission, and general modal completeness require separate statements and proofs. The strict result does not certify every target bridge model.

Platonic-ideal refinement: a *new class of 2-modal logics over bridge 2-categories*, defined precisely, with soundness and completeness theorems against a Kripke-style accessibility-through-bridge semantics. This is Section 7 below. The literature audit it requires (Mac Lane–Moerdijk on topos-internal modal logic, Awodey on modal HoTT, Reyes on functorial semantics of higher-order modal logic, Pfenning–Davies for judgmental S4, Nanevski–Pfenning–Pientka for contextual modal type theory) is itself a research project of months in the platonic-ideal execution.

### 4.4 Typed discretion holes

Status of the present formulation: `?h : T @ authority scope S` carrying a `PCAuth(authority, h)` witness on `fill(h, e, w)`, with multi-signer quorum, revocation metadata, linked timestamp anchoring, and bounded delegation. The hole-filling rule discharges the `discretion(authority)` effect; the filled term is pure modulo the filler's effect row.

Platonic-ideal refinement: *typed discretion holes are the load-bearing novelty* of Lex relative to all prior compliance languages and become the *completed Curry-Howard correspondence* — see Section 5 below. They also carry a richer lifecycle: speech-act-with-audit semantics for the fill, typed retraction propagation under appellate overrule, and fill-level reasons. The proposed manuscript §13.9 names this as research; the platonic-ideal version delivers the static-typing-plus-dynamic-lifecycle account in one paper, or splits it explicitly into two with both shipped together.

---

## 5. Curry-Howard for typed discretion holes

The programme seeks a Curry-Howard reading first on a precisely defined recursion-free fragment over finite enumerations, then on the full target. The platonic-ideal Lex completes the correspondence on its most distinctive primitive: typed discretion holes.

> **Correspondence (Discretion-Hole Curry-Howard, target).** A typed discretion hole `?h : T @ authority(auth) scope(S)` corresponds to a *control-operator-like term in a co-classical fragment of the type theory* whose inhabitant is exactly a PCAuth witness. The `fill(h, e, w)` rule is the *control-operator activation*: the witness `w : PCAuth(auth, h)` discharges the classical-style assumption "this proposition holds because a recognised authority asserts it," and the resulting term inhabits the proposition `phi_h(value) ∧ authorized(h, signer) ∧ temporally-admissible(audit)` constructively, by attestation rather than by mechanical derivation.

Position against the literature:

- **Murthy 1991** (classical computation) and **Griffin 1990** (call/cc as classical logic) supply the original control-operator-as-classical-logic correspondence; PCAuth-as-attestation is a conservative extension that replaces the call/cc continuation grab with a dependent-record proof of authority.
- **Krivine** and **Miquel** (realizability for classical proofs) supply the realizability content: a realizer of `[T] A` is a tribunal-indexed recursive procedure that, on demand, produces either a derivation of `A` or a PCAuth witness binding the attestation to a recognised authority.
- **Kohlenbach** (proof mining) supplies the framework for extracting computational content from attestation-style witnessing.
- **Pfenning–Davies 2001** (judgmental S4) and **Nanevski–Pfenning–Pientka 2008** (contextual modal type theory) supply the modal-context machinery for indexing the propositions an attestation can inhabit.

The completed correspondence has four distinguishable Curry-Howard correspondences in Lex, of which discretion-hole-as-attestation is the centerpiece:

| Feature | Type-theoretic correspondence | Status |
|---|---|---|
| Discretion holes | Co-classical / proof-by-attestation | Centerpiece, target full correspondence |
| Defeasibility | Exception-handling-as-types (CBPV / Levy 1999, Filinski 1994) | Compatible-conjectured |
| Temporal stratification | Modal type theory (Pfenning–Davies) extended to multi-sort time | Compatible-conjectured |
| Tribunal modality | Multi-modal MTT (Gratzer–Kavvos–Nuyts–Birkedal 2020) | Compatible-conjectured |

The platonic-ideal Lex fully mechanises the discretion-hole correspondence and provides explicit conjectures-with-evidence for the other three, each pointing at the precise type-theoretic tradition the full correspondence would adopt.

---

## 6. Position theorems framework

The position programme compares Lex with Catala, L4, and defeasible logic through explicit translations and counterexamples. The source-language versions below are proposed freeze labels, not verified release pins. Resolve each to a public specification and immutable implementation revision before stating a theorem. Each comparison must name its observations and permissible translations, then provide a robustness analysis.

> **Theorem (Catala embedding and separation, target).**
> Let `Catala-2024` denote the frozen Catala semantics as published in Merigoux, Chataing, Protzenko (ICFP 2021) plus the publicly-specified extensions of the Catala-2024 implementation. There is a translation `T : Catala-2024 → Lex` such that for every Catala-2024 program `P` and every well-typed input `i`, `P(i)` and `T(P)(i)` produce the same verdict under the common-fragment semantics. Conversely, there exists a Lex program `Q` (candidate: a program whose authority or bridge observations the fixed target interface cannot preserve) such that no Catala-2024 program `P'` within a specified structure-preserving translation class reproduces `Q` under the same authority interface and observations. Defining that class and a separation witness is part of the obligation; arbitrary computable preprocessing is too broad for the proposed claim.

> **Theorem (Governatori-Antoniou faithful encoding and separation, target).**
> Let `DDL-2004` denote the defeasible-logic framework of Governatori, Antoniou, Maher, Billington (AAAI 2000) plus the parameterized-superiority extension of Governatori 2005. There is an embedding `E : DDL-2004 → Lex` such that for every DDL-2004 rule set `R` and every fact base `F`, the conclusions derivable in DDL-2004 from `R, F` coincide with the conclusions derivable in Lex from `E(R), F` under the priority-graph + Heyting-verdict-lattice semantics. Investigate separation for typed discretion holes under a fixed observation and translation contract. Untyped syntax alone does not rule out an encoding.

> **Theorem (L4 translation in one direction, target).**
> Let `L4-CCLAW-2022` denote the L4 specification of Lim et al. (2021) in the CCLAW core fragment as of 2022. There is a translation `U : L4-CCLAW-2022 → Lex` for the regulatory-compliance fragment of L4 (the fragment that encodes statutory rules, excluding the deontic-contract fragment for bilateral obligations). For the contract fragment, define its deontic observations and seek an encoding or an explicit obstruction within the stated translation class. Missing surface operators alone do not prove inexpressibility.

Each theorem includes a *Robustness* subsection naming what would invalidate it: "if Catala-2025 introduces typed exceptions matching `PCAuth`-witnessed discretion holes, the separation direction degrades to equivalence on the extended common fragment"; "if DDL is extended with type discipline beyond superiority parameterization, the embedding may need to be revised to preserve faithfulness"; etc. Robustness analyses are part of the theorem statements, not afterthoughts.

---

## 7. Tribunal-modal logic class

The platonic-ideal Lex defines a new class of modal logics — *2-modal logics over bridge 2-categories* — and proves soundness and completeness for that class.

The motivation: tribunal modals in Lex are not a standard modal operator. They are a 2-functor from a bridge 2-category (objects: tribunals; 1-cells: recognition bridges; 2-cells: coherence witnesses) into the semantic universe (Type or a Heyting algebra). Standard modal logic frames are 1-categorical (a Kripke frame is a set with a binary accessibility relation, i.e. a category whose objects are worlds and whose morphisms are the accessibility instances); they do not capture the 2-cell structure that records when two recognition bridges agree on a coherent reading of an underlying proposition.

> **Definition (target).** A *2-modal logic over a bridge 2-category* `B` is given by:
> - A 2-category `B` with finite limits.
> - A 2-functor `M : B → Cat` (or, for a propositional fragment, `M : B → Heyt`, the 2-category of Heyting algebras).
> - Modal operators `[T]_B : Prop → Prop` for each tribunal-object `T ∈ Ob(B)`, satisfying the bridge naturality: for every recognition 1-cell `b : T₁ → T₂` and every proposition `A`, there is a coherent natural transformation `coerce[b] : [T₁] A → [T₂] A`.
> - 2-cell coherence: for every pair of recognition 1-cells `b, b' : T₁ → T₂` and every 2-cell `α : b ⇒ b'` in `B`, the natural transformations `coerce[b]` and `coerce[b']` are related by a coherent isomorphism arising from `M(α)`.

> **Theorem (target).** The 2-modal logic of Lex (with `B` the bridge 2-category and `M` the presheaf-topos interpretation of §10 of the paper) is sound and complete with respect to the Lex term-level tribunal-modal calculus. Soundness: every derivation in the term calculus interprets to a valid proof in the 2-modal logic. Completeness: every valid proof in the 2-modal logic can be reflected back to a term-calculus derivation.

The literature audit obligation (named in Section 4.3 above) is a precondition for stating this Definition with full precision. The audit's outcome may be one of three:

- **Subsumption.** An existing class (e.g., Awodey's modal HoTT or Mac Lane–Moerdijk topos-internal modal logic) already contains the 2-modal-over-bridge-2-category structure as a fragment; in that case Lex's tribunal modal is positioned as an instance and the soundness/completeness theorems are inherited or specialised.
- **Conservative extension.** An existing class is a 1-categorical projection; the 2-modal version is a genuine extension. Define the new class precisely; prove soundness and completeness for it.
- **Independence.** No existing class fits; define the new class entirely from scratch with explicit proof-theoretic motivation. Prove soundness and completeness without inheriting from prior work.

The platonic-ideal Lex commits to whichever outcome the audit produces, with explicit positioning either way.

---

## 8. Categorical and denotational completion

The categorical programme proposes a Category with Families interpretation with Lex-specific extensions, followed by an authority-indexed presheaf model. Adequacy and full abstraction require exact operational observations and a semantics that accounts for proof-relevant authority evidence. This document does not establish an impossibility theorem for all Set-valued presheaf interpretations.

Platonic-ideal refinements:

- **Soundness and adequacy mechanised.** Adequacy is an open target requiring its precise source calculus and interpretation. The platonic-ideal version `Qed`-closes this in Rocq for the full admissible fragment, with each per-constructor case (the six Lex-specific cases in addition to the standard CwF cases) discharged by its own proof.
- **Full abstraction explicitly NOT claimed; what is needed instead is named.** The platonic-ideal Lex paper's §10 ends with a precise statement of the obstruction to full abstraction (proof-relevant operational artifacts) and points at game semantics over certificate traces as the technical-content target. Full abstraction is an open conjecture, not a deferred theorem.
- **Cut elimination as conditional conjecture.** The proposed manuscript's §10 already reframes cut elimination as a conjecture conditional on the open subject-reduction conjecture and the open SN-admissible conjecture (open target). The platonic-ideal version retains this framing precisely, and lists cut elimination as the natural next paper-length development once SN-admissible closes.
- **Proof-carrying interpreter as artifact.** The platonic-ideal Lex includes a Coq-extracted interpreter that, on every input rule pack + facts, produces both the answer AND a machine-checkable proof of the derivation. Position relative to CompCert (Leroy 2009): CompCert verifies the compilation; the proof-carrying interpreter additionally produces a per-execution proof certificate. Position relative to proof-carrying code (Necula 1997): PCC produces a safety proof for an executable; the proof-carrying interpreter produces a *derivation* proof for a verdict.

---

## 9. Substrate interface

The Substrate Interface is a proposed contract for Op and other consumers. `SUBSTRATE-INTERFACE.md` is not frozen. Versioned guarantees require discharged proof obligations, a concrete export surface, and consumer review. The target relationship is versioned:

- **Lex 1.0 ships first** with the full integrated calculus, its admissible fragment, the Substrate Interface v1.0 specification, and (per the Mechanization Commitment of Section 10 below) the 100% Qed-closed metatheory.
- **Op 1.0 ships against Lex Substrate Interface v1.0** — Op's typing rules quote Lex's interface guarantees, never Lex's internal representations.
- **A breaking change to the frozen substrate contract requires a new major interface version.** Lex 2.0 introduces a new interface version, never silently revises v1.0.

This versioning replaces co-authorship coupling. Lex paper development can complete without waiting for Op paper development. The risk: if Lex 1.0's interface choice turns out to under-serve Op, Lex 2.0 is needed and the paper has to be revised. The platonic-ideal Lex paper explicitly acknowledges this risk in its introduction.

---

## 10. Mechanization commitment

Current proof status is recorded in `formal/README.md` and the named Rocq declarations. A `Qed` ending proves its stated implication; it does not discharge that implication's hypotheses. Administrative WHNF bounds are closed. Full-calculus normalization, substitution, confluence, preservation, match coverage, and the resulting unconditional type-safety claims retain separate obligations. The target remains closure of every theorem claimed by the completed calculus.

The completed artifact must support each unconditional theorem with a closed proof. Conjectures and conditional results remain explicitly classified while work continues. Recording a premise or counterexample completes a bounded investigation, not the stronger theorem objective.

The path:

1. **Defect 1 closure first.** The parallel multi-substitution primitive (`parallel_subst : list Term → Term → Term`) in `formal/coq/Lex/DeBruijn.v` with the appropriate shift-commutation lemmas, or prove the existing fold correct under the exact at-depth substitution specification. `Confluence.v` supplies `par_subst_args_spec` and a fold/scoping bridge from `par_subst_at_depth_spec`; that stronger premise remains open. Closing the relevant shift-compatibility obligation is required for `weakening_property` unconditionally (currently `weakening_at_fix` is `Qed` conditional on `conv_eq_shift_compat_spec`). The proposed substitution investigation retains this candidate counter-witness for reproduction against the exact historical reduction rule: `args = [v_0; v_5]`, `body = v_0`, outer cutoff `c = 0`, shift amount `d = 1`; layered reduct yields `v_6` while shift-then-fire yields `v_0`.
2. **`whnf_bounded_reduction` closure second.** The administrative fragment already has explicit, Qed-closed WHNF bounds in `PaperMechanization.v`. Extend the argument to the actual full admissible calculus and discharge the other metatheory premises before claiming unconditional decidability.
3. **Confluence closure third.** `par_diamond_spec` is named as a Prop but not Qed; the Tait-Martin-Löf parallel-reduction infrastructure (`par`, `par_branch`, `par_exception` mutual inductives plus the bidirectional `step_implies_par` / `par_implies_steps` bridges, all already Qed in `Confluence.v`) is in place. The diamond-lemma proof completes the chain.
4. **Preservation and progress for the full admissible fragment.** Currently progress is Qed conditional on `confluence_property` and `match_exhaustiveness_property`. Once confluence closes, progress becomes unconditional on confluence; match exhaustiveness is a separate obligation (tighten the typing rule to enforce branch coverage, then progress closes outright).
5. **Cut elimination, full abstraction, multi-axis defeasibility.** Either prove or preserve as honest conjecture with proof strategy.

Each closure step has a named target file in `formal/coq/Lex/`. The platonic-ideal Lex's mechanization is a multi-year programme; `ROADMAP.md` enumerates the phases.

---

## 11. Open programme refined

The proposed manuscript's §13 enumerates eleven open problems; the platonic-ideal version refines each into the form: PROBLEM, ORIGIN (year first stated), FORMAL STATEMENT, CURRENT BEST PARTIAL RESULT (with citation), CONJECTURED COMPLEXITY OR STATUS, PROPOSED ATTACK, WHY IT MATTERS FOR LEX.

The eleven survive as the genuine research programme Lex opens. They are summarised here; the full refined catalogue is the §13 of the platonic-ideal paper.

| # | Problem | Programme owner |
|---|---|---|
| 13.1 | Bounded legal first-order quantification — full extension with Presburger decision procedures for common predicate shapes | Lex paper §13.1 + decision-procedure literature |
| 13.2 | Curry-Howard for the full calculus (recursion-bearing, modal) | Resolved partially by Section 5 of this document; full closure remains open |
| 13.3 | Logical relations and parametricity | Reynolds 1983, Wadler 1989, Bernardy–Coquand–Jansson 2010 |
| 13.4 | Prop-sort discipline and proof irrelevance | Werner 1997 baseline; explicit Lex treatment open |
| 13.5 | Higher-dimensional equality (HoTT/cubical) | Awodey, cubical type theory community |
| 13.6 | Modal soundness and completeness for tribunal bridges | Resolved by Section 7 of this document if literature audit succeeds |
| 13.7 | Denotational semantics and full abstraction | Section 8 of this document; full abstraction remains open |
| 13.8 | Full-fragment metatheory beyond the admissible core | Section 10 of this document; multi-year mechanization |
| 13.9 | Discretion-hole lifecycle (speech-act-with-audit, retraction propagation, fill-level reasons) | Austin/Searle for speech-act, separate research programme |
| 13.10 | LTL/CTL/TCTL for rule composition at workflow scale | Op companion paper |
| 13.11 | Conflict resolution for equal-authority hole fills | Open programme; partial-order on authority certificates + repair protocol |

---

## 12. Falsifiers

The platonic-ideal plan is wrong if any of the following hold:

- **(F1) Integration theorem fails.** One feature interferes with another; the integrated calculus cannot carry preservation/progress without per-feature side conditions. In that case the plan rebuilds: either the four features must be sequenced (one introduced at a time with a conservativity proof at each step) or one feature must be relaxed.
- **(F2) Discretion-hole Curry-Howard correspondence has structural obstruction.** PCAuth quorum cannot be encoded as a control-operator-like term; co-classical fragment is incompatible with the dependent-record proof-of-authority shape. In that case, temporal stratification becomes the completed Curry-Howard correspondence (Pfenning–Davies extended to multi-sort time), and discretion-hole CH is demoted to compatible-conjectured.
- **(F3) Catala-2025+ becomes more expressive than estimated.** Catala introduces typed exceptions matching `PCAuth`-witnessed discretion holes, or typed authority indexing matching tribunal modals. In that case the position theorems become equivalence-on-extended-fragment rather than strict-extension.
- **(F4) Full-fragment metatheory has barrier.** Decidability of type-checking is provable for the full calculus only by reducing to Presburger arithmetic plus an undecidable extension, or strong normalization fails for some genuine subset of the dependent fragment. In that case the admissible-fragment framing becomes permanent rather than temporary.
- **(F5) Tribunal-modal-logic literature audit subsumes the contribution.** An existing class (Awodey's modal HoTT, Mac Lane–Moerdijk topos-internal modal logic, or another) already contains the 2-modal-over-bridge-2-category structure. In that case the contribution is positioned as instance/specialisation rather than new class definition.
- **(F6) Two simultaneous failures from the above.** If two falsifiers fire at once (e.g. F1 + F2, or F2 + F4), the plan requires fundamental redesign rather than parameter tuning. The platonic-ideal Lex paper acknowledges this risk explicitly in its introduction.

Falsifiers are part of the platonic-ideal commitment because honesty about what would invalidate the plan is the precondition for any sound research strategy. The plan that names no falsifiers is the plan that cannot be wrong, which is the plan that is not actually a plan.

---

## 13. Research review criterion

Review the plan against exact theorem statements, counterexamples, executable boundaries, and dependencies. A stable plan is not evidence that its theorems are proved. Record unresolved obligations and the next discriminating proof or experiment. Completion requires the deliverables in `ROADMAP.md`, not a fixed number of review rounds.

---

## 14. Cross-references

- **`SUPREMUM.md`** — architecture and evidence boundaries; executable claims defer to the language reference and named sources.
- **`ROADMAP.md`** — the game plan: the phases, dependencies, and per-phase deliverables that take Lex from current state to the platonic-ideal.
- **`SUBSTRATE-INTERFACE.md`** — the proposed v1.0 interface contract for Op and downstream consumers.
- **`SUPREMUM-DISCIPLINE.md`** — the meta-principle (always pick the supremum option) under which all of the above operate.
- **`formal/README.md`** — current public proof status and local mechanization routes. The research programme retains the full paper-level objectives described here.
- **`formal/coq/Lex/`** — the Rocq mechanization. Each Section of this document cross-references its Rocq target file where applicable.
