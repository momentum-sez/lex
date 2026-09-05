# Lex: Authoritative Design

> This document separates implemented architecture from the full research target. The companion documents describe the platonic-ideal target and the path to it:
>
> - **`PLATONIC-IDEAL.md`** — the converged conception: substrate principle, Feature Integration Theorem, Lex Expressiveness Boundary Theorem, Curry-Howard for typed discretion holes, position theorems framework, tribunal-modal logic class, categorical/denotational completion, mechanization 100% commitment, falsifiers, convergence criterion.
> - **`ROADMAP.md`** — the game plan: Phases A–H with logical dependencies, per-phase deliverables, convergence criterion.
> - **`SUBSTRATE-INTERFACE.md`** — the proposed v1.0 interface contract for Op and downstream consumers (currently draft v0.1, proposed for freeze at `ROADMAP.md` Phase E after its prerequisite proofs and consumer review).
> - **`SUPREMUM-DISCIPLINE.md`** — the meta-principle (always pick the supremum option) under which all of the above operate.

## 1. What Lex is

Lex is a dependently typed rule language for jurisdictional compliance. The executable admissible checker, frontier core calculus, and Rocq developments have distinct guarantees. This document records their architecture and research targets. `docs/language-reference.md` governs the executable boundary; `formal/README.md` governs current proof-status navigation. Full proof-producing evaluation of the integrated calculus remains a target.

Four grammar features are primitive, not encoded: defeasible rules with explicit numeric priority, two temporal sorts with a directional coercion between them, tribunal modals indexing propositions by the authority that asserts them, and typed discretion holes marking the boundary at which machine derivation halts and a named authority must decide. No prior compliance language carries all four as primitives of a single calculus.

The calculus is the substrate on which autonomous compliance evaluation knows its own limits. The machine reduces the rule as far as the type system permits and halts at a typed hole that specifies the type of judgment required, the authority entitled to supply it, and the scope in which the judgment applies. The filled term enters the derivation trace with a cryptographic authorization witness; downstream auditors receive a proof term that exposes the mechanical fragment and the discretionary fragment as independently inspectable.

## 2. Four joint primitives

### Defeasibility with explicit priority

A defeasible rule has a base body and a list of exceptions, each carrying a guard, a body, and a numeric priority. The typing rule requires every exception body to inhabit the same type as the base body; the priority is a natural-number literal, not a participant in the typing derivation. Evaluation resolves defeasibility by scanning exception guards in descending priority order. The highest-priority satisfied exception determines the outcome; if no exception fires, the base body produces the verdict. This separates *lex specialis derogat legi generali* from control flow. The Governatori–Prakken–Sartor defeasible-logic programs in the legal-AI tradition lack this typing constraint: a rule may defeat any other rule, even one with a different semantic domain.

### Temporal stratification

Two sorts at universe level 0 are distinguished: `Time_0`, the time at which a transition was committed, and `Time_1`, the time produced by a legal rewrite. The coercion `lift_0 : Time_0 → Time_1` is total. No term demotes `Time_1` to `Time_0`; the constructor does not appear in the grammar. Retroactive rule change regenerates `Time_1`-indexed consequences from the unchanged `Time_0` record. This encodes the legal invariant that amendments change the *consequences* of past events, not the *occurrence* of past events. Retroactive invalidations of the Schrems-II class are handled by re-evaluation under a new rule set against an unchanged historical record; the stratification guarantees the input is fixed and the output is recomputable.

### Tribunal-indexed modality `[T] A`

Propositions are indexed by the authority that asserts them. `[T] A` asserts proposition `A` holds under tribunal `T`. The elimination rule `coerce[T1 => T2](e, w) : [T2] A` requires an explicit `CanonBridge(T1, T2, A)` witness: a term proving the two authorities agree on the relevant interpretation. No implicit aggregation operates over tribunals; tribunals are not ordered. Divergence between authorities is represented as an explicit obstruction: a bridge witness may fail to exist, in which case the coercion is ill-typed and the disagreement becomes first-class type-theoretic content. Mutual recognition agreements are precisely bridge witnesses attested by both authorities.

### Typed discretion holes `?h : T @ authority scope(S)`

A hole is a placeholder for human judgment with three named fields: a type `T` (the value the filler must supply), an authority (the principal entitled to fill it), and an optional scope (a constraint on jurisdiction, entity class, time window, or corridor). A hole has type `T` and produces the `discretion(authority)` effect. The hole is filled by `fill(h, e, w)` whose witness `w : PCAuth(authority, h)` is a proof-carrying authorization record. Once filled, the `discretion` effect is discharged; the result is pure. No existing system typings this boundary: Catala authors supply a value when the law requires judgment and the distinction vanishes at compile time; Rego and Datalog have no language-level construct for it; LegalRuleML is an interchange schema with no execution semantics; encodings in Isabelle/HOL push the typing discipline to the user.

## 3. Core calculus

Lex is a dependent type theory with a cumulative universe hierarchy `Type_l` (l = 0, 1, 2, …), a proof-irrelevant sort `Prop` at `Type_1`, a normative sort `Rule_l` parallel to `Type_l`, and the temporal sorts `Time_0` and `Time_1` at `Type_0`. Universe levels are expressions built from natural-number literals, level variables, successor, and maximum, with a finite large bound on absolute level values preventing numeric overflow.

The typing judgment is `Γ ⊢ e : T ! E`, where `Γ` is the context, `T` is the result type, and `E` is the effect row. Effects are drawn from the vocabulary `{read, write(scope), attest(authority), authority(ref), oracle(ref), fuel(level, amount), sanctions_query, discretion(authority)}` and form a bounded semilattice under join with the empty row as unit. A branch-sensitive wrapper marks effect rows whose join would raise the privilege level; these require an explicit `unlock` eliminator, preventing privilege creep through branch composition.

The typing rules cover:

- **Var** — de Bruijn index lookup against the context.
- **Const** — constant reference against the prelude signature.
- **App** — `Γ ⊢ f : Π(x:A).B` and `Γ ⊢ a : A` yields `Γ ⊢ f a : B[a/x]`.
- **Lambda** — `Γ, x:A ⊢ b : B` yields `Γ ⊢ λ(x:A).b : Π(x:A).B`. Every binder carries an explicit domain annotation; there are no implicit arguments in core form.
- **Let** — `Γ ⊢ e : A` and `Γ, x:A ⊢ b : B` yields `Γ ⊢ let x:A := e in b : B[e/x]`.
- **Match** — branch-exhaustive case analysis against an inductive scrutinee with every branch returning the same annotated result type.
- **Defeasible** — `Γ ⊢ b : A`, every exception body inhabits `A`, yields the same `A`.
- **Sort** — each sort inhabits the next universe level; Prop inhabits Type_1; Time_i inhabits Type_0.
- **TemporalIntro** (`lift_0`) — `Γ ⊢ t : Time_0` yields `Γ ⊢ lift_0(t) : Time_1`. `derive_1(t, w)` with a rewrite witness `w` also yields `Time_1`. No reverse.
- **TribunalIntro** — `Γ ⊢ A : Prop` yields `Γ ⊢ [T] A : Prop` for tribunal `T`.
- **TribunalElim** — `Γ ⊢ e : [T1] A` and `Γ ⊢ w : CanonBridge(T1, T2, A)` yields `Γ ⊢ coerce[T1 => T2](e, w) : [T2] A`.
- **Hole** — `?h : T @ authority(auth) scope(S)` has type `T` with effect row `{discretion(auth)}`.
- **Fill** — `Γ ⊢ e : A` and `Γ ⊢ w : PCAuth(auth, h)` yields `Γ ⊢ fill(h, e, w) : A` with the filler’s effect row `ρ`; only the enclosing discretion effect is discharged.
- **Effect-Weaken** — `Γ ⊢ e : A ! ρ1` and `ρ1 ⊆ ρ2` yields `Γ ⊢ e : A ! ρ2`.
- **Sanctions-Dominance** — `Γ ⊢ p : SanctionsNonCompliant(entity)` yields `Γ ⊢ sanctions-dominance(p) : ⊥`. The bottom type absorbs all eliminators. No tribunal coercion, defeasibility exception, or discretion hole rescues a sanctions-non-compliance proof.

Evaluation is bidirectional type-checking against a `Context` drawn from the prelude signature plus bounded weak-head-normal-form reduction under a fuel counter with a finite substitution size limit. The type checker performs this reduction and structural comparison at each step. Definitional equality reduces to WHNF under finite fuel; the fuel counter's exhaustion yields the verdict `Indeterminate`, which is a proper outcome of the calculus rather than a timeout exception.

## 4. Admissible fragment

The executable checker admits a restricted fragment and rejects unsupported syntax. Rejection of modal forms or unfilled holes does not establish their undecidability or nontermination. Unrestricted recursion can prevent normalization. Full-calculus decidability requires precise syntax, reduction, and typing hypotheses that remain research obligations.

A term is admissible when it satisfies five positive clauses:

1. **First-order data.** Variables, constants, lambda abstractions with annotated domains, applications, let-bindings, type annotations, and pattern matching on prelude-provided inductive types.
2. **No modal forms.** Temporal modals `@t A`, `◇t A`, `□[t1,t2] A`, the temporal coercions `lift_0` and `derive_1`, and the tribunal modals `[T] A`, `coerce[T1 => T2]` are excluded. This is a boundary of the executable admissibility predicate, not an impossibility theorem for every modal extension.
3. **No unfilled holes.** A `Hole` produces the `discretion(auth)` effect, which cannot be discharged without a `PCAuth` witness. Admitting an extension requires an explicit residual-effect and authority-verification contract; an unfilled hole alone does not prove nontermination.
4. **Decidable-exhaustiveness match.** Every match scrutinee has an inductive type whose constructor set is known at admissibility-check time. The compliance-prelude types (`ComplianceVerdict`, `Bool`, `Nat`, `SanctionsResult`, `ComplianceTag`) satisfy this condition, which is why the practical rule suites fall inside the admissible fragment.
5. **No structural recursion.** The recursion form `fix f : A := b` permits non-terminating reduction and is excluded.

Sigma types, content-addressed references, principle-balancing, and the `unlock` eliminator are also excluded.

The admissibility predicate is decidable: the check is a structural traversal that returns either `admissible t` or `¬ admissible t` for every term `t`. The Rocq mechanization establishes this decidability as an inductive relation on the core AST.

Oracle-effect admissibility requires attestation. An oracle query carries an `OracleRef` naming the external resolver and a depth bound constraining the number of nested oracle queries the resolver may itself emit. An `oracle(ref)` effect is admissible when the referenced oracle is registered in the signature, the depth bound is a natural-number literal, and the attestation witness accompanies the query. The boundedness of nested oracle resolution prevents admissibility from reducing to a non-terminating oracle-query chain; the depth bound is a mechanical termination argument at the oracle boundary.

## 5. Mechanization status

The Rocq 9.1.1 mechanization in `formal/coq/FlatAdmissibleSN.v` establishes strong normalization of the flat admissible fragment extended with affine lambdas under call-by-value β and defeasible rules with non-empty exception lists. The principal theorem is:

```
Theorem flat_admissible_sn_ext : forall t, SN t.
```

`Print Assumptions flat_admissible_sn_ext.` reports `Closed under the global context`. The proof uses no axioms beyond the standard library's inductive and well-foundedness constructions. The same closure report holds for `flat_admissible_sn`, `step_decreases_size`, `subst_size`, and `subst_size_affine`.

The proof proceeds by a well-founded size measure `μ : FAdm → ℕ`. The key ingredient is the substitution identity

```
|t[u/k]| + occ(t, k) = |t| + occ(t, k) · |u|
```

and its affine corollary: when `occ(body, 0) ≤ 1`, substitution yields `|body[v/0]| ≤ |body| + |v| − 1`. Each of the ten reduction rules — ζ, μ-v, δ-0, δ-k, β, and the five congruences ξ-let, ξ-mat, ξ-def, ξ-app-l, ξ-app-r — strictly decreases the size measure. Well-foundedness of `<` on ℕ and measure-decreasing lifting conclude SN.

The flat result applies to terms in its own inductive fragment. Establish a translation and membership witness before applying it to a rule example or executable evaluation.

Current proof status is recorded in `formal/README.md` and the named Rocq declarations. A `Qed` ending proves its stated implication; it does not discharge that implication's hypotheses. Administrative WHNF bounds are closed. Full-calculus normalization, substitution, confluence, preservation, match coverage, and the resulting unconditional type-safety claims retain separate obligations. The flat calculus proves a size-decreasing reduction bound. Applying that bound to the Rust evaluator requires a semantics-preserving correspondence and cost model; this document does not claim that bridge is proved.

## 6. Fill and PCAuth

The conceptual proof-carrying authorization target has the following schematic record. Concrete wire formats and verified payload bindings are defined by their implemented interfaces:

```
PCAuth(auth, h) = {
  signer    : Did,
  role      : AuthorityRole(auth),
  scope_ok  : ScopeWitness(h.scope),
  timestamp : Time_0,
  signature : Ed25519Sig(signer, h, value)
}
```

The schematic record describes the target authority binding. A deployment must establish credential issuance, scope, time, payload binding, and cryptographic verification under an explicit threat model. The schematic signature field alone does not establish those guarantees.

The Fill rule flow-through preserves the filler's effect row. If the filler `e` carries effect row `ρ` at the Fill site, the effect row of `fill(h, e, w)` is `ρ` — the filler's effects propagate unchanged while the hole's own `discretion(auth)` effect is discharged. Admissibility of a filled term requires `ρ = ∅` post-substitution: a filler carrying its own unfilled holes or oracle queries is outside the admissible fragment even when the enclosing hole is filled.

Signature verification belongs at the admission boundary and is supplied through `PCAuthVerifier` in `crates/lex-core/src/core_calculus/hole.rs`. The structural precheck checks structure only. The built-in HMAC verifier uses a symmetric secret; it is not public-key signature verification. That module does not provide an asymmetric Ed25519 or hybrid-PQ verifier. A deployment claiming asymmetric admission must supply and validate one. The ordinary admissible checker still rejects surface hole fills; the residualized extension does not turn structural evidence into verified authority.

## 7. Temporal stratification

`Time_0` records frozen historical event time. `Time_1` records derived legal time. `lift_0 : Time_0 → Time_1` is total and one-way: every frozen fact can produce a derived consequence. The grammar has no constructor that demotes `Time_1` to `Time_0`. Any term that would require such demotion fails to parse, and any term that applies `lift_0` to a `Time_1` argument is rejected by `temporal::check_temporal_stratification` with the diagnostic "there is no coercion from Time_1 to Time_0."

Retroactive rule change regenerates `Time_1` consequences from unchanged `Time_0` record. The paradigm is the *Schrems II* decision (Court of Justice of the European Union, C-311/18): an entity that relied on Privacy Shield as its legal basis for a data-transfer verdict at one `Time_1` could, the following week, be evaluated against a rule framework in which Privacy Shield never provided a valid basis at that same `Time_1`. The `Time_0` observation — when the transfer occurred — does not change. The `Time_1` verdict — what the law says about the transfer under the currently-operative framework — is regenerated by re-running the rules against the unchanged `Time_0` record under the new pack version. The asof-indexing of every verdict records which framework produced it at what event time, so every verdict remains auditable across regulatory discontinuities.

## 8. Tribunal modality

`[T] A` indexes a proposition `A` by the tribunal `T` asserting it. Two tribunals may assert contradictory propositions about the same facts. The Tribunal-Elim rule requires an explicit `CanonBridge(T1, T2, A)` witness: a term proving the two tribunals agree on the proposition. No implicit aggregation operates over tribunals — there is no join, no voting, no FATF-member precedence, no hierarchy. Any aggregation scheme would encode a political judgment about which authority matters more, which the logic refuses to encode.

Mutual recognition agreements are logical objects of the calculus. Each is a `CanonBridge` witness attested by both tribunals, inhabiting the type `CanonBridge(T1, T2, A)` for a specific proposition `A`. The inhabitation of this type is an institutional fact about bilateral agreement, not a property the logic derives. When two tribunals disagree and no bridge witness exists, the disagreement is first-class type-theoretic content: a term typeable only under one tribunal cannot be coerced to the other, and an agent reasoning across both surfaces the divergence as an obstruction rather than silently selecting a winner. Cross-harbor aggregation at the compliance-tensor level operates on the verdicts that tribunals produce (the pointwise meet of those tensors), not on the tribunals themselves.

## 9. Implementation and repo state

The workspace members in `Cargo.toml` are `lex-core`, `lex-cli`, `lex-diag`, `lex-pack`, and `mez-canonical`. They provide the calculus implementation, command-line interface, diagnostics, pack operations, and in-tree canonical primitives. Public builds use the in-tree canonical crate.

The toolchain is pinned by `rust-toolchain.toml`. Run the affected checks and `cargo test --workspace` to establish current executable evidence. Test totals depend on the checked revision and are not a proof of full-calculus correctness.

`REPRODUCIBILITY.md` records the supported build procedure. Public compilation must remain independent of private sibling checkouts. Release publication and tag creation require separate authority.

## 10. Prior-art comparison programme

The following comparisons motivate investigation. They are not exhaustive capability or separation theorems. Pin each external specification and implementation revision, and verify the claimed differences before publication.

**Catala** (Merigoux, Chataing, Protzenko, ICFP 2021) compiles French tax law via a default calculus. Defeasibility is first-class. Types are ML-family without dependence; no multiple-authority model; no language-level machine-vs-judgment boundary — when the law requires judgment, the author supplies a value and the distinction vanishes at compile time.

**L4** (CCLAW, Singapore) is a deontic-logic DSL for contracts, targeting bilateral obligation/permission/prohibition. Contracts are voluntary; regulations are unilateral. L4 lacks dependent types, temporal-sort distinction, and the typed discretion hole.

**LegalRuleML** (OASIS, 2013) is an XML interchange schema with no execution semantics. The typing guarantees Lex provides — typed holes, type-agreement of defeasible exceptions, syntactic temporal stratification, non-silent tribunal coercion — cannot be expressed in a schema-level XML type system.

**Akoma Ntoso** (OASIS LegalDocML, 2018) is a document-markup standard for statutes, regulations, and case law. Complementary to Lex rather than competitive: Akoma Ntoso marks up statute text; Lex encodes the compliance rules derived from it.

**Defeasible logic** (Nute 1987; Governatori 1999, 2005; Prakken and Sartor 1997). Untyped. A rule can defeat any other rule regardless of semantic domain. Lex's type-agreement constraint catches a class of errors untyped defeasibility permits. Prakken–Sartor's two-dimensional priority ordering is a direct theoretical antecedent to the Lex separation of defeasibility from temporal stratification.

**Horty, *Reasons as Defaults* (2012)**. Formalizes reasoning with defaults and priority, framed for legal argumentation rather than compliance evaluation; no typing of the discretion boundary, no temporal stratification, no effect system.

**ABLP** (Abadi, Burrows, Lampson, Plotkin, *A Calculus for Access Control in Distributed Systems*, 1993). Introduces principal-indexed assertions and delegation logic. The tribunal modality owes its shape to this line: ABLP's `A says s` corresponds in structure to `[T] A`. Lex contributes the explicit CanonBridge coercion and the refusal of implicit aggregation.

**Nadathur and Miller, higher-order logic programming**. Foundations for λProlog and the theory of hereditary Harrop formulas. Supplies the higher-order unification machinery relevant to Lex's type-inference open problem.

**XACML** (OASIS, 2005). Attribute-based access-control policy language. Production-grade but untyped; no formal calculus, no discretion boundary, no cross-authority coercion.

**Ponder** (Imperial College, 2000). Declarative policy language for network management. Obligations and authorizations as first-class constructs, without a typed calculus for the machine-vs-judgment boundary.

**ASP / clingo**. Answer-set programming. Defaults and preferences via stable-model semantics; decidable but untyped; no typed discretion, no temporal strata.

**ASPIC+ / Carneades** (Prakken; Gordon). Structured-argumentation frameworks for legal reasoning; oriented to argument evaluation rather than compliance-rule execution.

**Rego / OPA** (Open Policy Agent). Production rule engine over flat relations. No dependent types, no temporal-sort distinction, no typed interface across the discretion boundary.

**Cedar** (AWS, 2023). Typed authorization-policy language. Types are simple; no defeasibility, no temporal stratification, no tribunal modality, no discretion hole.

## 11. Open problems

Non-affine β for the admissible fragment requires Girard–Tait reducibility candidates. The current flat-admissible SN mechanization restricts β to affine bodies, where every bound index occurs at most once; lifting this restriction is scoped to a follow-up mechanization.

Full admissible-fragment preservation (reduction preserves types) and progress (well-typed terms reduce or are values), confluence of the reduction relation, and the full substitution lemma for binding forms remain open in the mechanization.

`crates/lex-core/src/smt.rs` implements SMT-LIB2 generation and an external Z3 bridge. Preserve the distinction between solver execution, returned status, and a checked proof of the encoding or calculus correspondence. The latter guarantee remains a separate obligation; absence or uncertainty must not become a successful verdict.

Dependent-match admissibility — extending admissibility to dependent pattern matching on inductive families — requires the prelude to supply inductive eliminators beyond the current flat-constructor pattern.

Tribunal modals in the admissible fragment require a stratification argument ensuring modal operators do not introduce dependency cycles. Temporal coercions reach the same frontier. The decidability argument requires that reduction terminates uniformly, not conditionally on which possible world is inhabited.

## 12. Ecosystem role

Lex-to-Op compilation is the workflow integration target. Lex describes typed rule predicates and proof obligations; Op carries operation contracts. The interface must bind preconditions, postconditions, effects, and evidence without changing either language’s semantics. This architectural statement does not certify a complete compiler or its adequacy.

The public integration target is replayable admission of a compiled Op payload with its rule evidence. `formal/coq/Lex/AdmissionEnvelope.v` establishes structural carrier conditions, including digest matching and accepted receipts. Full compiler adequacy, deployed execution, and cryptographic unforgeability require their own evidence. Public companion sources are `github.com/momentum-sez/lex`, `github.com/momentum-sez/op`, `github.com/momentum-sez/gstore`, and `github.com/momentum-sez/stack`.

## 13. Forward-looking commitments

This document describes Lex *as it is*. Two load-bearing claims are named here as the spine of the platonic-ideal Lex (full statements in `PLATONIC-IDEAL.md` §§2–3):

- **Feature Integration Theorem (target).** The four typed primitives — defeasibility, temporal stratification, tribunal modality, typed discretion holes — compose in the integrated Lex calculus without mutual interference; the integrated calculus admits unconditional preservation, progress, decidability of admissible-fragment type-checking, and the Curry-Howard reading of `PLATONIC-IDEAL.md` §5, with no feature appearing as a side condition on another's metatheorem. The theorem is *not* proved as stated; the present mechanization carries each feature individually plus a partial integration. The theorem is named here because it is the load-bearing claim downstream papers need: that Lex is *one calculus* with these four features, not four overlaid calculi with conditional behaviour at their joins.

- **Lex Expressiveness Boundary Theorem (target).** For every legal rule `R = (input-types, output-type, evaluation-procedure)`, `R` is expressible as a closed Lex term iff `R`'s evaluation procedure terminates on every well-typed input modulo typed holes, every non-mechanical step is annotated with a typed authority recognized in some tribunal of the bridge 2-category, and every authority annotation carries a witness that the supplied judgment satisfies a named decidable predicate on the input. This proposed characterization first requires a fixed source rule language, observations, and admissible translation class. Termination and annotations alone do not establish representability or exclusion. The "only if" direction is the limit theorem: rules failing these conditions cannot be expressed in Lex without an `UnsettledHole`, formalising Hart's penumbra and Dworkin's principles-against-rules as structural exclusions. The theorem is *not* proved as stated; it is named here because it converts the prose limit-discussion of the published paper's §2 into theorematic precision.

Both theorems are the deliverables of `ROADMAP.md` Phase A (A.6 and A.7 respectively). The Curry-Howard correspondence for typed discretion holes (the centerpiece of `PLATONIC-IDEAL.md` §5) is the deliverable of Phase B.2. The substrate interface specification (currently draft v0.1 in `SUBSTRATE-INTERFACE.md`) is frozen as v1.0 after Phase E lands.

The mechanization target is closure of every claimed theorem with explicit assumptions and a public proof artifact. Current proof status is recorded in `formal/README.md` and the named Rocq declarations. A `Qed` ending proves its stated implication; it does not discharge that implication's hypotheses. Administrative WHNF bounds are closed. Full-calculus normalization, substitution, confluence, preservation, match coverage, and the resulting unconditional type-safety claims retain separate obligations. `ROADMAP.md` retains the obligations toward unconditional full-calculus results. Maintain a theorem-by-theorem ledger rather than an unaudited percentage.

Falsifiers — the conditions under which the platonic-ideal plan is wrong — are enumerated in `PLATONIC-IDEAL.md` §12. The plan survives any single falsifier and rebuilds against any pair.

## 14. References

Abadi, M., Burrows, M., Lampson, B., and Plotkin, G. (1993). "A Calculus for Access Control in Distributed Systems." *ACM Transactions on Programming Languages and Systems*, 15(4), 706–734.

Araszkiewicz, M. and Zurek, T. (2015). "Comprehensive Framework for the Representation of Legal Interpretation." *ICAIL 2015*, ACM.

Bench-Capon, T.J.M. and Sartor, G. (2003). "A Model of Legal Reasoning with Cases Incorporating Theories and Values." *Artificial Intelligence and Law*, 11(2-3), 97–143.

Bhargavan, K., et al. (2016). "Formal Verification of Smart Contracts." *PLAS 2016*, ACM.

Dinesh, N., Joshi, A., Lee, I., and Stuckey, P. (2008). "Normative Requirements via Regulations." *ICLP 2008*, Springer.

Dworkin, R. (1977). *Taking Rights Seriously.* Harvard University Press.

Dworkin, R. (1986). *Law's Empire.* Harvard University Press.

Gordon, T.F. (2010). "The Carneades Argumentation Support System." *Dimensions of Argument: Studies in Honour of Douglas Walton*, College Publications.

Governatori, G. (2005). "Representing Business Contracts in RuleML." *International Journal of Cooperative Information Systems*, 14(2-3), 181–216.

Hart, H.L.A. (1961). *The Concept of Law.* Oxford University Press.

Hildenbrandt, E., et al. (2018). "KEVM: A Complete Formal Semantics of the Ethereum Virtual Machine." *CSF 2018*, IEEE.

Horty, J.F. (2012). *Reasons as Defaults.* Oxford University Press.

Libal, T. and Steen, A. (2019). "NAI: Towards Transparent and Usable Semi-Automated Legal Analysis." *ARCADE 2019*.

Merigoux, D., Chataing, N., and Protzenko, J. (2021). "Catala: A Programming Language for the Law." *Proceedings of the ACM on Programming Languages*, 5(ICFP), 1–29.

Nadathur, G. and Miller, D. (1998). "Higher-Order Logic Programming." *Handbook of Logic in Artificial Intelligence and Logic Programming*, Oxford University Press.

Nute, D. (1987). "Defeasible Reasoning." *Proceedings of the 20th Hawaii International Conference on System Science*, IEEE.

OASIS. (2005). *eXtensible Access Control Markup Language (XACML) Version 2.0.* OASIS Standard.

OASIS. (2013). *LegalRuleML Core Specification Version 1.0.* OASIS Standard.

OASIS LegalDocML. (2018). *Akoma Ntoso Version 1.0.* OASIS Standard.

Prakken, H. and Sartor, G. (1997). "Argument-Based Extended Logic Programming with Defeasible Priorities." *Journal of Applied Non-Classical Logics*, 7(1), 25–75.

Prakken, H. (2010). "An Abstract Framework for Argumentation with Structured Arguments." *Argument and Computation*, 1(2), 93–124.

Sartor, G. (2005). *Legal Reasoning: A Cognitive Approach to the Law.* Springer.

Sloman, M. (1994). "Policy Driven Management for Distributed Systems." *Journal of Network and Systems Management*, 2(4), 333–360. (Ponder lineage.)

Cuppens, F. and Cuppens-Boulahia, N. (2008). "Modeling Contextual Security Policies." *International Journal of Information Security*, 7(4), 285–305.
