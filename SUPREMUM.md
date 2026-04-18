# Lex: Authoritative Design

## 1. What Lex is

Lex is a dependently-typed logic for jurisdictional compliance rules. A Lex rule is a closed term in the core calculus. It has a type. It accepts structured inputs. It produces a verdict. The verdict carries a machine-checkable proof that every intermediate obligation was discharged by a named decision procedure.

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
- **Fill** — `Γ ⊢ e : A` and `Γ ⊢ w : PCAuth(auth, h)` yields `Γ ⊢ fill(h, e, w) : A` with effect row `∅`.
- **Effect-Weaken** — `Γ ⊢ e : A ! ρ1` and `ρ1 ⊆ ρ2` yields `Γ ⊢ e : A ! ρ2`.
- **Sanctions-Dominance** — `Γ ⊢ p : SanctionsNonCompliant(entity)` yields `Γ ⊢ sanctions-dominance(p) : ⊥`. The bottom type absorbs all eliminators. No tribunal coercion, defeasibility exception, or discretion hole rescues a sanctions-non-compliance proof.

Evaluation is bidirectional type-checking against a `Context` drawn from the prelude signature plus bounded weak-head-normal-form reduction under a fuel counter with a finite substitution size limit. The type checker performs this reduction and structural comparison at each step. Definitional equality reduces to WHNF under finite fuel; the fuel counter's exhaustion yields the verdict `Indeterminate`, which is a proper outcome of the calculus rather than a timeout exception.

## 4. Admissible fragment

The full calculus is undecidable. General recursion, unrestricted match on user-defined inductive types, and unfilled discretion holes each prevent the type checker from terminating. Lex identifies a syntactic sub-language — the admissible fragment — where type-checking is decidable.

A term is admissible when it satisfies five positive clauses:

1. **First-order data.** Variables, constants, lambda abstractions with annotated domains, applications, let-bindings, type annotations, and pattern matching on prelude-provided inductive types.
2. **No modal forms.** Temporal modals `@t A`, `◇t A`, `□[t1,t2] A`, the temporal coercions `lift_0` and `derive_1`, and the tribunal modals `[T] A`, `coerce[T1 => T2]` are excluded. Modal operators introduce possible-world semantics where type-checking requires reasoning about propositions indexed by time or authority; the decidability argument requires uniform reduction termination, not conditional on which world is inhabited.
3. **No unfilled holes.** A `Hole` produces the `discretion(auth)` effect, which cannot be discharged without a `PCAuth` witness. Admitting unfilled holes would require the type checker to reason about effect-discharge obligations that may never be met.
4. **Decidable-exhaustiveness match.** Every match scrutinee has an inductive type whose constructor set is known at admissibility-check time. The compliance-prelude types (`ComplianceVerdict`, `Bool`, `Nat`, `SanctionsResult`, `ComplianceTag`) satisfy this condition, which is why the practical rule suites fall inside the admissible fragment.
5. **No structural recursion.** The recursion form `fix f : A := b` permits non-terminating reduction and is excluded.

Sigma types, content-addressed references, principle-balancing, and the `unlock` eliminator are also excluded.

The admissibility predicate is decidable: the check is a structural traversal that returns either `admissible t` or `¬ admissible t` for every term `t`. The Rocq mechanization establishes this decidability as an inductive relation on the core AST.

Oracle-effect admissibility requires attestation. An oracle query carries an `OracleRef` naming the external resolver and a depth bound constraining the number of nested oracle queries the resolver may itself emit. An `oracle(ref)` effect is admissible when the referenced oracle is registered in the signature, the depth bound is a natural-number literal, and the attestation witness accompanies the query. The boundedness of nested oracle resolution prevents admissibility from reducing to a non-terminating oracle-query chain; the depth bound is a mechanical termination argument at the oracle boundary.

## 5. Mechanization status

The Rocq 9.1.1 mechanization in `formal/coq/FlatAdmissibleSN.v` establishes strong normalization of the flat admissible fragment extended with affine lambdas under call-by-value β and defeasible rules with non-empty exception lists. The principal theorem is:

```
Theorem flat_admissible_sn_ext : forall t, SN t.   (line 464, Qed line 475)
```

`Print Assumptions flat_admissible_sn_ext.` (line 537) reports `Closed under the global context`. The proof uses no axioms beyond the standard library's inductive and well-foundedness constructions. The same closure report holds for `flat_admissible_sn` (line 451, Qed line 461), `step_decreases_size` (line 404, Qed line 433), `subst_size` (line 235), and `subst_size_affine`.

The proof proceeds by a well-founded size measure `μ : FAdm → ℕ`. The key ingredient is the substitution identity

```
|t[u/k]| + occ(t, k) = |t| + occ(t, k) · |u|
```

and its affine corollary: when `occ(body, 0) ≤ 1`, substitution yields `|body[v/0]| ≤ |body| + |v| − 1`. Each of the ten reduction rules — ζ, μ-v, δ-0, δ-k, β, and the five congruences ξ-let, ξ-mat, ξ-def, ξ-app-l, ξ-app-r — strictly decreases the size measure. Well-foundedness of `<` on ℕ and measure-decreasing lifting conclude SN.

The sub-fragment covered captures every §7 worked example of the canonical paper that falls inside the admissible fragment: the BVI director-minimum rule, the Seychelles IBC Act minimum-directors rule, the Pakistan Limitation Act tolling rule under the stratification premise, and the Seychelles sanctions hard-block rule.

Admissibility decidability is mechanized. What remains open in the mechanization: strong normalization of the non-affine β sub-fragment (requires a Girard–Tait reducibility-candidates argument), the full admissible-fragment preservation lemma (reduction preserves types), progress (well-typed terms reduce or are values), the full substitution lemma for binding forms, and confluence. The flat admissible-fragment result bounds reduction-chain length to `|t_0| − 1` and validates the fuel counter in `crates/lex-core/src/evaluate.rs` as a correct operational bound on evaluation budget for FAdm-shaped rules.

## 6. Fill and PCAuth

Proof-carrying authorization is a dependent record type:

```
PCAuth(auth, h) = {
  signer    : Did,
  role      : AuthorityRole(auth),
  scope_ok  : ScopeWitness(h.scope),
  timestamp : Time_0,
  signature : Ed25519Sig(signer, h, value)
}
```

The five fields bind the filler's decentralized identifier, a verifiable credential attesting that the signer holds the named role under the named authority, a witness that the hole's scope constraint is met, a frozen historical timestamp for when the judgment was made, and a cryptographic signature over the triple `(signer, hole-id, value)`. The `role` field is the trust anchor: it is witnessed by the authority named in the hole, not self-asserted. Fabricating a PCAuth witness requires either compromising the authority's credential issuance or forging the cryptographic signature.

The Fill rule flow-through preserves the filler's effect row. If the filler `e` carries effect row `ρ` at the Fill site, the effect row of `fill(h, e, w)` is `ρ` — the filler's effects propagate unchanged while the hole's own `discretion(auth)` effect is discharged. Admissibility of a filled term requires `ρ = ∅` post-substitution: a filler carrying its own unfilled holes or oracle queries is outside the admissible fragment even when the enclosing hole is filled.

Cryptographic verification of the PCAuth signature occurs at the proof-kernel boundary, not inside the typing rule. The typing rule is parametric in the signature scheme: the core calculus treats the signature as an opaque proof term. The kernel verifies the Ed25519 signature against the credential chain rooted at the named authority when the proof bundle enters the certificate-building pipeline. This separation keeps the typing derivation closed under substitution without embedding a cryptographic decision procedure in the type checker.

## 7. Temporal stratification

`Time_0` records frozen historical event time. `Time_1` records derived legal time. `lift_0 : Time_0 → Time_1` is total and one-way: every frozen fact can produce a derived consequence. The grammar has no constructor that demotes `Time_1` to `Time_0`. Any term that would require such demotion fails to parse, and any term that applies `lift_0` to a `Time_1` argument is rejected by `temporal::check_temporal_stratification` with the diagnostic "there is no coercion from Time_1 to Time_0."

Retroactive rule change regenerates `Time_1` consequences from unchanged `Time_0` record. The paradigm is the *Schrems II* decision (Court of Justice of the European Union, C-311/18): an entity that relied on Privacy Shield as its legal basis for a data-transfer verdict at one `Time_1` could, the following week, be evaluated against a rule framework in which Privacy Shield never provided a valid basis at that same `Time_1`. The `Time_0` observation — when the transfer occurred — does not change. The `Time_1` verdict — what the law says about the transfer under the currently-operative framework — is regenerated by re-running the rules against the unchanged `Time_0` record under the new pack version. The asof-indexing of every verdict records which framework produced it at what event time, so every verdict remains auditable across regulatory discontinuities.

## 8. Tribunal modality

`[T] A` indexes a proposition `A` by the tribunal `T` asserting it. Two tribunals may assert contradictory propositions about the same facts. The Tribunal-Elim rule requires an explicit `CanonBridge(T1, T2, A)` witness: a term proving the two tribunals agree on the proposition. No implicit aggregation operates over tribunals — there is no join, no voting, no FATF-member precedence, no hierarchy. Any aggregation scheme would encode a political judgment about which authority matters more, which the logic refuses to encode.

Mutual recognition agreements are logical objects of the calculus. Each is a `CanonBridge` witness attested by both tribunals, inhabiting the type `CanonBridge(T1, T2, A)` for a specific proposition `A`. The inhabitation of this type is an institutional fact about bilateral agreement, not a property the logic derives. When two tribunals disagree and no bridge witness exists, the disagreement is first-class type-theoretic content: a term typeable only under one tribunal cannot be coerced to the other, and an agent reasoning across both surfaces the divergence as an obstruction rather than silently selecting a winner. Cross-harbor aggregation at the compliance-tensor level operates on the verdicts that tribunals produce (the pointwise meet of those tensors), not on the tribunals themselves.

## 9. Implementation and repo state

The Rust workspace comprises four crates: `lex-core` (parser, elaborator, admissible type checker, evaluator, obligations, prelude, decision procedures, certificate, frontier core calculus), `lex-cli` (air-gapped command-line authoring shell), `lex-diag` (structured diagnostic ontology with controlled-English messages), and `mez-core-min` (a self-contained vendor of the subset of the kernel `mez-core` crate that Lex depends on: `CanonicalBytes`, `sha256_digest`, `ComplianceDomain`).

The workspace pins Rust 1.93.0 by `rust-toolchain.toml` and compiles from a cold clone without sibling checkouts. `cargo test --workspace` runs 742 tests across four binaries with zero failures: `lex-core` contributes 590 unit tests plus 82 integration tests across the ADGM rules fiber, Seychelles IBC rules fiber, adversarial-attacks suite (level self-application, cyclic priorities, unauthorised fills), discretion-hole contract suite, proof-pipeline end-to-end, and proptest soundness; `lex-diag` contributes 20 unit tests; `mez-core-min` contributes 44 unit tests; doc-tests add 7.

The release tag is 0.1.0. GitHub Actions CI builds Rust and Rocq; badges in `README.md` link to both. `REPRODUCIBILITY.md` records the toolchain pin, expected test counts, example outputs, and hardware budgets. An optional `kernel-integration` feature swaps the vendored `mez-core-min` types for the full kernel `mez-core` at a sibling checkout; byte-for-byte identical canonicalization, digests, and `ComplianceDomain` wire format are preserved across both configurations. CI does not enable the feature.

## 10. Prior art

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

SMT integration for side conditions (Presburger-arithmetic thresholds, boolean propositions, finite-domain membership beyond the prelude) requires an SMT-LIB2 bridge that preserves the typing guarantees across the call boundary. When SMT is unavailable, the pipeline falls through to `Unknown` rather than assuming a verdict.

Dependent-match admissibility — extending admissibility to dependent pattern matching on inductive families — requires the prelude to supply inductive eliminators beyond the current flat-constructor pattern.

Tribunal modals in the admissible fragment require a stratification argument ensuring modal operators do not introduce dependency cycles. Temporal coercions reach the same frontier. The decidability argument requires that reduction terminates uniformly, not conditionally on which possible world is inhabited.

## 12. Ecosystem role

Lex compiles to Op bytecode. A Lex rule encodes a typed jurisdictional predicate and emits structurally-derived proof obligations; an Op step references those obligations through `requires` and `ensures` contracts and discharges them as part of its effect row. Lex is the rule and proof layer; Op is the workflow layer. The interface is preconditions, postconditions, and effect discharge; neither language redefines the other's semantics.

The Mass kernel executes compiled Op programs against sovereign entity state. A Lex rule, its proof term, and the discharged obligations travel through the pipeline as a typed proof bundle. The bundle is content-addressed, Ed25519-signable, and replayable: a zone that accedes to a corridor replays the proof bundle against its own kernel to verify the verdict. Together the three components — Lex source, Op bytecode, proof bundle — support cross-zone replay, asof-indexed regulatory audit, and the separation of mechanical derivation from discretionary judgment that the typed hole specifies.

## 13. References

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
