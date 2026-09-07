# Frontier Work 09 - Rule applies_to and Pack Binding

Status: frontier design note
Scope: typed rule-level scope declaration (`applies_to`) and the pack-bundle
contract that lets downstream Op programs discharge Lex obligations at
type-check time without re-running the Lex evaluator
Audience: Lex implementers, Op implementers, formal-methods reviewers,
sovereign-kernel authors

Canonical public reference: `docs/language-reference.md`

Companion proposal: [Op rule contracts and pack binding](https://github.com/momentum-sez/op/blob/frontier/lex-rule-contracts/docs/proposal-lex-rule-contract-and-pack-binding.md)
(extends `Contract` with a `LexRule(LexRuleRef)` variant; specifies pack
consumption from Op's side; the two proposals must land together).

This note is not the canonical public language reference. It documents a
proposed extension to `crates/lex-core/src/ast.rs` and a new pack-bundle
crate. Until the extension is admitted to the canonical language and the
Coq + Lean scaffolds are updated in step (per the policy in
`README.md` lines 275-284), the contents here are frontier design only.

## 0. Motivation

Lex today is jurisdiction-aware in metadata only. `LexCertificate`
(`crates/lex-core/src/certificate.rs`) carries `pub jurisdiction: String`
as a runtime field populated at certificate assembly. The defeasible rule
itself (`DefeasibleRule`, `ast.rs:327-338`) has no scope: a rule cannot
declare which jurisdiction it applies under, nor which operation kind it
binds to. Operation binding is "downstream consumer concern" — a phrase
that today resolves to: every consumer must invent its own binding.

This is the accident. The companion Op proposal proves the consequence:
the canonical Op program structure already keys on
`(operation_type, jurisdiction)` (`docs/language-spec.md` §2) and already
exposes `requires domains [...]; ensures domains [...]` as the rule-layer
contract surface. But `op-lex-compiler::build_program` produces
`Contracts::default()` (lib.rs:315) on every compilation — empty contracts
— because there is no typed Lex-side artifact that says "this rule applies
to (jurisdiction `sc`, operation `entity.incorporate`)" and therefore no
mechanical way to populate the program's contract block.

The fix is symmetric and small: lift jurisdictional scope from certificate
metadata into the rule's typed AST, and define a packaging contract under
which a frozen bundle of compiled Lex predicates can be consumed by Op's
type checker as the source of mechanical binding. After this, Lex still
owns rule meaning, Op still owns workflow structure, and neither language
re-interprets the other's semantics — but the binding between them stops
being prose and becomes a typed, content-addressed artifact.

## 1. Commitment map

| # | Commitment                                              | Module                              |
|---|---------------------------------------------------------|-------------------------------------|
| 1 | Typed `applies_to` field on rule terms                  | `ast::AppliesTo`, `ast::DefeasibleRule` |
| 2 | Parser: `applies_to { ... }` rule-block clause          | `parser::rule_clause`               |
| 3 | Elaborator: jurisdiction + operation-kind resolution    | `elaborate::resolve_applies_to`     |
| 4 | Type checker: `applies_to` is admissible, well-scoped   | `typecheck::check_rule_scope`       |
| 5 | Content-address rule under `applies_to`                 | `digest::rule_digest_v2`            |
| 6 | Pack bundle format: compiled-predicate emission         | `crates/lex-pack` (new)             |
| 7 | Lex→Op compilation contract: `CompiledLexPredicate`     | `crates/lex-pack::compiled`         |
| 8 | Coq + Lean scaffold update                              | `formal/coq`, `formal/lean`         |

Pre-existing Lex modules remain authoritative for everything else.
`applies_to` is additive; rules without it stay valid surface terms (see
§4.4 on backward compatibility and the migration window).

## 2. Type-system encoding

### 2.1 The `AppliesTo` term

```rust
/// Rule-level scope: declares which jurisdictions and operation kinds
/// this rule binds to. Both lists must be non-empty; "all" is encoded
/// as the explicit wildcard `*` rather than absence.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AppliesTo {
    /// Jurisdictions this rule binds to. Reuses `QualIdent` consistent
    /// with `ScopeField::Jurisdiction` (ast.rs:292).
    pub jurisdictions: Vec<JurisdictionScope>,
    /// Operation kinds this rule binds to. Operation kind names are
    /// canonical Op primitive names (e.g. `entity.incorporate`,
    /// `ownership.issue_shares`). The canonical list is sourced from
    /// `op_stdlib::canonical::CANONICAL_PRIMITIVES`
    /// (resolved via `op_stdlib::canonical::lookup(name)`); Lex does
    /// not invent its own enum.
    pub operation_kinds: Vec<OperationKindScope>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum JurisdictionScope {
    /// Specific jurisdiction (e.g. `sc`, `hn-prospera`).
    Specific(QualIdent),
    /// Wildcard: rule binds in every jurisdiction.
    All,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum OperationKindScope {
    /// Specific operation kind (must be a canonical Op primitive name).
    Specific(QualIdent),
    /// Family wildcard: every primitive whose name shares this prefix
    /// (e.g. `entity.*` matches `entity.incorporate`,
    /// `entity.dissolve`, etc.).
    Family(QualIdent),
    /// Wildcard: rule binds across every operation kind.
    All,
}
```

`AppliesTo::All × OperationKindScope::All` is admissible but elaborator-
warned: it implies "this rule is universal", which is rare and almost
always indicates a missing scope. The warning is informational; it does
not reject.

### 2.2 Extension to `DefeasibleRule`

```rust
pub struct DefeasibleRule {
    pub name: Ident,
    pub base_ty: Box<Term>,
    pub base_body: Box<Term>,
    pub exceptions: Vec<Exception>,
    pub lattice: Option<ContentRef>,
    /// NEW: required for compilation into a pack bundle.
    /// Optional at the AST level for surface-syntax backward compatibility,
    /// but `lex-pack::compile` rejects rules without it.
    pub applies_to: Option<AppliesTo>,
}
```

`applies_to` is `Option<AppliesTo>` at the AST level so the existing parser,
elaborator, and certificate writer can ingest pre-09 rules unchanged. The
pack compiler (§3) requires it: any rule without `applies_to` is excluded
from the pack with a structural diagnostic.

### 2.3 Surface syntax

```lex
rule sc_aml_001 : EntityFacts -> ComplianceVerdict
applies_to {
  jurisdictions: [ sc ]
  operation_kinds: [ entity.incorporate, entity.update_directors ]
}
=
  if EntityFacts.beneficial_owners.any(is_sanctioned)
  then NonCompliant(reason = "beneficial owner sanctioned")
  else Pending  -- requires further BO traversal
unless EntityFacts.exempt_under_treaty
```

Family form:

```lex
rule sc_general_kyc : EntityFacts -> ComplianceVerdict
applies_to {
  jurisdictions: [ sc ]
  operation_kinds: [ entity.* ]   -- every entity-family primitive
}
= ...
```

Universal form (warned):

```lex
rule sanctions_terminal : Operation -> ComplianceVerdict
applies_to { jurisdictions: [*]; operation_kinds: [*] }
-- elaborator emits Diagnostic::UniversalScope { rule = sanctions_terminal }
= ...
```

### 2.4 Type-checker rule

Two checks, both structural:

1. **Operation-kind resolution.** Every `OperationKindScope::Specific`
   and `OperationKindScope::Family` prefix must resolve against the
   canonical Op primitive list supplied via the elaborator's
   `OperationKindRegistry` (a thin trait the host implements; in practice
   this comes from `op-stdlib::canonical`). A rule that binds to a
   nonexistent operation kind fails admissibility.
2. **Jurisdiction well-formedness.** Every `JurisdictionScope::Specific`
   must be a syntactically valid `QualIdent`. Lex does not validate
   jurisdiction codes against any external registry — that is a pack-
   curator concern (§3.4).

Neither check requires running the Lex evaluator or accessing entity
state. Both fire at parse + elaborate + typecheck time.

## 3. Pack bundle: the compilation contract

The pack bundle is the binding medium. A pack is a content-addressed,
deterministic artifact produced by `lex-pack::compile` from a set of
admitted Lex rules and consumed by `op-lex-compiler` (and any other Op
host) at Op-program compile time.

### 3.1 New crate: `lex-pack`

`crates/lex-pack/` lives in this repo, depends on `lex-core` only, and
has no host or runtime dependencies. A downstream pack format is free to bundle a `lex-pack::Pack` as a
sub-artifact, but the pack format itself is canonical Lex.

### 3.2 `Pack` and `CompiledLexPredicate`

```rust
/// A frozen bundle of admissible compiled Lex predicates.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Pack {
    /// Pack version. Monotonic, signed by curator (§3.4).
    pub version: PackVersion,
    /// Content digest of the pack body (excludes signature).
    pub digest: PackDigest,
    /// Curator signature over `digest`.
    pub signature: CuratorSignature,
    /// All admissible rules in this pack.
    pub rules: Vec<CompiledLexPredicate>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompiledLexPredicate {
    /// SHA-256 of the canonicalized rule term.
    pub rule_hash: LexRuleHash,
    /// The rule's scope, lifted from `DefeasibleRule.applies_to`.
    pub applies_to: AppliesTo,
    /// The rule name (informational; equality is by hash, not name).
    pub name: Ident,
    /// Statute citation, lifted from rule metadata.
    pub legal_basis: String,
    /// The compiled body: a typed, elaborated, indices-assigned,
    /// admissibility-checked term ready for downstream consumption.
    /// This is the artifact Op's type checker structurally discharges
    /// against. It is NOT re-executed by the Op host.
    pub body: CompiledTerm,
    /// Proof obligations the rule emits (from `obligations.rs`).
    pub obligations: Vec<ProofObligation>,
}
```

`CompiledTerm` is a stable serialization of the elaborated rule body in
de-Bruijn form, with all `Term::Hole` instances either filled (with their
witnessing `PCAuth` reference) or left explicit and tracked. The pack
compiler refuses to admit a rule with unfilled holes that lack a residual
record; this is the bridge between the runtime caveat primitive surface
(`predicate_runtime`) and the pack-time admissibility check.

### 3.3 Index by `(jurisdiction, operation_kind)`

A pack supports the canonical lookup downstream consumers need:

```rust
impl Pack {
    /// Returns every rule in this pack whose `applies_to` matches
    /// the given (jurisdiction, operation_kind). Wildcards expand
    /// according to §2.1. Operation-family wildcards match by prefix.
    pub fn rules_for(
        &self,
        jurisdiction: &QualIdent,
        operation_kind: &QualIdent,
    ) -> Vec<&CompiledLexPredicate>;
}
```

This is the function `op-lex-compiler` will call at Op-program compile
time to populate `Contracts::requires` (see companion proposal §3.2). It
is not the only function: pack curators, regulators, and audit tools can
all use the same primitive.

### 3.4 Curator signature and pack version

A pack is curator-signed. The curator declares which jurisdictions they
have authority over (this is metadata in the pack manifest, distinct
from rule-level `applies_to`). The Lex programme does not specify
curator authority; that is sovereign-kernel concern. The Lex programme
specifies that the pack is signed and that the signature is verified
before any rule from the pack can be referenced.

`PackVersion` is `(curator_did, semver, content_digest)`. Two packs
with different curators are distinct artifacts even if they contain the
same rules; this is intentional and keeps curator provenance explicit at the binding layer.

## 4. Compilation pipeline

```
Lex source
   │
   │  parser           (extended to accept `applies_to { ... }` clause)
   ▼
Term::Defeasible { applies_to: Some(...), .. }
   │
   │  elaborate        (resolves QualIdents, indices, scope registry)
   ▼
ElaboratedRule
   │
   │  typecheck        (admissibility + applies_to well-formedness)
   ▼
AdmissibleRule
   │
   │  lex-pack::compile   (canonicalize, content-address, sign)
   ▼
CompiledLexPredicate ──── shipped inside ────► Pack
                                                 │
                                                 │  consumed by
                                                 ▼
                                          op-lex-compiler
                                          (§3.2 of companion)
```

Each stage is structural and deterministic. Same source + same elaborator
config + same Lex-core revision → same `CompiledLexPredicate`. Replay
discipline matches existing Lex evaluator replay.

### 4.1 Backward compatibility (a window, with teeth)

Rules without `applies_to` parse and typecheck as today. They cannot be
admitted to a pack: `lex-pack::compile` rejects them with
`PackCompileError::MissingAppliesTo { rule }`. This is a hard reject, not
a warning, because the entire purpose of the pack is to carry the
binding. A rule that does not declare its scope cannot be packed; a rule
that is not packed cannot be referenced from an Op program; a program
that does not reference it does not discharge it. The chain is a single
gate, not a chain of soft warnings.

The migration window is exactly: how long does it take an existing Lex
rule corpus to acquire `applies_to` clauses? The answer is not "as long
as needed"; it is a named deadline per pack curator, set at pack adoption.
Curators that miss the deadline ship empty packs. This is the supremum-
discipline shape: soft cutover with teeth, not soft cutover indefinitely.

## 5. Formal scaffold updates

Per `README.md` lines 275-284, every AST extension updates Coq and Lean
in step.

- **Coq.** `formal/coq/Lex/AST.v` adds `AppliesTo` as an inductive type
  and extends `DefeasibleRule` with the optional field. `formal/coq/
  Lex/Typing.v` adds the well-formedness rule for `AppliesTo`. The
  existing `progress` theorem (Qed-closed conditional on `confluence_
  property` and `match_exhaustiveness_property` per the Lex repo
  baseline) is unaffected: `applies_to` is metadata, not a term-level
  computation rule.
- **Lean.** `formal/lean/LexCore/AST.lean` and `Typing.lean` mirror the
  same extension. No new `sorry` introduced; existing baseline of 1
  sorry remains stable.
- **Pack.** A new file `formal/coq/Lex/Pack.v` defines `Pack`,
  `CompiledLexPredicate`, and proves `pack_rules_for_completeness`: for
  any pack `P` and any `(j, k)`, `P.rules_for(j, k)` returns exactly the
  set of `CompiledLexPredicate` in `P` whose `applies_to` matches.

## 6. Open obligations

1. **Operation-kind authority.** Lex defers to `op-stdlib` for the
   canonical operation-kind list. The companion proposal must specify
   how that list is exported and versioned. A change to the canonical
   list is a coordinated `lex-core` + `op-core` + `op-stdlib` update,
   not a unilateral Op decision.
2. **Curator authority.** Pack curator authority is sovereign-kernel
   concern, not Lex concern. But the pack format must specify the
   signature scheme and the curator-DID format. Hybrid PQ
   (Ed25519 || ML-DSA-65 || SLH-DSA) per the canonical hybrid signature
   discipline.
3. **Hole residuals in packs.** If a rule body contains `Term::Hole`
   without a filling, can it be packed? Conservative default: no; the
   pack compiler rejects unfilled holes. Frontier alternative: a hole
   whose `authority` is named and whose scope is bounded is admissible
   as a "deferred-fill obligation" carried in the pack — this matches
   `HoleExtension` admissibility mode in the existing checker. Choose
   the conservative default for v1.
4. **Rule-rule composition across packs.** Two packs from two curators
   may both contain rules for `(sc, entity.incorporate)`. Op's
   completeness check (companion §3.3) sees the union. This is
   intentional: it lets a sovereign kernel layer a federal pack and a
   ministerial pack without merging them. But it raises a question:
   what if the two rules contradict? Lattice meet on verdict is the
   answer (`compose::verdict_meet` exists today); the pack consumer
   composes verdicts at runtime against entity state, not at compile
   time. The Op type checker only verifies structural discharge per
   rule, not consistency across rules.

## 7. Status doctrine

Per `AGENTS.md`/`CLAUDE.md` discipline:

- **Proposed (frontier).** Everything in this document.
- **Open.** §6 obligations.
- **Implemented.** Nothing yet. Implementation lands as a single PR per
  numbered commitment in §1.
- **Conjectural.** Curator authority semantics; deferred to companion
  proposal and to the kernel-side adopter.

A change to this document that promotes any line above frontier status
must update the corresponding crate, formal scaffold, and language
reference in step.
