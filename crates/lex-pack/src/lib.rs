//! # lex-pack — the Lex ↔ Op binding medium
//!
//! A [`Pack`] is a content-addressed, deterministic bundle of admissible
//! compiled Lex predicates, indexed by `(jurisdiction, operation_kind)`. It is
//! the artifact a downstream Op host (or any consumer, e.g. a sovereign kernel)
//! resolves at compile/admission time to bind a Lex rule to an operation it
//! runs — *without* inventing its own private `(operation, rule)` mapping
//! table. The mapping is the rule's own typed [`AppliesTo`] scope, lifted into
//! the pack at compile time.
//!
//! This crate implements the load-bearing core of Frontier-09 §3:
//!
//! - [`CompiledLexPredicate`] — a single rule's compiled body + its scope +
//!   its proof obligations, content-addressed by `rule_hash`.
//! - [`Pack`] — a frozen set of compiled predicates with a content digest, a
//!   pack version, and a (pluggably verified) curator signature.
//! - [`Pack::rules_for`] — the canonical `(jurisdiction, operation_kind)`
//!   resolution downstream consumers call.
//! - [`compile`] — turns admissible rules into a pack, rejecting fail-loud any
//!   rule that lacks an `applies_to` scope ([`PackCompileError::MissingAppliesTo`])
//!   or carries an unfilled discretion hole
//!   ([`PackCompileError::UnfilledHole`], the conservative §6.3 default).
//!
//! ## Honest scope boundary
//!
//! Curator authority semantics and the concrete hybrid-PQ signature scheme are
//! **sovereign-kernel concerns**, deferred by Frontier-09 §3.4 / §6.2. This
//! crate therefore does NOT mint or fake-verify a cryptographic signature: a
//! [`CuratorSignature`] is *carried* opaque bytes, and verification is
//! delegated to a caller-supplied [`CuratorVerifier`]. A pack produced by
//! [`compile`] is **unsigned** until a caller attaches a signature via
//! [`Pack::with_signature`]; [`Pack::verify`] fails closed on an unsigned pack
//! or a signature the verifier rejects. There is no default-permissive
//! "signature OK" path.
//!
//! The crate depends on `lex-core` (AST, certificate types) and `mez-canonical`
//! (content digest) only — no host or runtime dependencies (Frontier-09 §3.1).

use lex_core::ast::{AppliesTo, Hole, QualIdent, Term};
use lex_core::obligations::ProofObligation;
use mez_canonical::canonical::CanonicalBytes;
use mez_canonical::digest::sha256_digest;
use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// CompiledTerm — stable serialization of an elaborated, de-Bruijn-indexed body
// ---------------------------------------------------------------------------

/// A compiled rule body: the de-Bruijn-indexed term ready for downstream
/// structural discharge, plus its own content hash.
///
/// This is the artifact an Op host structurally discharges *against*; it is NOT
/// re-executed by the host (Frontier-09 §3.2). The `term` is a `lex-core`
/// [`Term`] in de-Bruijn form (indices already assigned), so two consumers that
/// deserialize the same pack see the same body.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledTerm {
    /// The elaborated, de-Bruijn-indexed body term.
    pub term: Term,
    /// SHA-256 hex of the canonical serialization of `term`.
    pub term_hash: String,
}

impl CompiledTerm {
    /// Build a compiled term from a body, content-addressing it.
    fn from_term(term: Term) -> Result<Self, PackCompileError> {
        let canonical = CanonicalBytes::new(&term)
            .map_err(|e| PackCompileError::Canonicalization(e.to_string()))?;
        let term_hash = sha256_digest(&canonical).to_hex();
        Ok(CompiledTerm { term, term_hash })
    }
}

// ---------------------------------------------------------------------------
// PackedObligation — serializable view of a proof obligation
// ---------------------------------------------------------------------------

/// A proof obligation the rule emits, in a serializable form (Frontier-09
/// §3.2).
///
/// `lex-core`'s [`ProofObligation`] is not itself `Serialize` (it carries a
/// live `Term`), so the pack stores the structural fields plus the obligation
/// term as a [`CompiledTerm`]. The category is recorded as its canonical debug
/// name (the `ObligationCategory` enum is a closed, stable set).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PackedObligation {
    /// Structural obligation id (e.g. `"obl-0001"`).
    pub id: String,
    /// Human-readable description.
    pub description: String,
    /// Obligation category name (e.g. `"ExhaustiveMatch"`).
    pub category: String,
    /// The obligation's term, content-addressed.
    pub term: CompiledTerm,
    /// The expected verdict / outcome string.
    pub expected: String,
    /// The suggested decision procedure.
    pub suggested_procedure: String,
}

impl PackedObligation {
    fn from_obligation(o: &ProofObligation) -> Result<Self, PackCompileError> {
        Ok(PackedObligation {
            id: o.id.clone(),
            description: o.description.clone(),
            category: format!("{:?}", o.category),
            term: CompiledTerm::from_term(o.term.clone())?,
            expected: o.expected.clone(),
            suggested_procedure: o.suggested_procedure.clone(),
        })
    }
}

// ---------------------------------------------------------------------------
// CompiledLexPredicate — a single packed rule
// ---------------------------------------------------------------------------

/// A frozen, admissible compiled Lex predicate (Frontier-09 §3.2).
///
/// Equality across packs is by `rule_hash`, not by `name` (the name is
/// informational). Two curators that pack the same rule body produce the same
/// `rule_hash`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledLexPredicate {
    /// SHA-256 hex of the canonicalized rule term (content address).
    pub rule_hash: String,
    /// The rule's typed scope, lifted from [`lex_core::ast::DefeasibleRule::applies_to`].
    pub applies_to: AppliesTo,
    /// The rule name (informational; equality is by `rule_hash`).
    pub name: String,
    /// Statute citation, lifted from rule metadata.
    pub legal_basis: String,
    /// The compiled, de-Bruijn-indexed body.
    pub body: CompiledTerm,
    /// Proof obligations the rule emits.
    pub obligations: Vec<PackedObligation>,
}

impl CompiledLexPredicate {
    /// Whether this predicate binds the given concrete `(jurisdiction,
    /// operation_kind)`.
    pub fn matches(&self, jurisdiction: &QualIdent, operation_kind: &QualIdent) -> bool {
        self.applies_to.matches(jurisdiction, operation_kind)
    }
}

// ---------------------------------------------------------------------------
// An admitted rule (compile input)
// ---------------------------------------------------------------------------

/// The compile input for one rule: an admissible rule body, its name, its legal
/// basis, and (required) its scope.
///
/// The caller is responsible for having already run the rule through
/// `lex-core`'s parse → elaborate → typecheck (admissibility) pipeline. The
/// pack compiler does the de-Bruijn index assignment, content-addressing,
/// obligation extraction, and the structural §6.3 hole check; it does not
/// re-run admissibility (that is the caller's contract, mirroring the existing
/// Lex pipeline split).
#[derive(Debug, Clone)]
pub struct AdmittedRule {
    /// Rule name (informational).
    pub name: String,
    /// Statute citation.
    pub legal_basis: String,
    /// Required scope. A rule whose `DefeasibleRule.applies_to` is `None`
    /// cannot be packed — pass `None` here and [`compile`] rejects it
    /// fail-loud.
    pub applies_to: Option<AppliesTo>,
    /// The elaborated rule body term.
    pub body: Term,
}

// ---------------------------------------------------------------------------
// Pack version + signature
// ---------------------------------------------------------------------------

/// A pack version: `(curator_did, semver, content_digest)` (Frontier-09 §3.4).
///
/// Two packs with different curators are distinct artifacts even if they carry
/// identical rules — this enforces the I-2 sovereignty-structural invariant at
/// the binding layer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PackVersion {
    /// DID of the curator who declares authority over the pack's jurisdictions.
    pub curator_did: String,
    /// Monotonic semantic version string.
    pub semver: String,
    /// Content digest of the pack body (matches [`Pack::digest`]).
    pub content_digest: String,
}

/// An opaque curator signature over the pack's content digest.
///
/// The concrete scheme (hybrid PQ `Ed25519 || ML-DSA-65 || SLH-DSA`) is a
/// sovereign-kernel concern (Frontier-09 §6.2); this crate carries the bytes
/// and delegates verification to a [`CuratorVerifier`]. It never fabricates or
/// self-validates a signature.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CuratorSignature {
    /// Signature scheme identifier (e.g. `"hybrid-ed25519-mldsa65-slhdsa"`).
    pub scheme: String,
    /// Hex-encoded signature bytes over the pack content digest.
    pub signature_hex: String,
}

/// Verifies a curator signature over a pack content digest.
///
/// Implemented by the host (sovereign kernel). The pack crate provides no
/// default impl — there is no "signature OK" fallback.
pub trait CuratorVerifier {
    /// Verify `signature` over `content_digest`, signed by `curator_did`.
    /// Returns `Ok(())` only if the signature is genuinely valid; any failure
    /// (unknown curator, scheme mismatch, bad bytes) is `Err`.
    fn verify(
        &self,
        curator_did: &str,
        content_digest: &str,
        signature: &CuratorSignature,
    ) -> Result<(), String>;
}

// ---------------------------------------------------------------------------
// Pack
// ---------------------------------------------------------------------------

/// A frozen bundle of admissible compiled Lex predicates (Frontier-09 §3.2).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Pack {
    /// Pack version (curator DID, semver, content digest).
    pub version: PackVersion,
    /// Content digest of the pack body (excludes the signature).
    pub digest: String,
    /// Curator signature over `digest`. `None` for an unsigned pack — an
    /// unsigned pack is structurally valid as an in-flight artifact but
    /// [`Pack::verify`] refuses it.
    pub signature: Option<CuratorSignature>,
    /// All admissible rules in this pack.
    pub rules: Vec<CompiledLexPredicate>,
}

/// The signature-excluding body of a pack, used to compute [`Pack::digest`].
///
/// The digest binds the version's `(curator_did, semver)` and the rules, but
/// NOT the signature or the version's own `content_digest` (that would be a
/// circular self-reference). The curator signs this digest.
#[derive(Serialize)]
struct PackBody<'a> {
    curator_did: &'a str,
    semver: &'a str,
    rules: &'a [CompiledLexPredicate],
}

impl Pack {
    /// Resolve every rule whose scope matches the given `(jurisdiction,
    /// operation_kind)` (Frontier-09 §3.3).
    ///
    /// This is the function an Op host calls at program compile time to
    /// populate its contract block, and the function a kernel calls to find the
    /// rule(s) that bind an operation it admits. Wildcards and family prefixes
    /// expand per [`AppliesTo::matches`].
    pub fn rules_for(
        &self,
        jurisdiction: &QualIdent,
        operation_kind: &QualIdent,
    ) -> Vec<&CompiledLexPredicate> {
        self.rules
            .iter()
            .filter(|r| r.matches(jurisdiction, operation_kind))
            .collect()
    }

    /// Look up a single packed rule by its content hash.
    pub fn rule_by_hash(&self, rule_hash: &str) -> Option<&CompiledLexPredicate> {
        self.rules.iter().find(|r| r.rule_hash == rule_hash)
    }

    /// Attach a curator signature, producing a signed pack. The caller is
    /// responsible for having signed [`Pack::digest`] with the curator key;
    /// this only records the bytes (the signing key never enters this crate).
    pub fn with_signature(mut self, signature: CuratorSignature) -> Self {
        self.signature = Some(signature);
        self
    }

    /// Verify the pack fail-closed: the recomputed content digest must match
    /// the recorded `digest` and the version `content_digest`, AND the pack
    /// must carry a signature the supplied [`CuratorVerifier`] accepts.
    ///
    /// An unsigned pack is rejected ([`PackVerifyError::Unsigned`]). There is no
    /// default-permissive path.
    pub fn verify(&self, verifier: &dyn CuratorVerifier) -> Result<(), PackVerifyError> {
        let recomputed = self.recompute_digest()?;
        if recomputed != self.digest {
            return Err(PackVerifyError::DigestMismatch {
                recorded: self.digest.clone(),
                recomputed,
            });
        }
        if self.version.content_digest != self.digest {
            return Err(PackVerifyError::VersionDigestMismatch {
                version_digest: self.version.content_digest.clone(),
                body_digest: self.digest.clone(),
            });
        }
        let signature = self.signature.as_ref().ok_or(PackVerifyError::Unsigned)?;
        verifier
            .verify(&self.version.curator_did, &self.digest, signature)
            .map_err(PackVerifyError::SignatureRejected)
    }

    fn recompute_digest(&self) -> Result<String, PackVerifyError> {
        let body = PackBody {
            curator_did: &self.version.curator_did,
            semver: &self.version.semver,
            rules: &self.rules,
        };
        let canonical = CanonicalBytes::new(&body)
            .map_err(|e| PackVerifyError::Canonicalization(e.to_string()))?;
        Ok(sha256_digest(&canonical).to_hex())
    }
}

// ---------------------------------------------------------------------------
// compile
// ---------------------------------------------------------------------------

/// Compile a set of admissible rules into an **unsigned** [`Pack`] for the
/// given curator (Frontier-09 §3, §4).
///
/// Fail-loud rejections:
/// - a rule whose `applies_to` is `None` → [`PackCompileError::MissingAppliesTo`]
///   (the entire purpose of the pack is to carry the binding — an unscoped rule
///   cannot be packed, §4.1);
/// - a rule body carrying an unfilled discretion [`Hole`] →
///   [`PackCompileError::UnfilledHole`] (conservative §6.3 default);
/// - duplicate `rule_hash` (the same body packed twice) →
///   [`PackCompileError::DuplicateRule`].
///
/// The returned pack is unsigned; attach a curator signature with
/// [`Pack::with_signature`] before [`Pack::verify`] will accept it.
pub fn compile(
    curator_did: impl Into<String>,
    semver: impl Into<String>,
    rules: impl IntoIterator<Item = AdmittedRule>,
) -> Result<Pack, PackCompileError> {
    let mut compiled: Vec<CompiledLexPredicate> = Vec::new();

    for rule in rules {
        let applies_to = rule
            .applies_to
            .ok_or_else(|| PackCompileError::MissingAppliesTo {
                rule: rule.name.clone(),
            })?;

        // Conservative §6.3: reject a body with an unfilled hole. A filled
        // `HoleFill` is fine; a bare `Hole` is a deferred-fill obligation that
        // v1 does not admit into a pack.
        if let Some(hole) = first_unfilled_hole(&rule.body) {
            return Err(PackCompileError::UnfilledHole {
                rule: rule.name.clone(),
                hole: hole
                    .name
                    .as_ref()
                    .map(|n| n.name.clone())
                    .unwrap_or_else(|| "<anonymous>".to_string()),
            });
        }

        // Assign de-Bruijn indices for a stable, host-consumable body.
        let indexed = lex_core::debruijn::assign_indices(&rule.body).map_err(|e| {
            PackCompileError::IndexAssignment {
                rule: rule.name.clone(),
                reason: format!("{e:?}"),
            }
        })?;

        let body = CompiledTerm::from_term(indexed)?;

        let obligations = lex_core::obligations::extract_obligations(&rule.body)
            .iter()
            .map(PackedObligation::from_obligation)
            .collect::<Result<Vec<_>, _>>()?;

        let predicate = CompiledLexPredicate {
            rule_hash: body.term_hash.clone(),
            applies_to,
            name: rule.name.clone(),
            legal_basis: rule.legal_basis,
            body,
            obligations,
        };

        if compiled.iter().any(|p| p.rule_hash == predicate.rule_hash) {
            return Err(PackCompileError::DuplicateRule {
                rule_hash: predicate.rule_hash,
            });
        }
        compiled.push(predicate);
    }

    let curator_did = curator_did.into();
    let semver = semver.into();

    // Content-address the pack body (signature-excluding).
    let body = PackBody {
        curator_did: &curator_did,
        semver: &semver,
        rules: &compiled,
    };
    let canonical = CanonicalBytes::new(&body)
        .map_err(|e| PackCompileError::Canonicalization(e.to_string()))?;
    let digest = sha256_digest(&canonical).to_hex();

    Ok(Pack {
        version: PackVersion {
            curator_did,
            semver,
            content_digest: digest.clone(),
        },
        digest,
        signature: None,
        rules: compiled,
    })
}

/// Find the first unfilled discretion [`Hole`] in a term, if any. A
/// `Term::HoleFill` is a *filled* hole — its filler is recursed but the fill
/// itself is not an unfilled hole.
fn first_unfilled_hole(term: &Term) -> Option<&Hole> {
    match term {
        Term::Hole(h) => Some(h),

        // Leaves — no children.
        Term::Var { .. }
        | Term::Sort(_)
        | Term::Constant(_)
        | Term::ContentRefTerm(_)
        | Term::IntLit(_)
        | Term::RatLit(_, _)
        | Term::StringLit(_)
        | Term::AxiomUse { .. } => None,

        // Single-child / paired children.
        Term::Pair { fst, snd } => first_unfilled_hole(fst).or_else(|| first_unfilled_hole(snd)),
        Term::Proj { pair, .. } => first_unfilled_hole(pair),
        Term::App { func, arg } => first_unfilled_hole(func).or_else(|| first_unfilled_hole(arg)),
        Term::SanctionsDominance { proof } => first_unfilled_hole(proof),
        Term::DefeatElim { rule } => first_unfilled_hole(rule),
        Term::Lift0 { time } => first_unfilled_hole(time),
        Term::Derive1 { time, witness } => {
            first_unfilled_hole(time).or_else(|| first_unfilled_hole(witness))
        }
        Term::Annot { term, ty } => first_unfilled_hole(term).or_else(|| first_unfilled_hole(ty)),
        Term::Unlock { effect_row, body } => {
            first_unfilled_hole(effect_row).or_else(|| first_unfilled_hole(body))
        }

        // Binders.
        Term::Lambda { domain, body, .. } => {
            first_unfilled_hole(domain).or_else(|| first_unfilled_hole(body))
        }
        Term::Pi {
            domain, codomain, ..
        } => first_unfilled_hole(domain).or_else(|| first_unfilled_hole(codomain)),
        Term::Sigma { fst_ty, snd_ty, .. } => {
            first_unfilled_hole(fst_ty).or_else(|| first_unfilled_hole(snd_ty))
        }
        Term::Let { ty, val, body, .. } => first_unfilled_hole(ty)
            .or_else(|| first_unfilled_hole(val))
            .or_else(|| first_unfilled_hole(body)),
        Term::Rec { ty, body, .. } => first_unfilled_hole(ty).or_else(|| first_unfilled_hole(body)),

        // Collections.
        Term::InductiveIntro { args, .. } => args.iter().find_map(first_unfilled_hole),
        Term::Match {
            scrutinee,
            return_ty,
            branches,
        } => first_unfilled_hole(scrutinee)
            .or_else(|| first_unfilled_hole(return_ty))
            .or_else(|| branches.iter().find_map(|b| first_unfilled_hole(&b.body))),

        // Temporal / tribunal modals.
        Term::ModalAt { body, .. }
        | Term::ModalEventually { body, .. }
        | Term::ModalAlways { body, .. }
        | Term::ModalIntro { body, .. } => first_unfilled_hole(body),
        Term::ModalElim { term, witness, .. } => {
            first_unfilled_hole(term).or_else(|| first_unfilled_hole(witness))
        }

        // Defeasible: walk base + exception bodies/guards.
        Term::Defeasible(dr) => first_unfilled_hole(&dr.base_ty)
            .or_else(|| first_unfilled_hole(&dr.base_body))
            .or_else(|| {
                dr.exceptions.iter().find_map(|e| {
                    first_unfilled_hole(&e.guard).or_else(|| first_unfilled_hole(&e.body))
                })
            }),

        // A filled hole: the hole is discharged, recurse only into children.
        Term::HoleFill { filler, pcauth, .. } => {
            first_unfilled_hole(filler).or_else(|| first_unfilled_hole(pcauth))
        }

        // Principle balance: structural only; its sub-steps carry no holes in
        // the admissible fragment, so treat as a leaf for the hole check.
        Term::PrincipleBalance(_) => None,
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors raised while compiling a [`Pack`].
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum PackCompileError {
    /// A rule was offered without an `applies_to` scope. The pack carries the
    /// binding; an unscoped rule cannot be packed (Frontier-09 §4.1).
    #[error(
        "rule '{rule}' has no applies_to scope; a rule without a declared scope cannot be packed \
         (it cannot be referenced from an Op program)"
    )]
    MissingAppliesTo {
        /// The offending rule name.
        rule: String,
    },
    /// A rule body carries an unfilled discretion hole (conservative §6.3
    /// default rejects it).
    #[error(
        "rule '{rule}' carries an unfilled discretion hole '{hole}'; a hole must be filled before \
         the rule can be packed (Frontier-09 §6.3 conservative default)"
    )]
    UnfilledHole {
        /// The offending rule name.
        rule: String,
        /// The hole name (`<anonymous>` for `?_`).
        hole: String,
    },
    /// Two rules canonicalize to the same body (same content hash).
    #[error("duplicate rule in pack: two rules content-address to {rule_hash}")]
    DuplicateRule {
        /// The colliding content hash.
        rule_hash: String,
    },
    /// De-Bruijn index assignment failed for a rule body.
    #[error("de-Bruijn index assignment failed for rule '{rule}': {reason}")]
    IndexAssignment {
        /// The offending rule name.
        rule: String,
        /// The underlying reason.
        reason: String,
    },
    /// Canonical serialization failed.
    #[error("canonical serialization failed: {0}")]
    Canonicalization(String),
}

/// Errors raised while verifying a [`Pack`].
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum PackVerifyError {
    /// The recomputed body digest does not match the recorded digest.
    #[error("pack digest mismatch: recorded {recorded}, recomputed {recomputed}")]
    DigestMismatch {
        /// The digest recorded on the pack.
        recorded: String,
        /// The digest recomputed from the body.
        recomputed: String,
    },
    /// The version's `content_digest` disagrees with the body digest.
    #[error("pack version content_digest {version_digest} != body digest {body_digest}")]
    VersionDigestMismatch {
        /// The digest recorded on the version.
        version_digest: String,
        /// The digest recomputed from the body.
        body_digest: String,
    },
    /// The pack carries no signature — fail closed.
    #[error("pack is unsigned; an unsigned pack cannot be verified (no default-permissive path)")]
    Unsigned,
    /// The supplied verifier rejected the signature.
    #[error("curator signature rejected: {0}")]
    SignatureRejected(String),
    /// Canonical serialization failed.
    #[error("canonical serialization failed: {0}")]
    Canonicalization(String),
}

#[cfg(test)]
mod tests {
    use super::*;
    use lex_core::ast::{
        DefeasibleRule, Exception, Ident, JurisdictionScope, OperationKindScope, Sort,
    };

    fn qi(s: &str) -> QualIdent {
        QualIdent::from_dotted(s)
    }

    fn scope(jur: &[&str], ops: &[OperationKindScope]) -> AppliesTo {
        AppliesTo {
            jurisdictions: jur
                .iter()
                .map(|j| {
                    if *j == "*" {
                        JurisdictionScope::All
                    } else {
                        JurisdictionScope::Specific(qi(j))
                    }
                })
                .collect(),
            operation_kinds: ops.to_vec(),
        }
    }

    /// A minimal admissible-shaped rule body. The body is a plain constant; the
    /// pack compiler does not re-run admissibility (caller's contract), so this
    /// is sufficient to exercise compile/index/hash/obligation extraction.
    fn body(verdict: &str) -> Term {
        Term::Constant(qi(verdict))
    }

    fn admitted(name: &str, applies_to: Option<AppliesTo>, body: Term) -> AdmittedRule {
        AdmittedRule {
            name: name.to_string(),
            legal_basis: "IBC Act 2016 s.130(1)".to_string(),
            applies_to,
            body,
        }
    }

    // ── applies_to scope matching ─────────────────────────────────────────

    #[test]
    fn specific_scope_matches_exact_pair_only() {
        let s = scope(
            &["sc"],
            &[OperationKindScope::Specific(qi("entity.incorporate"))],
        );
        assert!(s.matches(&qi("sc"), &qi("entity.incorporate")));
        // Wrong jurisdiction.
        assert!(!s.matches(&qi("de"), &qi("entity.incorporate")));
        // Wrong operation.
        assert!(!s.matches(&qi("sc"), &qi("entity.dissolve")));
    }

    #[test]
    fn family_wildcard_matches_by_segment_boundary() {
        let s = scope(&["sc"], &[OperationKindScope::Family(qi("entity"))]);
        assert!(s.matches(&qi("sc"), &qi("entity.incorporate")));
        assert!(s.matches(&qi("sc"), &qi("entity.dissolve")));
        // Family is segment-aware: `entity` must not match `entityx.*`.
        assert!(!s.matches(&qi("sc"), &qi("entityx.incorporate")));
        // Different family.
        assert!(!s.matches(&qi("sc"), &qi("ownership.issue_shares")));
    }

    #[test]
    fn jurisdiction_and_operation_wildcards_match_anything() {
        let s = scope(&["*"], &[OperationKindScope::All]);
        assert!(s.matches(&qi("sc"), &qi("entity.incorporate")));
        assert!(s.matches(&qi("anywhere"), &qi("any.operation")));
        assert!(s.is_universal());
    }

    #[test]
    fn non_universal_scope_is_not_flagged_universal() {
        let s = scope(&["sc"], &[OperationKindScope::All]);
        assert!(!s.is_universal());
    }

    // ── compile fail-loud ─────────────────────────────────────────────────

    #[test]
    fn compile_rejects_rule_without_applies_to() {
        let err = compile(
            "did:mass:curator",
            "1.0.0",
            vec![admitted("unscoped", None, body("Compliant"))],
        )
        .unwrap_err();
        assert_eq!(
            err,
            PackCompileError::MissingAppliesTo {
                rule: "unscoped".to_string()
            }
        );
    }

    #[test]
    fn compile_rejects_unfilled_hole() {
        let hole_rule = admitted(
            "has_hole",
            Some(scope(&["sc"], &[OperationKindScope::All])),
            Term::Defeasible(DefeasibleRule {
                name: Ident::new("has_hole"),
                base_ty: Box::new(Term::Sort(Sort::Prop)),
                // An unfilled hole nested in the body.
                base_body: Box::new(Term::Hole(lex_core::ast::Hole {
                    name: Some(Ident::new("discretion")),
                    ty: Box::new(Term::Sort(Sort::Prop)),
                    authority: lex_core::ast::AuthorityRef::Named(qi("regulator")),
                    scope: None,
                })),
                exceptions: vec![],
                lattice: None,
                applies_to: Some(scope(&["sc"], &[OperationKindScope::All])),
            }),
        );
        let err = compile("did:mass:curator", "1.0.0", vec![hole_rule]).unwrap_err();
        assert_eq!(
            err,
            PackCompileError::UnfilledHole {
                rule: "has_hole".to_string(),
                hole: "discretion".to_string(),
            }
        );
    }

    #[test]
    fn compile_rejects_duplicate_rule_bodies() {
        let a = admitted(
            "a",
            Some(scope(&["sc"], &[OperationKindScope::All])),
            body("Compliant"),
        );
        let b = admitted(
            "b",
            Some(scope(&["de"], &[OperationKindScope::All])),
            body("Compliant"), // same body → same hash
        );
        let err = compile("did:mass:curator", "1.0.0", vec![a, b]).unwrap_err();
        assert!(matches!(err, PackCompileError::DuplicateRule { .. }));
    }

    // ── pack resolution ───────────────────────────────────────────────────

    #[test]
    fn rules_for_resolves_by_jurisdiction_and_operation() {
        let pack = compile(
            "did:mass:curator",
            "1.0.0",
            vec![
                admitted(
                    "sc_incorporate",
                    Some(scope(
                        &["sc"],
                        &[OperationKindScope::Specific(qi("entity.incorporate"))],
                    )),
                    body("Compliant"),
                ),
                admitted(
                    "sc_entity_family",
                    Some(scope(&["sc"], &[OperationKindScope::Family(qi("entity"))])),
                    body("Pending"),
                ),
                admitted(
                    "de_incorporate",
                    Some(scope(
                        &["de"],
                        &[OperationKindScope::Specific(qi("entity.incorporate"))],
                    )),
                    body("NonCompliant"),
                ),
            ],
        )
        .expect("compile should succeed");

        // (sc, entity.incorporate) hits the specific + the family rule.
        let matched = pack.rules_for(&qi("sc"), &qi("entity.incorporate"));
        assert_eq!(matched.len(), 2);
        let names: Vec<&str> = matched.iter().map(|r| r.name.as_str()).collect();
        assert!(names.contains(&"sc_incorporate"));
        assert!(names.contains(&"sc_entity_family"));

        // (sc, entity.dissolve) hits only the family rule.
        let dissolve = pack.rules_for(&qi("sc"), &qi("entity.dissolve"));
        assert_eq!(dissolve.len(), 1);
        assert_eq!(dissolve[0].name, "sc_entity_family");

        // (de, entity.incorporate) hits only the DE rule.
        let de = pack.rules_for(&qi("de"), &qi("entity.incorporate"));
        assert_eq!(de.len(), 1);
        assert_eq!(de[0].name, "de_incorporate");

        // Wrong jurisdiction → no rules.
        assert!(pack
            .rules_for(&qi("uk"), &qi("entity.incorporate"))
            .is_empty());
    }

    #[test]
    fn pack_is_content_addressed_and_deterministic() {
        let mk = || {
            compile(
                "did:mass:curator",
                "1.0.0",
                vec![admitted(
                    "r",
                    Some(scope(&["sc"], &[OperationKindScope::All])),
                    body("Compliant"),
                )],
            )
            .unwrap()
        };
        let p1 = mk();
        let p2 = mk();
        assert_eq!(p1.digest, p2.digest, "same input → same digest");
        assert_eq!(p1.version.content_digest, p1.digest);
        assert_eq!(p1.digest.len(), 64);
        // The compiled rule's hash is the body hash.
        assert_eq!(p1.rules[0].rule_hash, p1.rules[0].body.term_hash);
    }

    #[test]
    fn different_curator_produces_different_pack_digest() {
        let rule = || {
            vec![admitted(
                "r",
                Some(scope(&["sc"], &[OperationKindScope::All])),
                body("Compliant"),
            )]
        };
        let p1 = compile("did:mass:curator-a", "1.0.0", rule()).unwrap();
        let p2 = compile("did:mass:curator-b", "1.0.0", rule()).unwrap();
        assert_ne!(
            p1.digest, p2.digest,
            "different curators are distinct artifacts (I-2)"
        );
    }

    // ── signature verification fail-closed ────────────────────────────────

    struct AcceptAll;
    impl CuratorVerifier for AcceptAll {
        fn verify(&self, _did: &str, _digest: &str, _sig: &CuratorSignature) -> Result<(), String> {
            Ok(())
        }
    }
    struct RejectAll;
    impl CuratorVerifier for RejectAll {
        fn verify(&self, _did: &str, _digest: &str, _sig: &CuratorSignature) -> Result<(), String> {
            Err("not a recognized curator".to_string())
        }
    }

    fn signed_pack() -> Pack {
        compile(
            "did:mass:curator",
            "1.0.0",
            vec![admitted(
                "r",
                Some(scope(&["sc"], &[OperationKindScope::All])),
                body("Compliant"),
            )],
        )
        .unwrap()
        .with_signature(CuratorSignature {
            scheme: "hybrid-ed25519-mldsa65-slhdsa".to_string(),
            signature_hex: "ab".repeat(32),
        })
    }

    #[test]
    fn unsigned_pack_fails_verification_closed() {
        let pack = compile(
            "did:mass:curator",
            "1.0.0",
            vec![admitted(
                "r",
                Some(scope(&["sc"], &[OperationKindScope::All])),
                body("Compliant"),
            )],
        )
        .unwrap();
        assert_eq!(
            pack.verify(&AcceptAll).unwrap_err(),
            PackVerifyError::Unsigned
        );
    }

    #[test]
    fn signed_pack_verifies_with_accepting_verifier() {
        assert!(signed_pack().verify(&AcceptAll).is_ok());
    }

    #[test]
    fn signed_pack_rejected_by_rejecting_verifier() {
        assert!(matches!(
            signed_pack().verify(&RejectAll).unwrap_err(),
            PackVerifyError::SignatureRejected(_)
        ));
    }

    #[test]
    fn tampered_pack_digest_fails_verification() {
        let mut pack = signed_pack();
        // Tamper with a rule's legal_basis after the digest was computed.
        pack.rules[0].legal_basis = "tampered".to_string();
        assert!(matches!(
            pack.verify(&AcceptAll).unwrap_err(),
            PackVerifyError::DigestMismatch { .. }
        ));
    }

    // ── obligation extraction is captured ─────────────────────────────────

    #[test]
    fn compiled_rule_captures_obligations() {
        // A match expression with a non-exhaustive-looking body extracts at
        // least one obligation via lex-core's extractor.
        let rule_body = Term::Defeasible(DefeasibleRule {
            name: Ident::new("late_filing"),
            base_ty: Box::new(Term::Sort(Sort::Prop)),
            base_body: Box::new(Term::Constant(qi("report_required"))),
            exceptions: vec![Exception {
                guard: Box::new(Term::Constant(qi("is_market_maker"))),
                body: Box::new(Term::Constant(qi("mm_exception"))),
                priority: Some(10),
                authority: None,
            }],
            lattice: None,
            applies_to: Some(scope(&["sc"], &[OperationKindScope::All])),
        });
        let pack = compile(
            "did:mass:curator",
            "1.0.0",
            vec![admitted(
                "late_filing",
                Some(scope(&["sc"], &[OperationKindScope::All])),
                rule_body,
            )],
        )
        .expect("compile should succeed");
        // The defeasible rule produces a DefeasibleResolution obligation.
        assert!(
            !pack.rules[0].obligations.is_empty(),
            "defeasible rule should emit at least one obligation"
        );
    }
}
