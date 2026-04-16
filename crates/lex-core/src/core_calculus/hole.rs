//! Commitment 4 — Typed discretion holes (HEADLINE PRIMITIVE).
//!
//! A typed discretion hole is a first-class term `? : T @ Authority` marking
//! the precise point where mechanical computation must halt and human
//! judgment of type `T` must be supplied by a party with `Authority`. A
//! discretion hole is NOT a missing implementation. It is the formal
//! boundary between computable predicates and judgment-requiring standards.
//!
//! Lex makes the distinction visible in the type system so that AI agents
//! can navigate it safely. The agent evaluates everything the type system
//! permits, then halts at exactly the points where the law demands human
//! judgment.
//!
//! See `docs/frontier-work/08-lex-core-calculus.md` §4 for the three worked
//! examples:
//! - "fit and proper person" (ADGM FSRA)
//! - "material adverse change" (loan covenant)
//! - "adequate systems and controls" (Basel III)

use super::monotone::FourTuple;
use crate::ast::Term;
use serde::{Deserialize, Serialize};
use std::marker::PhantomData;

// ---------------------------------------------------------------------------
// Authority — who may fill a hole
// ---------------------------------------------------------------------------

/// An authority authorized to fill a discretion hole.
///
/// Authorities are opaque identifiers — in production they resolve to
/// PCAuth-signed keys. The `validate` method is called by the verifier to
/// check that a supplied filler's PCAuth witness satisfies the authority.
pub trait Authority {
    /// Stable identifier for this authority (used in certificates).
    fn id(&self) -> &str;

    /// Validate a PCAuth witness against this authority.
    fn validate(&self, witness: &PCAuthWitness) -> Result<(), AuthorityError>;
}

/// A concrete named authority (e.g., "ADGM-FSRA").
///
/// For production use, implement [`Authority`] on a richer type that resolves
/// to a signed key hierarchy.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NamedAuthority {
    pub id: String,
    pub public_key_hash: String,
}

impl Authority for NamedAuthority {
    fn id(&self) -> &str {
        &self.id
    }

    fn validate(&self, witness: &PCAuthWitness) -> Result<(), AuthorityError> {
        if witness.signer_public_key_hash != self.public_key_hash {
            return Err(AuthorityError::SignerMismatch {
                expected: self.public_key_hash.clone(),
                got: witness.signer_public_key_hash.clone(),
            });
        }
        if witness.signature.is_empty() {
            return Err(AuthorityError::MissingSignature);
        }
        Ok(())
    }
}

/// A PCAuth witness — a signed assertion from an authorized party.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PCAuthWitness {
    /// Signer public key hash.
    pub signer_public_key_hash: String,
    /// Signature bytes (opaque; could be Ed25519 || ML-DSA-65 || SLH-DSA).
    pub signature: Vec<u8>,
    /// Stratum-0 time at which the signature was emitted.
    pub signed_at: String,
    /// Cryptographic epoch, per PLATONIC-IDEAL §5.3.
    pub cryptographic_epoch: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum AuthorityError {
    #[error("signer mismatch: expected {expected}, got {got}")]
    SignerMismatch { expected: String, got: String },
    #[error("missing signature")]
    MissingSignature,
    #[error("signature verification failed: {reason}")]
    SignatureInvalid { reason: String },
    #[error("scope constraint violated: {detail}")]
    ScopeViolation { detail: String },
}

// ---------------------------------------------------------------------------
// ScopeConstraint — narrowing the admissible scope of a hole
// ---------------------------------------------------------------------------

/// A scope constraint on a discretion hole.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct ScopeConstraint {
    /// Corridor the hole is scoped to (e.g., "ADGM↔Seychelles").
    pub corridor: Option<String>,
    /// Time window (ISO 8601 strings, inclusive).
    pub time_window: Option<(String, String)>,
    /// Jurisdiction.
    pub jurisdiction: Option<String>,
    /// Entity class (free-form).
    pub entity_class: Option<String>,
}

impl ScopeConstraint {
    pub fn is_empty(&self) -> bool {
        self.corridor.is_none()
            && self.time_window.is_none()
            && self.jurisdiction.is_none()
            && self.entity_class.is_none()
    }
}

// ---------------------------------------------------------------------------
// HoleId — content-addressed hole identifier
// ---------------------------------------------------------------------------

/// A content-addressed identifier for a hole, used in the discretion frontier.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Serialize, Deserialize)]
pub struct HoleId(pub String);

impl HoleId {
    /// Derive a `HoleId` from the declared name and scope. A stable digest
    /// is used so re-evaluation produces the same identifier.
    pub fn derive(name: &str, scope: &ScopeConstraint) -> Self {
        // Use SHA-256 over the canonical serialization. The exact hash is an
        // implementation detail; the important property is determinism.
        HoleId(super::digest::sha256_hex(&(name, scope)))
    }
}

// ---------------------------------------------------------------------------
// Hole — the headline primitive
// ---------------------------------------------------------------------------

/// A typed discretion hole `? : T @ A`.
///
/// `T` is the *type* of judgment demanded. `A` is the *authority* that may
/// supply it. Both are visible in the type system — an agent statically
/// knows what kind of filler it needs and from whom.
///
/// Elaboration preserves holes: a term containing `Hole<T, A>` type-checks
/// as if the hole inhabited `T`, but the verifier carries the hole forward
/// and records it in the discretion frontier.
#[derive(Debug, Clone)]
pub struct Hole<T, A: Authority> {
    id: HoleId,
    name: Option<String>,
    authority: A,
    scope: ScopeConstraint,
    /// The declared type, as an AST term. The phantom `T` encodes the type
    /// in the Rust type system for compile-time propagation.
    pub declared_ty: Term,
    _judgment: PhantomData<fn() -> T>,
}

impl<T, A: Authority> Hole<T, A> {
    /// Declare a new discretion hole.
    pub fn new(
        name: Option<&str>,
        authority: A,
        scope: ScopeConstraint,
        declared_ty: Term,
    ) -> Self {
        let id = HoleId::derive(name.unwrap_or(""), &scope);
        Self {
            id,
            name: name.map(str::to_string),
            authority,
            scope,
            declared_ty,
            _judgment: PhantomData,
        }
    }

    pub fn id(&self) -> &HoleId {
        &self.id
    }

    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    pub fn authority(&self) -> &A {
        &self.authority
    }

    pub fn scope(&self) -> &ScopeConstraint {
        &self.scope
    }

    /// Fill this hole, producing a [`HoleFill<T, A>`] term.
    ///
    /// The `filler` is the concrete judgment supplied by the authority.
    /// The `witness` is a PCAuth attestation; the authority's `validate`
    /// method is called to check it.
    pub fn fill(self, filler: T, witness: PCAuthWitness) -> Result<HoleFill<T, A>, AuthorityError>
    where
        T: serde::Serialize,
    {
        self.authority.validate(&witness)?;
        Ok(HoleFill {
            hole_id: self.id,
            filler,
            witness,
            authority: self.authority,
            scope: self.scope,
            declared_ty: self.declared_ty,
            _judgment: PhantomData,
        })
    }
}

// ---------------------------------------------------------------------------
// HoleFill — a filled hole
// ---------------------------------------------------------------------------

/// A filled discretion hole.
///
/// Carries the filler, the PCAuth witness, and the content-addressed hole
/// identifier. Certificates embed `HoleFill`s in their
/// `discretion_steps`.
#[derive(Debug, Clone)]
pub struct HoleFill<T, A: Authority> {
    hole_id: HoleId,
    filler: T,
    witness: PCAuthWitness,
    authority: A,
    scope: ScopeConstraint,
    pub declared_ty: Term,
    _judgment: PhantomData<fn() -> T>,
}

impl<T, A: Authority> HoleFill<T, A> {
    pub fn hole_id(&self) -> &HoleId {
        &self.hole_id
    }

    pub fn filler(&self) -> &T {
        &self.filler
    }

    pub fn witness(&self) -> &PCAuthWitness {
        &self.witness
    }

    pub fn authority(&self) -> &A {
        &self.authority
    }

    pub fn scope(&self) -> &ScopeConstraint {
        &self.scope
    }

    /// Convert to a [`FilledHoleRecord`] for embedding in a certificate.
    pub fn to_record(&self, four_tuple: FourTuple) -> FilledHoleRecord
    where
        T: serde::Serialize,
    {
        FilledHoleRecord {
            hole_id: self.hole_id.clone(),
            authority_id: self.authority.id().to_string(),
            scope: self.scope.clone(),
            filler_digest: super::digest::sha256_hex(&self.filler),
            witness: self.witness.clone(),
            four_tuple,
        }
    }
}

/// Serializable record of a filled hole, embedded in a certificate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FilledHoleRecord {
    pub hole_id: HoleId,
    pub authority_id: String,
    pub scope: ScopeConstraint,
    pub filler_digest: String,
    pub witness: PCAuthWitness,
    pub four_tuple: FourTuple,
}

// ---------------------------------------------------------------------------
// HoleContext — ambient context for hole elaboration
// ---------------------------------------------------------------------------

/// Ambient context carried by the elaborator and verifier when handling
/// holes.
#[derive(Debug, Clone, Default)]
pub struct HoleContext {
    /// Currently unfilled holes in this proof's frontier.
    pub frontier: std::collections::BTreeSet<HoleId>,
    /// Filled holes, with their records.
    pub filled: Vec<FilledHoleRecord>,
}

impl HoleContext {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn record_unfilled(&mut self, id: HoleId) {
        self.frontier.insert(id);
    }

    pub fn record_filled(&mut self, record: FilledHoleRecord) {
        self.frontier.remove(&record.hole_id);
        self.filled.push(record);
    }

    pub fn is_mechanical(&self) -> bool {
        self.frontier.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{QualIdent, Term};

    fn adgm_fsra() -> NamedAuthority {
        NamedAuthority {
            id: "ADGM-FSRA".into(),
            public_key_hash: "pk:adgm-fsra".into(),
        }
    }

    fn witness_ok() -> PCAuthWitness {
        PCAuthWitness {
            signer_public_key_hash: "pk:adgm-fsra".into(),
            signature: vec![1, 2, 3],
            signed_at: "2026-04-15T00:00:00Z".into(),
            cryptographic_epoch: 1,
        }
    }

    fn witness_bad_signer() -> PCAuthWitness {
        PCAuthWitness {
            signer_public_key_hash: "pk:wrong".into(),
            signature: vec![1, 2, 3],
            signed_at: "2026-04-15T00:00:00Z".into(),
            cryptographic_epoch: 1,
        }
    }

    fn witness_no_sig() -> PCAuthWitness {
        PCAuthWitness {
            signer_public_key_hash: "pk:adgm-fsra".into(),
            signature: vec![],
            signed_at: "2026-04-15T00:00:00Z".into(),
            cryptographic_epoch: 1,
        }
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    struct FitAndProperJudgment {
        pub fit: bool,
        pub basis: String,
    }

    #[test]
    fn hole_carries_authority_and_scope() {
        let h: Hole<FitAndProperJudgment, _> = Hole::new(
            Some("fit_check"),
            adgm_fsra(),
            ScopeConstraint {
                jurisdiction: Some("ADGM".into()),
                entity_class: Some("Principal".into()),
                ..Default::default()
            },
            Term::Constant(QualIdent::simple("FitAndProperJudgment")),
        );
        assert_eq!(h.authority().id(), "ADGM-FSRA");
        assert_eq!(h.scope().jurisdiction.as_deref(), Some("ADGM"));
        assert_eq!(h.name(), Some("fit_check"));
    }

    #[test]
    fn hole_id_is_deterministic() {
        let scope = ScopeConstraint::default();
        let a = HoleId::derive("x", &scope);
        let b = HoleId::derive("x", &scope);
        assert_eq!(a, b);
        let c = HoleId::derive("y", &scope);
        assert_ne!(a, c);
    }

    #[test]
    fn fill_accepts_valid_witness() {
        let h: Hole<FitAndProperJudgment, _> = Hole::new(
            Some("fit_check"),
            adgm_fsra(),
            ScopeConstraint::default(),
            Term::Constant(QualIdent::simple("FitAndProperJudgment")),
        );
        let filler = FitAndProperJudgment {
            fit: true,
            basis: "on-site inspection".into(),
        };
        let filled = h.fill(filler, witness_ok()).expect("should validate");
        assert!(filled.filler().fit);
        assert_eq!(filled.authority().id(), "ADGM-FSRA");
    }

    #[test]
    fn fill_rejects_wrong_signer() {
        let h: Hole<FitAndProperJudgment, _> = Hole::new(
            Some("fit_check"),
            adgm_fsra(),
            ScopeConstraint::default(),
            Term::Constant(QualIdent::simple("FitAndProperJudgment")),
        );
        let filler = FitAndProperJudgment {
            fit: true,
            basis: "".into(),
        };
        let r = h.fill(filler, witness_bad_signer());
        assert!(matches!(r, Err(AuthorityError::SignerMismatch { .. })));
    }

    #[test]
    fn fill_rejects_missing_signature() {
        let h: Hole<FitAndProperJudgment, _> = Hole::new(
            Some("fit_check"),
            adgm_fsra(),
            ScopeConstraint::default(),
            Term::Constant(QualIdent::simple("FitAndProperJudgment")),
        );
        let filler = FitAndProperJudgment {
            fit: true,
            basis: "".into(),
        };
        let r = h.fill(filler, witness_no_sig());
        assert!(matches!(r, Err(AuthorityError::MissingSignature)));
    }

    #[test]
    fn hole_context_tracks_mechanical_bit() {
        let mut ctx = HoleContext::new();
        assert!(ctx.is_mechanical());
        let id = HoleId("abc".into());
        ctx.record_unfilled(id.clone());
        assert!(!ctx.is_mechanical());
        let rec = FilledHoleRecord {
            hole_id: id.clone(),
            authority_id: "X".into(),
            scope: ScopeConstraint::default(),
            filler_digest: "d".into(),
            witness: witness_ok(),
            four_tuple: FourTuple {
                time: "2026".into(),
                jurisdiction: "X".into(),
                version: "v1".into(),
                tribunal: "X".into(),
            },
        };
        ctx.record_filled(rec);
        assert!(ctx.is_mechanical());
    }

    #[test]
    fn hole_fill_to_record_contains_filler_digest() {
        let h: Hole<FitAndProperJudgment, _> = Hole::new(
            Some("fit_check"),
            adgm_fsra(),
            ScopeConstraint::default(),
            Term::Constant(QualIdent::simple("FitAndProperJudgment")),
        );
        let filler = FitAndProperJudgment {
            fit: true,
            basis: "inspection".into(),
        };
        let filled = h.fill(filler, witness_ok()).unwrap();
        let rec = filled.to_record(FourTuple {
            time: "2026-04-15T00:00:00Z".into(),
            jurisdiction: "ADGM".into(),
            version: "v2026.04.15".into(),
            tribunal: "ADGM-FSRA".into(),
        });
        assert!(!rec.filler_digest.is_empty());
        assert_eq!(rec.authority_id, "ADGM-FSRA");
    }

    #[test]
    fn scope_constraint_default_is_empty() {
        assert!(ScopeConstraint::default().is_empty());
    }

    #[test]
    fn different_scopes_yield_different_hole_ids() {
        let s1 = ScopeConstraint {
            jurisdiction: Some("ADGM".into()),
            ..Default::default()
        };
        let s2 = ScopeConstraint {
            jurisdiction: Some("Seychelles".into()),
            ..Default::default()
        };
        assert_ne!(HoleId::derive("h", &s1), HoleId::derive("h", &s2));
    }
}
