//! Commitment 4 - Typed discretion holes (HEADLINE PRIMITIVE).
//!
//! A typed discretion hole is a first-class term `? : T @ Authority` marking
//! the precise point where mechanical computation must halt and human
//! judgment of type `T` must be supplied by a party with `Authority`. A
//! discretion hole is NOT a missing implementation. It is the formal
//! boundary between computable predicates and judgment-requiring standards.
//!
//! Lex makes the distinction visible in the type system. Evaluation proceeds
//! through the mechanically typed region and suspends exactly where the law
//! demands human judgment.
//!
//! See `docs/frontier-work/08-lex-core-calculus.md` §4 for the three worked
//! examples:
//! - "fit and proper person" (ADGM FSRA)
//! - "material adverse change" (loan covenant)
//! - "adequate systems and controls" (Basel III)

use super::monotone::FourTuple;
use crate::ast::Term;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::marker::PhantomData;

// ---------------------------------------------------------------------------
// Authority - who may fill a hole
// ---------------------------------------------------------------------------

/// An authority authorized to fill a discretion hole.
///
/// Authorities are opaque identifiers - in production they resolve to
/// PCAuth-signed keys. The `validate` method runs a STRUCTURAL precheck
/// only - it verifies the signer-key hash matches and that the signature
/// bytes are non-empty. Structural precheck is NOT cryptographic
/// authentication: it proves nothing about whether the signature actually
/// authenticates the witness. Cryptographic verification is the job of a
/// [`PCAuthVerifier`], and the only fill path that performs it is
/// [`Hole::fill_verified`]. The plain [`Hole::fill`] path runs the
/// structural precheck ONLY and is therefore not, by itself, a
/// cryptographically-admitted fill.
pub trait Authority {
    /// Stable identifier for this authority (used in certificates).
    fn id(&self) -> &str;

    /// The expected signer public-key hash for this authority. Used by a
    /// [`PCAuthVerifier`] to bind the cryptographic check to this
    /// authority's key.
    fn expected_key_hash(&self) -> &str;

    /// Structural precheck of a PCAuth witness against this authority.
    ///
    /// This is NOT cryptographic verification. See [`witness_structural_precheck`]
    /// and [`PCAuthVerifier`] for the full story.
    fn validate(&self, witness: &PCAuthWitness) -> Result<(), AuthorityError>;
}

/// Verifier of cryptographic PCAuth signatures.
///
/// Implementations of this trait perform the actual cryptographic
/// authentication of a [`PCAuthWitness`]. A fill admitted through
/// [`Hole::fill_verified`] runs the supplied verifier and is rejected
/// (fail-closed) if verification fails.
///
/// # Wiring status (no overclaim)
///
/// The only verifier implemented in this crate is [`HmacSha256Verifier`],
/// a real HMAC-SHA256 keyed-MAC check built on the workspace `sha2`
/// dependency. It authenticates a witness against a symmetric key with a
/// constant-time tag comparison. It is genuine cryptographic authentication
/// of an HMAC tag — it is NOT public-key signature verification.
///
/// Asymmetric PCAuth signatures (the `Ed25519 || ML-DSA-65 || SLH-DSA`
/// hybrid named on [`PCAuthWitness::signature`]) are NOT verified anywhere
/// in this crate: lex-core does not depend on an Ed25519 / ML-DSA / SLH-DSA
/// implementation, so no asymmetric-signature `PCAuthVerifier` exists here.
/// A deployment that needs hybrid-PQ signature admission must implement this
/// trait against its own crypto stack and pass it to [`Hole::fill_verified`].
/// Until such a verifier is supplied, an asymmetric signature carried on a
/// witness is treated as opaque bytes by the structural precheck and is
/// never cryptographically authenticated.
pub trait PCAuthVerifier {
    /// Cryptographically authenticate `witness` against the public-key (or
    /// keyed-MAC key) hash `expected_key_hash`.
    ///
    /// Implementations must run in time independent of the secret-dependent
    /// comparison (constant-time tag/equality check) and must surface a
    /// typed [`AuthorityError`] on any failure — never a silent pass.
    fn verify(
        &self,
        witness: &PCAuthWitness,
        expected_key_hash: &str,
    ) -> Result<(), AuthorityError>;
}

/// Structural precheck of a PCAuth witness.
///
/// Checks only that the signer public-key hash equals `expected_key_hash`
/// and that the signature bytes are non-empty. Cryptographic signature
/// verification happens at the outer proof-checker boundary - it is
/// performed by a [`PCAuthVerifier`] at the elaboration-certificate
/// boundary, NOT inside the typing rule.
pub fn witness_structural_precheck(
    witness: &PCAuthWitness,
    expected_key_hash: &str,
) -> Result<(), AuthorityError> {
    if witness.signer_public_key_hash != expected_key_hash {
        return Err(AuthorityError::SignerMismatch {
            expected: expected_key_hash.to_string(),
            got: witness.signer_public_key_hash.clone(),
        });
    }
    if witness.signature.is_empty() {
        return Err(AuthorityError::MissingSignature);
    }
    Ok(())
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

    fn expected_key_hash(&self) -> &str {
        &self.public_key_hash
    }

    /// Structural precheck only. Cryptographic signature verification
    /// happens at the outer proof-checker boundary, not inside the typing
    /// rule.
    fn validate(&self, witness: &PCAuthWitness) -> Result<(), AuthorityError> {
        witness_structural_precheck(witness, &self.public_key_hash)
    }
}

// ---------------------------------------------------------------------------
// HmacSha256Verifier - a real (symmetric) PCAuthVerifier
// ---------------------------------------------------------------------------

/// A real [`PCAuthVerifier`] that authenticates a witness with HMAC-SHA256.
///
/// This is genuine cryptographic authentication, built on the workspace
/// `sha2` dependency: the verifier recomputes `HMAC-SHA256(key, message)`
/// over the witness's authenticated fields and compares it against
/// [`PCAuthWitness::signature`] in constant time. It is a SYMMETRIC keyed
/// MAC — both the signer and this verifier hold the same secret `key`. It is
/// deliberately NOT presented as public-key signature verification; see the
/// [`PCAuthVerifier`] trait docs for the precise (un)wiring status of
/// asymmetric Ed25519 / ML-DSA-65 / SLH-DSA signatures.
///
/// The `expected_key_hash` passed to [`PCAuthVerifier::verify`] must equal
/// `SHA-256(key)` rendered as lowercase hex; this binds the symmetric key to
/// the authority's advertised key hash so a witness minted under a different
/// key is rejected before the MAC is even checked.
pub struct HmacSha256Verifier {
    key: Vec<u8>,
}

impl HmacSha256Verifier {
    /// Construct a verifier from the shared secret `key`.
    pub fn new(key: impl Into<Vec<u8>>) -> Self {
        Self { key: key.into() }
    }

    /// The key hash this verifier expects an authority to advertise:
    /// `SHA-256(key)` as lowercase hex. An [`Authority::expected_key_hash`]
    /// must equal this for [`PCAuthVerifier::verify`] to proceed.
    pub fn key_hash(&self) -> String {
        super::digest::sha256_hex_bytes(&self.key)
    }

    /// The authenticated message for a witness: the canonical concatenation
    /// of the fields the MAC binds. The signature field itself is excluded
    /// (it is the tag), but every other field is authenticated so a witness
    /// cannot be replayed under a different signer / time / epoch.
    fn authenticated_message(witness: &PCAuthWitness) -> Vec<u8> {
        let mut msg = Vec::new();
        // Length-prefix each field so distinct field boundaries cannot be
        // shifted (canonical, unambiguous encoding).
        for field in [
            witness.signer_public_key_hash.as_bytes(),
            witness.signed_at.as_bytes(),
        ] {
            msg.extend_from_slice(&(field.len() as u64).to_be_bytes());
            msg.extend_from_slice(field);
        }
        msg.extend_from_slice(&witness.cryptographic_epoch.to_be_bytes());
        msg
    }

    /// Compute `HMAC-SHA256(key, message)` using `sha2` directly (HMAC is
    /// defined purely in terms of the hash function; no `hmac` crate
    /// dependency is required).
    fn hmac_sha256(key: &[u8], message: &[u8]) -> [u8; 32] {
        const BLOCK: usize = 64; // SHA-256 block size in bytes.
        // Keys longer than the block size are first hashed.
        let mut key_block = [0u8; BLOCK];
        if key.len() > BLOCK {
            let mut h = Sha256::new();
            h.update(key);
            let digest = h.finalize();
            key_block[..32].copy_from_slice(&digest);
        } else {
            key_block[..key.len()].copy_from_slice(key);
        }

        let mut ipad = [0x36u8; BLOCK];
        let mut opad = [0x5cu8; BLOCK];
        for i in 0..BLOCK {
            ipad[i] ^= key_block[i];
            opad[i] ^= key_block[i];
        }

        // inner = H(ipad || message)
        let mut inner = Sha256::new();
        inner.update(ipad);
        inner.update(message);
        let inner_digest = inner.finalize();

        // outer = H(opad || inner)
        let mut outer = Sha256::new();
        outer.update(opad);
        outer.update(inner_digest);
        let out = outer.finalize();

        let mut tag = [0u8; 32];
        tag.copy_from_slice(&out);
        tag
    }
}

/// Constant-time byte-slice equality. Returns `true` iff `a == b`. Runs in
/// time dependent only on `a.len()` (and short-circuits ONLY on the length
/// mismatch, which is not secret-dependent for a fixed-size MAC tag).
fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff: u8 = 0;
    for (x, y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}

impl PCAuthVerifier for HmacSha256Verifier {
    /// Authenticate the witness's HMAC-SHA256 tag.
    ///
    /// Fail-closed: returns [`AuthorityError`] if the key hash does not bind
    /// to this verifier's key, if the signature (tag) is empty, or if the
    /// recomputed MAC does not match the witness tag in constant time.
    fn verify(
        &self,
        witness: &PCAuthWitness,
        expected_key_hash: &str,
    ) -> Result<(), AuthorityError> {
        // Bind the symmetric key to the authority's advertised key hash.
        if !constant_time_eq(self.key_hash().as_bytes(), expected_key_hash.as_bytes()) {
            return Err(AuthorityError::SignerMismatch {
                expected: expected_key_hash.to_string(),
                got: self.key_hash(),
            });
        }
        // The witness must also claim the same signer key hash.
        if !constant_time_eq(
            witness.signer_public_key_hash.as_bytes(),
            expected_key_hash.as_bytes(),
        ) {
            return Err(AuthorityError::SignerMismatch {
                expected: expected_key_hash.to_string(),
                got: witness.signer_public_key_hash.clone(),
            });
        }
        if witness.signature.is_empty() {
            return Err(AuthorityError::MissingSignature);
        }
        let message = Self::authenticated_message(witness);
        let expected_tag = Self::hmac_sha256(&self.key, &message);
        if !constant_time_eq(&expected_tag, &witness.signature) {
            return Err(AuthorityError::SignatureInvalid {
                reason: "HMAC-SHA256 tag mismatch".to_string(),
            });
        }
        Ok(())
    }
}

/// A PCAuth witness - a signed assertion from an authorized party.
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
// ScopeConstraint - narrowing the admissible scope of a hole
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
// HoleId - content-addressed hole identifier
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
// Hole - the headline primitive
// ---------------------------------------------------------------------------

/// A typed discretion hole `? : T @ A`.
///
/// `T` is the *type* of judgment demanded. `A` is the *authority* that may
/// supply it. Both are visible in the type system, so a verifier knows what
/// kind of filler is required and from whom.
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

    /// Fill this hole with a STRUCTURAL precheck only.
    ///
    /// The `filler` is the concrete judgment supplied by the authority.
    /// The `witness` is a PCAuth attestation; the authority's
    /// [`Authority::validate`] STRUCTURAL precheck is run (signer-key-hash
    /// match + non-empty signature bytes).
    ///
    /// # This does NOT cryptographically authenticate the witness.
    ///
    /// `validate` checks the *shape* of the witness, not the *validity* of
    /// its signature. A `HoleFill` produced here is therefore not a
    /// cryptographically-admitted fill — it asserts only that a
    /// correctly-shaped attestation naming the right key was presented. To
    /// admit a fill into a proof under cryptographic authentication, use
    /// [`Hole::fill_verified`] with a [`PCAuthVerifier`]; that path is
    /// fail-closed on verification failure.
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

    /// Fill this hole with FULL cryptographic verification — fail-closed.
    ///
    /// Runs the structural precheck ([`Authority::validate`]) AND then asks
    /// the supplied [`PCAuthVerifier`] to cryptographically authenticate the
    /// witness against the authority's [`Authority::expected_key_hash`]. The
    /// fill is admitted ONLY if both succeed; any structural or
    /// cryptographic failure returns a typed [`AuthorityError`] and produces
    /// no `HoleFill`.
    ///
    /// This is the cryptographically-admitting fill path. Prefer it over
    /// [`Hole::fill`] wherever a verifier is available; reserve plain `fill`
    /// for contexts that explicitly only require the structural shape check
    /// and that do not admit the fill into a proof.
    pub fn fill_verified<V: PCAuthVerifier>(
        self,
        filler: T,
        witness: PCAuthWitness,
        verifier: &V,
    ) -> Result<HoleFill<T, A>, AuthorityError>
    where
        T: serde::Serialize,
    {
        // Structural precheck first (cheap, shape-only).
        self.authority.validate(&witness)?;
        // Then the real cryptographic check, bound to this authority's key.
        verifier.verify(&witness, self.authority.expected_key_hash())?;
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
// HoleFill - a filled hole
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
// HoleContext - ambient context for hole elaboration
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

    // -----------------------------------------------------------------
    // oracle-crypto-unimplemented regression — PCAuthVerifier must do
    // real cryptographic authentication, and fill_verified must be
    // fail-closed. Plain fill is structural-only and must not pretend to
    // verify.
    // -----------------------------------------------------------------

    /// An authority whose advertised key hash matches a given HMAC key, so
    /// `fill_verified` can bind the verifier to it.
    fn hmac_authority(verifier: &HmacSha256Verifier) -> NamedAuthority {
        NamedAuthority {
            id: "HMAC-AUTH".into(),
            public_key_hash: verifier.key_hash(),
        }
    }

    /// Mint a witness carrying a VALID HMAC-SHA256 tag for `verifier`'s key.
    fn witness_hmac_valid(verifier: &HmacSha256Verifier) -> PCAuthWitness {
        let mut w = PCAuthWitness {
            signer_public_key_hash: verifier.key_hash(),
            signature: vec![],
            signed_at: "2026-04-15T00:00:00Z".into(),
            cryptographic_epoch: 1,
        };
        let msg = HmacSha256Verifier::authenticated_message(&w);
        w.signature = HmacSha256Verifier::hmac_sha256(&verifier.key, &msg).to_vec();
        w
    }

    #[test]
    fn hmac_verifier_accepts_valid_tag() {
        let v = HmacSha256Verifier::new(b"super-secret-key".to_vec());
        let w = witness_hmac_valid(&v);
        assert!(v.verify(&w, &v.key_hash()).is_ok());
    }

    #[test]
    fn hmac_verifier_rejects_tampered_field() {
        let v = HmacSha256Verifier::new(b"super-secret-key".to_vec());
        let mut w = witness_hmac_valid(&v);
        // Tamper an authenticated field after the tag was computed.
        w.cryptographic_epoch = 2;
        assert!(matches!(
            v.verify(&w, &v.key_hash()),
            Err(AuthorityError::SignatureInvalid { .. })
        ));
    }

    #[test]
    fn hmac_verifier_rejects_tampered_tag() {
        let v = HmacSha256Verifier::new(b"super-secret-key".to_vec());
        let mut w = witness_hmac_valid(&v);
        w.signature[0] ^= 0xff; // Flip a bit in the tag.
        assert!(matches!(
            v.verify(&w, &v.key_hash()),
            Err(AuthorityError::SignatureInvalid { .. })
        ));
    }

    #[test]
    fn hmac_verifier_rejects_wrong_key() {
        let signer = HmacSha256Verifier::new(b"real-key".to_vec());
        let attacker = HmacSha256Verifier::new(b"forged-key".to_vec());
        // Witness was MAC'd with the signer's key but claims the signer's
        // key hash; the attacker's verifier (different key) must reject when
        // asked to bind to the signer's key hash.
        let w = witness_hmac_valid(&signer);
        assert!(matches!(
            attacker.verify(&w, &signer.key_hash()),
            Err(AuthorityError::SignerMismatch { .. })
        ));
    }

    #[test]
    fn hmac_verifier_rejects_empty_signature() {
        let v = HmacSha256Verifier::new(b"k".to_vec());
        let w = PCAuthWitness {
            signer_public_key_hash: v.key_hash(),
            signature: vec![],
            signed_at: "2026-04-15T00:00:00Z".into(),
            cryptographic_epoch: 1,
        };
        assert!(matches!(
            v.verify(&w, &v.key_hash()),
            Err(AuthorityError::MissingSignature)
        ));
    }

    #[test]
    fn fill_verified_admits_valid_witness() {
        let v = HmacSha256Verifier::new(b"fill-key".to_vec());
        let auth = hmac_authority(&v);
        let h: Hole<FitAndProperJudgment, _> = Hole::new(
            Some("fit_check"),
            auth,
            ScopeConstraint::default(),
            Term::Constant(QualIdent::simple("FitAndProperJudgment")),
        );
        let filler = FitAndProperJudgment {
            fit: true,
            basis: "verified".into(),
        };
        let w = witness_hmac_valid(&v);
        let filled = h
            .fill_verified(filler, w, &v)
            .expect("valid HMAC witness should be admitted");
        assert!(filled.filler().fit);
    }

    #[test]
    fn fill_verified_is_fail_closed_on_bad_tag() {
        let v = HmacSha256Verifier::new(b"fill-key".to_vec());
        let auth = hmac_authority(&v);
        let h: Hole<FitAndProperJudgment, _> = Hole::new(
            Some("fit_check"),
            auth,
            ScopeConstraint::default(),
            Term::Constant(QualIdent::simple("FitAndProperJudgment")),
        );
        let filler = FitAndProperJudgment {
            fit: true,
            basis: "".into(),
        };
        let mut w = witness_hmac_valid(&v);
        w.signature[0] ^= 0x01; // Corrupt the tag.
        let r = h.fill_verified(filler, w, &v);
        assert!(matches!(
            r,
            Err(AuthorityError::SignatureInvalid { .. })
        ));
    }

    #[test]
    fn fill_verified_rejects_structurally_bad_witness_before_crypto() {
        // A witness whose signer hash doesn't match the authority fails the
        // structural precheck first — fail-closed before the MAC check.
        let v = HmacSha256Verifier::new(b"fill-key".to_vec());
        let auth = hmac_authority(&v);
        let h: Hole<FitAndProperJudgment, _> = Hole::new(
            Some("fit_check"),
            auth,
            ScopeConstraint::default(),
            Term::Constant(QualIdent::simple("FitAndProperJudgment")),
        );
        let filler = FitAndProperJudgment {
            fit: true,
            basis: "".into(),
        };
        let bad = PCAuthWitness {
            signer_public_key_hash: "pk:not-the-authority".into(),
            signature: vec![1, 2, 3],
            signed_at: "2026-04-15T00:00:00Z".into(),
            cryptographic_epoch: 1,
        };
        assert!(matches!(
            h.fill_verified(filler, bad, &v),
            Err(AuthorityError::SignerMismatch { .. })
        ));
    }

    #[test]
    fn constant_time_eq_basic() {
        assert!(constant_time_eq(b"abc", b"abc"));
        assert!(!constant_time_eq(b"abc", b"abd"));
        assert!(!constant_time_eq(b"abc", b"ab"));
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
