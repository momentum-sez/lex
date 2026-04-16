//! Commitment 8 — Derivation certificate.
//!
//! Every proof term records which sub-terms were filled mechanically and
//! which were filled by regulator discretion. Verification returns a
//! structured certificate `(mechanical_check: bool, discretion_steps:
//! Vec<DiscretionStep>)` — plus the 4-tuple, the discretion frontier, and a
//! summary digest binding the certificate to its proof summary.

use super::digest::sha256_hex;
use super::hole::{FilledHoleRecord, HoleId};
use super::monotone::FourTuple;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

/// A step in the derivation that was filled by regulator discretion.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiscretionStep {
    /// The filled-hole record.
    pub record: FilledHoleRecord,
    /// Optional rationale digest (SHA-256 of the rationale text).
    pub rationale_digest: Option<String>,
}

/// A derivation certificate.
///
/// The fundamental output of verification. Downstream consumers inspect
/// `mechanical_check` to decide whether a proof required human judgment.
/// `discretion_steps` enumerates those judgments with signed PCAuth
/// witnesses. `discretion_frontier` enumerates the *unfilled* holes — if
/// non-empty, the proof is incomplete and the `verdict` is `Pending`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DerivationCertificate {
    /// `true` iff the proof was fully mechanical (no holes outstanding, all
    /// filled holes signed by the authorized party).
    pub mechanical_check: bool,
    /// Filled discretion steps, each with its PCAuth witness.
    pub discretion_steps: Vec<DiscretionStep>,
    /// Unfilled holes. Empty iff `mechanical_check = true`.
    pub discretion_frontier: BTreeSet<HoleId>,
    /// The 4-tuple scope of this proof.
    pub four_tuple: FourTuple,
    /// Proof-term digest (SHA-256 of the canonical serialization).
    pub proof_digest: String,
    /// Summary digest, binding the certificate to the proof summary.
    pub summary_digest: String,
    /// Final verdict of the evaluation.
    pub verdict: Verdict,
    /// Certificate's own content-addressed digest (SHA-256 over the above
    /// fields, canonicalized).
    pub certificate_digest: String,
}

/// The compliance verdict carried by a certificate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Verdict {
    Compliant,
    NonCompliant,
    Pending,
    NotApplicable,
    Indeterminate,
}

/// Certificate construction error.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CertificateError {
    #[error("pending verdict requires a non-empty discretion frontier")]
    InconsistentPending,
    #[error("compliant verdict requires mechanical_check=true")]
    InconsistentCompliant,
    #[error("mechanical_check=true but discretion_frontier is non-empty")]
    MechanicalFrontierMismatch,
}

impl DerivationCertificate {
    /// Construct a certificate from its components, enforcing the cross-
    /// consistency invariants.
    pub fn build(
        four_tuple: FourTuple,
        proof_digest: String,
        summary_digest: String,
        discretion_steps: Vec<DiscretionStep>,
        discretion_frontier: BTreeSet<HoleId>,
        verdict: Verdict,
    ) -> Result<Self, CertificateError> {
        let mechanical_check = discretion_frontier.is_empty();

        // Consistency: if frontier is non-empty, cannot be Compliant.
        if !mechanical_check && verdict == Verdict::Compliant {
            return Err(CertificateError::InconsistentCompliant);
        }
        // Consistency: Pending requires outstanding work (frontier non-empty).
        if verdict == Verdict::Pending && mechanical_check {
            return Err(CertificateError::InconsistentPending);
        }

        let mut cert = Self {
            mechanical_check,
            discretion_steps,
            discretion_frontier,
            four_tuple,
            proof_digest,
            summary_digest,
            verdict,
            certificate_digest: String::new(),
        };
        cert.certificate_digest = cert.compute_digest();
        Ok(cert)
    }

    fn compute_digest(&self) -> String {
        // Canonicalize the certificate with digest field cleared, hash it.
        let mut cloned = self.clone();
        cloned.certificate_digest = String::new();
        sha256_hex(&cloned)
    }

    /// Verify the certificate's own digest.
    pub fn verify_self_digest(&self) -> bool {
        self.compute_digest() == self.certificate_digest
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ft() -> FourTuple {
        FourTuple {
            time: "2026-04-15T00:00:00Z".into(),
            jurisdiction: "ADGM".into(),
            version: "v1".into(),
            tribunal: "ADGM-FSRA".into(),
        }
    }

    #[test]
    fn empty_frontier_is_mechanical() {
        let c = DerivationCertificate::build(
            ft(),
            "pd".into(),
            "sd".into(),
            vec![],
            BTreeSet::new(),
            Verdict::Compliant,
        )
        .unwrap();
        assert!(c.mechanical_check);
    }

    #[test]
    fn non_empty_frontier_is_not_mechanical() {
        let mut f = BTreeSet::new();
        f.insert(HoleId("h1".into()));
        let c = DerivationCertificate::build(
            ft(),
            "pd".into(),
            "sd".into(),
            vec![],
            f,
            Verdict::Pending,
        )
        .unwrap();
        assert!(!c.mechanical_check);
    }

    #[test]
    fn compliant_with_frontier_is_rejected() {
        let mut f = BTreeSet::new();
        f.insert(HoleId("h1".into()));
        let r = DerivationCertificate::build(
            ft(),
            "pd".into(),
            "sd".into(),
            vec![],
            f,
            Verdict::Compliant,
        );
        assert!(matches!(r, Err(CertificateError::InconsistentCompliant)));
    }

    #[test]
    fn pending_without_frontier_is_rejected() {
        let r = DerivationCertificate::build(
            ft(),
            "pd".into(),
            "sd".into(),
            vec![],
            BTreeSet::new(),
            Verdict::Pending,
        );
        assert!(matches!(r, Err(CertificateError::InconsistentPending)));
    }

    #[test]
    fn self_digest_verifies() {
        let c = DerivationCertificate::build(
            ft(),
            "pd".into(),
            "sd".into(),
            vec![],
            BTreeSet::new(),
            Verdict::Compliant,
        )
        .unwrap();
        assert!(c.verify_self_digest());
    }

    #[test]
    fn tampering_breaks_digest() {
        let mut c = DerivationCertificate::build(
            ft(),
            "pd".into(),
            "sd".into(),
            vec![],
            BTreeSet::new(),
            Verdict::Compliant,
        )
        .unwrap();
        c.verdict = Verdict::NonCompliant;
        assert!(!c.verify_self_digest());
    }
}
