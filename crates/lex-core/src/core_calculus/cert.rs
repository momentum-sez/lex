//! Commitment 8 — Derivation certificate.
//!
//! Every proof term records which sub-terms were filled mechanically and
//! which were filled by regulator discretion. Verification returns a
//! structured certificate `(mechanical_check: bool, discretion_steps:
//! Vec<DiscretionStep>)` — plus the 4-tuple, the discretion frontier, and a
//! `summary_digest` that commits the certificate to a [proof summary].
//!
//! [proof summary]: super::summary::ProofSummary
//!
//! # Summary binding — committed, and verifiable
//!
//! A certificate is built before its summary is compiled (the summary is
//! derived *from* the certificate). The `summary_digest` carried here is
//! therefore a **commitment** to the summary that will be compiled, not a value
//! copied from one. The low-level [`DerivationCertificate::build`] accepts that
//! commitment as-is.
//!
//! The commitment is only meaningful if it can be *checked* against the actual
//! summary. Two surfaces make the binding real rather than nominal:
//!
//! - [`DerivationCertificate::verify_summary_binding`] checks that a given
//!   [`ProofSummary`] is the one this certificate commits to (matching
//!   `summary_digest`) AND is a summary of the *same* proof (matching
//!   `proof_digest`). Use it whenever a `(certificate, summary)` pair is
//!   consumed together.
//! - [`DerivationCertificate::build_bound`] builds a certificate *and* verifies
//!   the binding against the summary in one step, failing loud on mismatch, so
//!   a caller that already has the summary cannot mint a certificate whose
//!   committed digest does not match it.
//!
//! [`ProofSummary`]: super::summary::ProofSummary

use super::digest::sha256_hex;
use super::hole::{FilledHoleRecord, HoleId};
use super::monotone::FourTuple;
use super::summary::ProofSummary;
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
    /// Commitment to the proof summary: the SHA-256 `summary_digest` of the
    /// [`ProofSummary`] that summarizes this proof. Checked by
    /// [`DerivationCertificate::verify_summary_binding`].
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
    #[error(
        "summary binding mismatch: certificate commits to summary_digest {expected} \
         but the supplied summary has digest {actual}"
    )]
    SummaryDigestMismatch { expected: String, actual: String },
    #[error(
        "summary binding mismatch: certificate is over proof_digest {expected} \
         but the supplied summary is over proof_digest {actual}"
    )]
    SummaryProofMismatch { expected: String, actual: String },
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

    /// Verify that `summary` is the proof summary this certificate commits to.
    ///
    /// The binding holds iff (1) the summary's own `summary_digest` equals the
    /// `summary_digest` this certificate committed to, and (2) the summary is a
    /// summary of the *same* proof (`proof_digest` matches). Both checks are
    /// required: a digest match alone would not prevent pairing the certificate
    /// with a same-digest summary of a different proof.
    ///
    /// This is the verification that makes the "summary digest binds the
    /// certificate to its proof summary" claim true rather than nominal. It
    /// fails loud (typed error naming the mismatch) on either mismatch.
    pub fn verify_summary_binding(&self, summary: &ProofSummary) -> Result<(), CertificateError> {
        if summary.proof_digest != self.proof_digest {
            return Err(CertificateError::SummaryProofMismatch {
                expected: self.proof_digest.clone(),
                actual: summary.proof_digest.clone(),
            });
        }
        if summary.summary_digest != self.summary_digest {
            return Err(CertificateError::SummaryDigestMismatch {
                expected: self.summary_digest.clone(),
                actual: summary.summary_digest.clone(),
            });
        }
        Ok(())
    }

    /// Build a certificate already bound to a concrete proof summary.
    ///
    /// Unlike [`build`](Self::build), which takes the `summary_digest`
    /// commitment on trust, this constructor takes the actual [`ProofSummary`],
    /// seals `summary_digest` from it (correct by construction), and then
    /// re-verifies the binding via [`verify_summary_binding`]. A summary that is
    /// not over the same proof is rejected fail-loud before any certificate is
    /// minted, so a bound certificate can never carry a digest that does not
    /// match its summary.
    ///
    /// [`verify_summary_binding`]: Self::verify_summary_binding
    pub fn build_bound(
        four_tuple: FourTuple,
        proof_digest: String,
        summary: &ProofSummary,
        discretion_steps: Vec<DiscretionStep>,
        discretion_frontier: BTreeSet<HoleId>,
        verdict: Verdict,
    ) -> Result<Self, CertificateError> {
        // Reject a summary that does not belong to this proof up front; the
        // digest is meaningless across proofs.
        if summary.proof_digest != proof_digest {
            return Err(CertificateError::SummaryProofMismatch {
                expected: proof_digest,
                actual: summary.proof_digest.clone(),
            });
        }
        // Seal the commitment from the summary itself — correct by construction.
        let cert = Self::build(
            four_tuple,
            proof_digest,
            summary.summary_digest.clone(),
            discretion_steps,
            discretion_frontier,
            verdict,
        )?;
        // Belt-and-suspenders: the binding must now verify.
        cert.verify_summary_binding(summary)?;
        Ok(cert)
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

    // ── Summary binding (LEX-2) ─────────────────────────────────────────
    // WHY: the certificate's summary_digest claims to "bind the certificate to
    // its proof summary". A claimed binding that is never checked is nominal.
    // These tests prove the binding is real: a summary the certificate commits
    // to verifies; a tampered or foreign summary is rejected fail-loud.

    use super::super::summary::compile_summary;

    /// Compile a real summary over the given proof digest, then build a
    /// certificate bound to it via `build_bound`.
    fn bound_cert_and_summary() -> (DerivationCertificate, super::super::summary::ProofSummary) {
        // A provisional cert just to derive a summary from (compile_summary
        // copies proof_digest + verdict + frontier off the cert).
        let provisional = DerivationCertificate::build(
            ft(),
            "proof-XYZ".into(),
            "placeholder".into(),
            vec![],
            BTreeSet::new(),
            Verdict::Compliant,
        )
        .unwrap();
        let summary = compile_summary(&provisional, vec!["ExhaustiveMatch".to_string()], &[]);
        // Now build the real, bound certificate from that summary.
        let cert = DerivationCertificate::build_bound(
            ft(),
            "proof-XYZ".into(),
            &summary,
            vec![],
            BTreeSet::new(),
            Verdict::Compliant,
        )
        .unwrap();
        (cert, summary)
    }

    #[test]
    fn build_bound_seals_summary_digest_from_summary() {
        let (cert, summary) = bound_cert_and_summary();
        // The certificate's committed digest equals the summary's own digest.
        assert_eq!(cert.summary_digest, summary.summary_digest);
        assert!(!cert.summary_digest.is_empty());
    }

    #[test]
    fn bound_certificate_verifies_against_its_summary() {
        let (cert, summary) = bound_cert_and_summary();
        assert!(cert.verify_summary_binding(&summary).is_ok());
    }

    #[test]
    fn tampered_summary_digest_fails_binding() {
        let (cert, mut summary) = bound_cert_and_summary();
        // Tamper with the summary's digest: the binding must now reject.
        summary.summary_digest = "deadbeef".to_string();
        match cert.verify_summary_binding(&summary) {
            Err(CertificateError::SummaryDigestMismatch { expected, actual }) => {
                assert_eq!(expected, cert.summary_digest);
                assert_eq!(actual, "deadbeef");
            }
            other => panic!("expected SummaryDigestMismatch, got: {:?}", other),
        }
    }

    #[test]
    fn foreign_summary_over_different_proof_fails_binding() {
        let (cert, _summary) = bound_cert_and_summary();
        // A summary over a DIFFERENT proof, even with a valid digest, must not
        // bind to this certificate.
        let other = DerivationCertificate::build(
            ft(),
            "proof-OTHER".into(),
            "placeholder".into(),
            vec![],
            BTreeSet::new(),
            Verdict::Compliant,
        )
        .unwrap();
        let foreign_summary = compile_summary(&other, vec![], &[]);
        match cert.verify_summary_binding(&foreign_summary) {
            Err(CertificateError::SummaryProofMismatch { expected, actual }) => {
                assert_eq!(expected, "proof-XYZ");
                assert_eq!(actual, "proof-OTHER");
            }
            other => panic!("expected SummaryProofMismatch, got: {:?}", other),
        }
    }

    #[test]
    fn build_bound_rejects_summary_over_different_proof() {
        // Building a bound cert with a proof_digest that disagrees with the
        // summary's proof_digest is rejected fail-loud before minting.
        let provisional = DerivationCertificate::build(
            ft(),
            "proof-A".into(),
            "placeholder".into(),
            vec![],
            BTreeSet::new(),
            Verdict::Compliant,
        )
        .unwrap();
        let summary = compile_summary(&provisional, vec![], &[]);
        let r = DerivationCertificate::build_bound(
            ft(),
            "proof-B".into(), // disagrees with summary.proof_digest = "proof-A"
            &summary,
            vec![],
            BTreeSet::new(),
            Verdict::Compliant,
        );
        assert!(matches!(
            r,
            Err(CertificateError::SummaryProofMismatch { .. })
        ));
    }
}
