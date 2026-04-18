//! Compliance certificates produced by the Lex proof pipeline.
//!
//! A [`LexCertificate`] is a content-addressed, serializable record proving
//! that a rule was evaluated against a set of facts, all proof obligations
//! were discharged, and a compliance verdict was produced. Certificates are
//! the terminal output of the pipeline: parse → typecheck → extract
//! obligations → discharge obligations → assemble certificate.
//!
//! Certificates are Ed25519-signable (via `CanonicalBytes`) and convertible
//! to W3C Verifiable Credentials at the `mez-vc` layer.

use std::time::{SystemTime, UNIX_EPOCH};

#[cfg(not(feature = "kernel-integration"))]
use mez_core_min::canonical::CanonicalBytes;
#[cfg(not(feature = "kernel-integration"))]
use mez_core_min::digest::sha256_digest;
#[cfg(feature = "kernel-integration")]
use mez_core::canonical::CanonicalBytes;
#[cfg(feature = "kernel-integration")]
use mez_core::digest::sha256_digest;
use serde::{Deserialize, Serialize};

/// The compliance verdict produced by evaluating a rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ComplianceVerdict {
    /// The rule evaluated to full compliance.
    Compliant,
    /// The rule evaluation is incomplete or awaiting further evidence.
    Pending,
    /// The rule evaluated to non-compliance.
    NonCompliant,
}

impl std::fmt::Display for ComplianceVerdict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Compliant => write!(f, "Compliant"),
            Self::NonCompliant => write!(f, "NonCompliant"),
            Self::Pending => write!(f, "Pending"),
        }
    }
}

/// A compliance certificate proving that a rule was evaluated and a verdict produced.
///
/// Content-addressed via `certificate_digest` (SHA-256 of the canonical
/// serialization). The digest is computed at construction time by
/// [`build_certificate`] and can be independently verified by re-canonicalizing
/// the certificate with `certificate_digest` set to the empty string.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LexCertificate {
    /// SHA-256 hex digest of the canonical rule source AST.
    pub rule_digest: String,
    /// Fiber identifier (if the rule is registered in a fiber registry).
    pub fiber_id: Option<String>,
    /// Jurisdiction this rule applies to.
    pub jurisdiction: String,
    /// Legal basis citation (e.g., "IBC Act 2016 s.66").
    pub legal_basis: String,
    /// The compliance verdict produced by evaluating the rule.
    pub verdict: ComplianceVerdict,
    /// Discharged proof obligations with their decision-procedure witnesses.
    pub obligations: Vec<DischargedObligation>,
    /// SHA-256 hex digest of this certificate (content address).
    pub certificate_digest: String,
    /// ISO 8601 timestamp when the certificate was produced.
    pub issued_at: String,
    /// Entity this certificate pertains to (if applicable).
    pub entity_id: Option<String>,
}

/// A proof obligation that was successfully discharged by a decision procedure.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DischargedObligation {
    /// Obligation category name (e.g., "ExhaustiveMatch", "ThresholdComparison").
    pub category: String,
    /// Human-readable description of the witness evidence.
    pub witness: String,
    /// The decision procedure that discharged the obligation
    /// (e.g., "finite_domain_enumeration", "presburger_arithmetic").
    pub decision_procedure: String,
}

/// Errors that can occur during certificate construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificateError {
    /// System clock is before the UNIX epoch.
    ClockBeforeEpoch,
    /// Canonical serialization of the certificate failed.
    CanonicalizationFailed(String),
}

impl std::fmt::Display for CertificateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CertificateError::ClockBeforeEpoch => {
                write!(f, "system clock is before the UNIX epoch")
            }
            CertificateError::CanonicalizationFailed(msg) => {
                write!(f, "certificate canonicalization failed: {msg}")
            }
        }
    }
}

impl std::error::Error for CertificateError {}

/// Convert UNIX epoch seconds to an ISO 8601 UTC timestamp string.
///
/// Produces `YYYY-MM-DDTHH:MM:SSZ` without pulling in `chrono`.
fn unix_secs_to_iso8601(epoch_secs: u64) -> String {
    // Days in each month for non-leap / leap years.
    const DAYS_IN_MONTH: [[u64; 12]; 2] = [
        [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31],
        [31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31],
    ];
    fn is_leap(y: u64) -> bool {
        y.is_multiple_of(4) && (!y.is_multiple_of(100) || y.is_multiple_of(400))
    }

    let secs_in_day: u64 = 86_400;

    let hh = (epoch_secs % secs_in_day) / 3600;
    let mm = (epoch_secs % 3600) / 60;
    let ss = epoch_secs % 60;

    let mut days = epoch_secs / secs_in_day;
    let mut year: u64 = 1970;

    loop {
        let days_in_year: u64 = if is_leap(year) { 366 } else { 365 };
        if days < days_in_year {
            break;
        }
        days -= days_in_year;
        year += 1;
    }

    let leap = if is_leap(year) { 1 } else { 0 };
    let mut month: u64 = 0;
    for (m, &dim) in DAYS_IN_MONTH[leap].iter().enumerate() {
        if days < dim {
            month = m as u64;
            break;
        }
        days -= dim;
    }

    let day = days + 1;
    let month = month + 1;

    format!(
        "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}Z",
        year, month, day, hh, mm, ss
    )
}

/// Build a [`LexCertificate`] from the Lex pipeline outputs.
///
/// Computes the `certificate_digest` by canonicalizing a preliminary
/// certificate (with an empty digest) and taking its SHA-256 hash.
pub fn build_certificate(
    rule_digest: &str,
    jurisdiction: &str,
    legal_basis: &str,
    verdict: ComplianceVerdict,
    obligations: Vec<DischargedObligation>,
) -> Result<LexCertificate, CertificateError> {
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|_| CertificateError::ClockBeforeEpoch)?
        .as_secs();
    let issued_at = unix_secs_to_iso8601(secs);

    // Build a preliminary certificate with empty digest for hashing.
    let mut cert = LexCertificate {
        rule_digest: rule_digest.to_string(),
        fiber_id: None,
        jurisdiction: jurisdiction.to_string(),
        legal_basis: legal_basis.to_string(),
        verdict,
        obligations,
        certificate_digest: String::new(),
        issued_at,
        entity_id: None,
    };

    // Content-address the certificate.
    let canonical = CanonicalBytes::new(&cert)
        .map_err(|e| CertificateError::CanonicalizationFailed(e.to_string()))?;
    cert.certificate_digest = sha256_digest(&canonical).to_hex();

    Ok(cert)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_certificate_produces_valid_digest() {
        let cert = build_certificate(
            "abcd1234abcd1234abcd1234abcd1234abcd1234abcd1234abcd1234abcd1234",
            "SC",
            "IBC Act 2016 s.66",
            ComplianceVerdict::Compliant,
            vec![DischargedObligation {
                category: "ExhaustiveMatch".to_string(),
                witness: "all match arms cover the scrutinee domain".to_string(),
                decision_procedure: "finite_domain_enumeration".to_string(),
            }],
        )
        .unwrap();

        assert_eq!(cert.certificate_digest.len(), 64, "digest should be 64 hex chars");
        assert_eq!(cert.jurisdiction, "SC");
        assert_eq!(cert.legal_basis, "IBC Act 2016 s.66");
        assert_eq!(cert.verdict, ComplianceVerdict::Compliant);
        assert_eq!(cert.obligations.len(), 1);
        assert!(
            cert.issued_at.ends_with('Z') && cert.issued_at.contains('T'),
            "issued_at should be ISO 8601: {}",
            cert.issued_at
        );
    }

    #[test]
    fn certificate_digest_is_deterministic_for_same_content() {
        // Two certificates with the same content (but built in the same second)
        // must produce the same digest. We control `issued_at` by building a
        // certificate manually.
        let obligations = vec![DischargedObligation {
            category: "ThresholdComparison".to_string(),
            witness: "comparison holds".to_string(),
            decision_procedure: "presburger_arithmetic".to_string(),
        }];

        let mut cert = LexCertificate {
            rule_digest: "deadbeef".repeat(8),
            fiber_id: None,
            jurisdiction: "SC".to_string(),
            legal_basis: "IBC Act 2016 s.66".to_string(),
            verdict: ComplianceVerdict::Compliant,
            obligations: obligations.clone(),
            certificate_digest: String::new(),
            issued_at: "2023-11-14T22:13:20Z".to_string(),
            entity_id: None,
        };

        let canonical = CanonicalBytes::new(&cert).expect("canonicalize");
        let digest1 = sha256_digest(&canonical).to_hex();

        cert.certificate_digest = String::new();
        let canonical2 = CanonicalBytes::new(&cert).expect("canonicalize");
        let digest2 = sha256_digest(&canonical2).to_hex();

        assert_eq!(digest1, digest2, "same content must produce same digest");
        assert_eq!(digest1.len(), 64);
    }

    #[test]
    fn serde_roundtrip_certificate() {
        let cert = build_certificate(
            &"ab".repeat(32),
            "ADGM",
            "Companies Regulations 2020 s.12",
            ComplianceVerdict::Pending,
            vec![
                DischargedObligation {
                    category: "SanctionsCheck".to_string(),
                    witness: "sanctions screening clear".to_string(),
                    decision_procedure: "bdd_style_boolean_compliance".to_string(),
                },
                DischargedObligation {
                    category: "IdentityVerification".to_string(),
                    witness: "KYC attestation chain valid".to_string(),
                    decision_procedure: "identity_attestation_chain".to_string(),
                },
            ],
        )
        .unwrap();

        let json = serde_json::to_string(&cert).expect("serialize");
        let deserialized: LexCertificate = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(deserialized.certificate_digest, cert.certificate_digest);
        assert_eq!(deserialized.jurisdiction, "ADGM");
        assert_eq!(deserialized.legal_basis, "Companies Regulations 2020 s.12");
        assert_eq!(deserialized.verdict, ComplianceVerdict::Pending);
        assert_eq!(deserialized.obligations.len(), 2);
        assert_eq!(deserialized.obligations[0].category, "SanctionsCheck");
        assert_eq!(deserialized.obligations[1].decision_procedure, "identity_attestation_chain");
        assert_eq!(deserialized.rule_digest, cert.rule_digest);
        assert_eq!(deserialized.issued_at, cert.issued_at);
    }

    #[test]
    fn serde_roundtrip_verdict_variants() {
        for verdict in [
            ComplianceVerdict::Compliant,
            ComplianceVerdict::Pending,
            ComplianceVerdict::NonCompliant,
        ] {
            let json = serde_json::to_string(&verdict).expect("serialize verdict");
            let deserialized: ComplianceVerdict =
                serde_json::from_str(&json).expect("deserialize verdict");
            assert_eq!(deserialized, verdict);
        }
    }

    #[test]
    fn serde_roundtrip_discharged_obligation() {
        let obligation = DischargedObligation {
            category: "DefeasibleResolution".to_string(),
            witness: "highest-priority satisfied exception at priority 50".to_string(),
            decision_procedure: "fuel_bounded_defeasible_search".to_string(),
        };

        let json = serde_json::to_string(&obligation).expect("serialize");
        let deserialized: DischargedObligation =
            serde_json::from_str(&json).expect("deserialize");

        assert_eq!(deserialized.category, obligation.category);
        assert_eq!(deserialized.witness, obligation.witness);
        assert_eq!(deserialized.decision_procedure, obligation.decision_procedure);
    }

    #[test]
    fn certificate_with_entity_id_roundtrips() {
        let mut cert = build_certificate(
            &"ff".repeat(32),
            "SC",
            "IBC Act 2016 s.66",
            ComplianceVerdict::NonCompliant,
            vec![],
        )
        .unwrap();
        cert.entity_id = Some("ent-12345".to_string());
        cert.fiber_id = Some("fiber-ibc-s66-min-directors".to_string());

        let json = serde_json::to_string(&cert).expect("serialize");
        let deserialized: LexCertificate = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(deserialized.entity_id, Some("ent-12345".to_string()));
        assert_eq!(
            deserialized.fiber_id,
            Some("fiber-ibc-s66-min-directors".to_string())
        );
        assert_eq!(deserialized.verdict, ComplianceVerdict::NonCompliant);
    }

    #[test]
    fn different_verdicts_produce_different_digests() {
        let obligations = vec![DischargedObligation {
            category: "ExhaustiveMatch".to_string(),
            witness: "covered".to_string(),
            decision_procedure: "finite_domain_enumeration".to_string(),
        }];

        let mut cert_compliant = LexCertificate {
            rule_digest: "aa".repeat(32),
            fiber_id: None,
            jurisdiction: "SC".to_string(),
            legal_basis: "IBC Act 2016 s.66".to_string(),
            verdict: ComplianceVerdict::Compliant,
            obligations: obligations.clone(),
            certificate_digest: String::new(),
            issued_at: "2023-11-14T22:13:20Z".to_string(),
            entity_id: None,
        };

        let mut cert_non_compliant = cert_compliant.clone();
        cert_non_compliant.verdict = ComplianceVerdict::NonCompliant;

        let canonical_c =
            CanonicalBytes::new(&cert_compliant).expect("canonicalize");
        cert_compliant.certificate_digest = sha256_digest(&canonical_c).to_hex();

        let canonical_nc =
            CanonicalBytes::new(&cert_non_compliant).expect("canonicalize");
        cert_non_compliant.certificate_digest = sha256_digest(&canonical_nc).to_hex();

        assert_ne!(
            cert_compliant.certificate_digest,
            cert_non_compliant.certificate_digest,
            "different verdicts must produce different digests"
        );
    }
}
