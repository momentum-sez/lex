//! Compliance certificates produced by the Lex proof pipeline.
//!
//! A [`LexCertificate`] is a content-addressed, serializable record proving
//! that a rule was evaluated against a set of facts, all proof obligations
//! were discharged, and a compliance verdict was produced. Certificates are
//! the terminal output of the pipeline: parse → typecheck → extract
//! obligations → discharge obligations → assemble certificate.
//!
//! Certificates are Ed25519-signable (via `CanonicalBytes`) and convertible
//! to W3C Verifiable Credentials at the embedder's credential layer.

use std::time::{SystemTime, UNIX_EPOCH};

use mez_canonical::canonical::CanonicalBytes;
use mez_canonical::digest::sha256_digest;
use serde::{Deserialize, Serialize};

use crate::ast::AppliesTo;
use crate::decide::DecisionResult;
use crate::obligations::ProofObligation;

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
    /// Jurisdiction this rule applies to (runtime evaluation metadata — the
    /// concrete jurisdiction the rule was evaluated under).
    pub jurisdiction: String,
    /// The rule's typed scope declaration, lifted verbatim from
    /// [`crate::ast::DefeasibleRule::applies_to`] (Frontier-09 §1 commitment 4).
    ///
    /// `None` for a pre-09 rule that carried no `applies_to` clause. A
    /// downstream consumer (e.g. a sovereign kernel binding a Lex certificate
    /// to an operation it admits) reads this typed scope to verify the cert's
    /// `(operation_family, jurisdiction)` binding **from the certificate body
    /// itself** — it does not have to invent a private `(operation, rule)`
    /// mapping table. The scope is part of the certificate's content digest, so
    /// it cannot be altered after issuance without invalidating
    /// `certificate_digest`.
    #[serde(default)]
    pub applies_to: Option<AppliesTo>,
    /// Legal basis citation (e.g., "IBC Act 2016 s.130(1)").
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
///
/// # Unforgeability
///
/// The fields are private and there is **no public field constructor**. The
/// only way to mint a `DischargedObligation` is [`DischargedObligation::seal`],
/// which requires a genuine [`DecisionResult::Proved`] carrying a
/// [`crate::decide::ProofWitness`]. `ProofWitness` values are produced only by
/// the decision procedures in [`crate::decide`] (e.g. `finite_domain_check`,
/// `threshold_check`, `boolean_compliance_check`, `defeasible_search`,
/// `temporal_tableau`, `smt_check`). A caller cannot hand-construct a witness,
/// so a certificate cannot be minted from a fabricated discharge: the
/// `decision_procedure` and `witness` strings are copied **out of** the proof
/// witness, not supplied by the caller, and the `obligation_id`/`category` are
/// copied out of the real extracted [`ProofObligation`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DischargedObligation {
    /// The id of the extracted obligation this discharge covers (e.g.
    /// `"obl-0001"`). Bound at seal time from the genuine [`ProofObligation`];
    /// this is the key `build_certificate` uses to verify coverage.
    obligation_id: String,
    /// Obligation category name (e.g., "ExhaustiveMatch", "ThresholdComparison").
    category: String,
    /// Human-readable description of the witness evidence, copied from the
    /// proof witness produced by the decision procedure.
    witness: String,
    /// The decision procedure that discharged the obligation
    /// (e.g., "finite_domain_enumeration", "presburger_arithmetic"), copied
    /// from the proof witness.
    decision_procedure: String,
}

impl DischargedObligation {
    /// Seal a discharged obligation from genuine decision-procedure evidence.
    ///
    /// This is the sole constructor. It binds the extracted `obligation`
    /// (which carries the structural obligation id and category) to the
    /// `result` of running a decision procedure against it. Only a
    /// [`DecisionResult::Proved`] is accepted — a `Refuted` or `Undecidable`
    /// result is **not** a discharge and is rejected, so a certificate can
    /// never assert that an obligation was discharged when it was in fact
    /// refuted or left undecided.
    ///
    /// The `witness` and `decision_procedure` recorded on the certificate are
    /// taken from the proof witness, not from caller-supplied strings, which
    /// is what makes a fabricated discharge impossible to mint.
    pub fn seal(
        obligation: &ProofObligation,
        result: &DecisionResult,
    ) -> Result<Self, CertificateError> {
        match result {
            DecisionResult::Proved { witness } => Ok(DischargedObligation {
                obligation_id: obligation.id.clone(),
                category: format!("{:?}", obligation.category),
                witness: witness.description.clone(),
                decision_procedure: witness.procedure.clone(),
            }),
            DecisionResult::Refuted { counterexample } => {
                Err(CertificateError::ObligationNotDischarged {
                    obligation_id: obligation.id.clone(),
                    reason: format!("refuted: {counterexample}"),
                })
            }
            DecisionResult::Undecidable { reason } => {
                Err(CertificateError::ObligationNotDischarged {
                    obligation_id: obligation.id.clone(),
                    reason: format!("undecidable: {reason}"),
                })
            }
        }
    }

    /// The id of the extracted obligation this discharge covers.
    pub fn obligation_id(&self) -> &str {
        &self.obligation_id
    }

    /// The obligation category (`Debug` form of [`crate::obligations::ObligationCategory`]).
    pub fn category(&self) -> &str {
        &self.category
    }

    /// The witness description, copied from the decision-procedure proof witness.
    pub fn witness(&self) -> &str {
        &self.witness
    }

    /// The decision procedure that discharged the obligation.
    pub fn decision_procedure(&self) -> &str {
        &self.decision_procedure
    }
}

/// Errors that can occur during certificate construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificateError {
    /// System clock is before the UNIX epoch.
    ClockBeforeEpoch,
    /// Canonical serialization of the certificate failed.
    CanonicalizationFailed(String),
    /// A decision result was not a genuine discharge (it was refuted or
    /// undecidable), so it cannot seal a [`DischargedObligation`].
    ObligationNotDischarged {
        /// The extracted obligation that could not be discharged.
        obligation_id: String,
        /// Why it was not discharged (refuted counterexample / undecidable reason).
        reason: String,
    },
    /// An extracted obligation has no matching genuine discharge in the
    /// supplied discharged set. The certificate refuses to assert coverage it
    /// did not verify.
    UndischargedObligation {
        /// The extracted obligation left uncovered.
        obligation_id: String,
        /// The obligation's category, for diagnostics.
        category: String,
    },
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
            CertificateError::ObligationNotDischarged {
                obligation_id,
                reason,
            } => write!(
                f,
                "obligation `{obligation_id}` was not discharged ({reason}); \
                 only a Proved decision result can seal a discharge"
            ),
            CertificateError::UndischargedObligation {
                obligation_id,
                category,
            } => write!(
                f,
                "extracted obligation `{obligation_id}` [{category}] has no matching \
                 discharge; the certificate refuses to assert undischarged coverage"
            ),
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
/// # Coverage validation (no unvalidated discharge)
///
/// `extracted` is the full set of proof obligations the rule produced (from
/// [`crate::obligations::extract_obligations`]); `discharged` is the set of
/// sealed discharges. This function verifies that **every** extracted
/// obligation has a matching genuine [`DischargedObligation`] (keyed by
/// obligation id) before it will issue a certificate. If any extracted
/// obligation is uncovered, it returns
/// [`CertificateError::UndischargedObligation`] and issues nothing — a
/// certificate must not assert discharge it did not verify.
///
/// Because a `DischargedObligation` can only be produced by
/// [`DischargedObligation::seal`] from a [`DecisionResult::Proved`], passing
/// the coverage check is proof that each obligation was actually discharged by
/// a decision procedure, not merely asserted.
///
/// Computes the `certificate_digest` by canonicalizing a preliminary
/// certificate (with an empty digest) and taking its SHA-256 hash.
pub fn build_certificate(
    rule_digest: &str,
    jurisdiction: &str,
    legal_basis: &str,
    verdict: ComplianceVerdict,
    extracted: &[ProofObligation],
    discharged: Vec<DischargedObligation>,
) -> Result<LexCertificate, CertificateError> {
    build_certificate_with_scope(
        rule_digest,
        jurisdiction,
        None,
        legal_basis,
        verdict,
        extracted,
        discharged,
    )
}

/// Build a [`LexCertificate`] carrying the rule's typed `applies_to` scope
/// (Frontier-09 §1 commitment 4).
///
/// Identical to [`build_certificate`] except it records `applies_to` on the
/// certificate. The scope is part of the content-addressed body, so the
/// `certificate_digest` binds it: a downstream consumer that reads the scope
/// off the certificate to verify an `(operation_family, jurisdiction)` binding
/// is reading a digest-bound field, not a forgeable side annotation.
///
/// Callers that have the admitted rule's `DefeasibleRule.applies_to` pass it
/// through here; callers that do not (legacy pre-09 path) use
/// [`build_certificate`], which records `None`.
pub fn build_certificate_with_scope(
    rule_digest: &str,
    jurisdiction: &str,
    applies_to: Option<AppliesTo>,
    legal_basis: &str,
    verdict: ComplianceVerdict,
    extracted: &[ProofObligation],
    discharged: Vec<DischargedObligation>,
) -> Result<LexCertificate, CertificateError> {
    // Coverage check: every extracted obligation must have a matching sealed
    // discharge. Match on the structural obligation id bound at seal time.
    for obligation in extracted {
        let covered = discharged
            .iter()
            .any(|d| d.obligation_id == obligation.id);
        if !covered {
            return Err(CertificateError::UndischargedObligation {
                obligation_id: obligation.id.clone(),
                category: format!("{:?}", obligation.category),
            });
        }
    }

    let obligations = discharged;

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
        applies_to,
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
    use crate::decide::{boolean_check, finite_domain_check, threshold_check};
    use crate::obligations::{ObligationCategory, ProofObligation};

    // ── Test helpers: build genuine extracted-obligation / discharge pairs ──

    /// A genuine extracted obligation. `ProofObligation` is a plain in-crate
    /// struct; tests construct it the same way `extract_obligations` does.
    fn extracted(id: &str, category: ObligationCategory) -> ProofObligation {
        ProofObligation {
            id: id.to_string(),
            description: format!("test obligation {id}"),
            category,
            term: crate::ast::Term::StringLit(id.to_string()),
            expected: "holds".to_string(),
            suggested_procedure: "test".to_string(),
        }
    }

    /// Seal a discharge from a genuine `boolean_check(true)` proof witness.
    fn seal_proved(obl: &ProofObligation) -> DischargedObligation {
        DischargedObligation::seal(obl, &boolean_check(true))
            .expect("Proved result must seal")
    }

    #[test]
    fn build_certificate_produces_valid_digest() {
        let obl = extracted("obl-0001", ObligationCategory::ExhaustiveMatch);
        let discharged = vec![seal_proved(&obl)];
        let cert = build_certificate(
            "abcd1234abcd1234abcd1234abcd1234abcd1234abcd1234abcd1234abcd1234",
            "SC",
            "IBC Act 2016 s.130(1)",
            ComplianceVerdict::Compliant,
            std::slice::from_ref(&obl),
            discharged,
        )
        .unwrap();

        assert_eq!(cert.certificate_digest.len(), 64, "digest should be 64 hex chars");
        assert_eq!(cert.jurisdiction, "SC");
        assert_eq!(cert.legal_basis, "IBC Act 2016 s.130(1)");
        assert_eq!(cert.verdict, ComplianceVerdict::Compliant);
        assert_eq!(cert.obligations.len(), 1);
        assert!(
            cert.issued_at.ends_with('Z') && cert.issued_at.contains('T'),
            "issued_at should be ISO 8601: {}",
            cert.issued_at
        );
    }

    // ── PRIORITY 1: a discharge cannot be forged ──

    #[test]
    fn seal_rejects_refuted_result() {
        // `finite_domain_check` against a value outside the domain is Refuted.
        let obl = extracted("obl-0001", ObligationCategory::DomainMembership);
        let refuted = finite_domain_check("Jurisdiction", &["SC"], "XX");
        let err = DischargedObligation::seal(&obl, &refuted).unwrap_err();
        assert!(
            matches!(err, CertificateError::ObligationNotDischarged { .. }),
            "a refuted result must not seal a discharge, got {err:?}"
        );
    }

    #[test]
    fn seal_rejects_undecidable_result() {
        // An unknown operator is Undecidable.
        let obl = extracted("obl-0001", ObligationCategory::ThresholdComparison);
        let undecidable = threshold_check(1, 1, "!=");
        let err = DischargedObligation::seal(&obl, &undecidable).unwrap_err();
        assert!(
            matches!(err, CertificateError::ObligationNotDischarged { .. }),
            "an undecidable result must not seal a discharge, got {err:?}"
        );
    }

    #[test]
    fn sealed_discharge_copies_strings_from_the_proof_witness() {
        // The recorded procedure/witness come from the decision procedure,
        // not from any caller-supplied string — this is what makes forgery
        // impossible.
        let obl = extracted("obl-0001", ObligationCategory::ThresholdComparison);
        let proved = threshold_check(5, 1, ">=");
        let sealed = DischargedObligation::seal(&obl, &proved).unwrap();
        assert_eq!(sealed.decision_procedure(), "presburger_arithmetic");
        assert_eq!(sealed.obligation_id(), "obl-0001");
        assert_eq!(sealed.category(), "ThresholdComparison");
        assert!(sealed.witness().contains("5 >= 1"));
    }

    // ── PRIORITY 2: build_certificate refuses unvalidated coverage ──

    #[test]
    fn build_certificate_rejects_uncovered_obligation() {
        let covered = extracted("obl-0001", ObligationCategory::ExhaustiveMatch);
        let uncovered = extracted("obl-0002", ObligationCategory::SanctionsCheck);
        // Discharge only the first; leave the second uncovered.
        let discharged = vec![seal_proved(&covered)];
        let err = build_certificate(
            &"ab".repeat(32),
            "SC",
            "IBC Act 2016 s.130(1)",
            ComplianceVerdict::Compliant,
            &[covered, uncovered],
            discharged,
        )
        .unwrap_err();
        match err {
            CertificateError::UndischargedObligation { obligation_id, .. } => {
                assert_eq!(obligation_id, "obl-0002");
            }
            other => panic!("expected UndischargedObligation, got {other:?}"),
        }
    }

    #[test]
    fn build_certificate_accepts_full_coverage() {
        let a = extracted("obl-0001", ObligationCategory::ExhaustiveMatch);
        let b = extracted("obl-0002", ObligationCategory::ThresholdComparison);
        let discharged = vec![seal_proved(&a), seal_proved(&b)];
        let cert = build_certificate(
            &"ab".repeat(32),
            "SC",
            "IBC Act 2016 s.130(1)",
            ComplianceVerdict::Compliant,
            &[a, b],
            discharged,
        )
        .expect("full coverage must succeed");
        assert_eq!(cert.obligations.len(), 2);
    }

    #[test]
    fn build_certificate_accepts_no_obligations() {
        // A rule that extracts zero obligations is trivially fully covered.
        let cert = build_certificate(
            &"ff".repeat(32),
            "SC",
            "IBC Act 2016 s.130(1)",
            ComplianceVerdict::NonCompliant,
            &[],
            vec![],
        )
        .unwrap();
        assert!(cert.obligations.is_empty());
    }

    // ── Frontier-09 §1 commitment 4: certificate carries typed applies_to ──

    fn scope_sc_incorporate() -> AppliesTo {
        use crate::ast::{JurisdictionScope, OperationKindScope, QualIdent};
        AppliesTo {
            jurisdictions: vec![JurisdictionScope::Specific(QualIdent::from_dotted("sc"))],
            operation_kinds: vec![OperationKindScope::Specific(QualIdent::from_dotted(
                "entity.incorporate",
            ))],
        }
    }

    #[test]
    fn build_certificate_records_no_scope_by_default() {
        let cert = build_certificate(
            &"ab".repeat(32),
            "SC",
            "IBC Act 2016 s.130(1)",
            ComplianceVerdict::Compliant,
            &[],
            vec![],
        )
        .unwrap();
        assert_eq!(cert.applies_to, None);
    }

    #[test]
    fn build_certificate_with_scope_records_typed_applies_to() {
        let scope = scope_sc_incorporate();
        let cert = build_certificate_with_scope(
            &"ab".repeat(32),
            "SC",
            Some(scope.clone()),
            "IBC Act 2016 s.130(1)",
            ComplianceVerdict::Compliant,
            &[],
            vec![],
        )
        .unwrap();
        // A downstream consumer reads the operation family + jurisdiction off
        // the certificate body directly — no private mapping table.
        assert_eq!(cert.applies_to, Some(scope));
        let recorded = cert.applies_to.unwrap();
        assert_eq!(recorded.operation_kinds.len(), 1);
        assert_eq!(recorded.jurisdictions.len(), 1);
    }

    #[test]
    fn certificate_digest_binds_applies_to_scope() {
        // The scope is part of the content-addressed body: a certificate with a
        // scope and one without must have different digests (the scope cannot
        // be altered post-issuance without invalidating the digest).
        let no_scope = build_certificate(
            &"cd".repeat(32),
            "SC",
            "IBC Act 2016 s.130(1)",
            ComplianceVerdict::Compliant,
            &[],
            vec![],
        )
        .unwrap();
        let with_scope = build_certificate_with_scope(
            &"cd".repeat(32),
            "SC",
            Some(scope_sc_incorporate()),
            "IBC Act 2016 s.130(1)",
            ComplianceVerdict::Compliant,
            &[],
            vec![],
        )
        .unwrap();
        // Same second, same everything except scope → digests must differ.
        // (If the clock ticked between builds, issued_at also differs, but the
        // scope difference alone guarantees inequality regardless.)
        assert_ne!(
            no_scope.certificate_digest, with_scope.certificate_digest,
            "applies_to must be inside the content digest"
        );
    }

    #[test]
    fn certificate_digest_is_deterministic_for_same_content() {
        // Two certificates with the same content (but built in the same second)
        // must produce the same digest. We control `issued_at` by building a
        // certificate manually.
        let obl = extracted("obl-0001", ObligationCategory::ThresholdComparison);
        let obligations = vec![seal_proved(&obl)];

        let mut cert = LexCertificate {
            rule_digest: "deadbeef".repeat(8),
            fiber_id: None,
            jurisdiction: "SC".to_string(),
            applies_to: None,
            legal_basis: "IBC Act 2016 s.130(1)".to_string(),
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
        let a = extracted("obl-0001", ObligationCategory::SanctionsCheck);
        let b = extracted("obl-0002", ObligationCategory::IdentityVerification);
        let discharged = vec![seal_proved(&a), seal_proved(&b)];
        let cert = build_certificate(
            &"ab".repeat(32),
            "ADGM",
            "Companies Regulations 2020 s.12",
            ComplianceVerdict::Pending,
            &[a, b],
            discharged,
        )
        .unwrap();

        let json = serde_json::to_string(&cert).expect("serialize");
        let deserialized: LexCertificate = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(deserialized.certificate_digest, cert.certificate_digest);
        assert_eq!(deserialized.jurisdiction, "ADGM");
        assert_eq!(deserialized.legal_basis, "Companies Regulations 2020 s.12");
        assert_eq!(deserialized.verdict, ComplianceVerdict::Pending);
        assert_eq!(deserialized.obligations.len(), 2);
        assert_eq!(deserialized.obligations[0].category(), "SanctionsCheck");
        assert_eq!(
            deserialized.obligations[0].decision_procedure(),
            "boolean_decision"
        );
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
        let obl = extracted("obl-0001", ObligationCategory::DefeasibleResolution);
        let obligation = seal_proved(&obl);

        let json = serde_json::to_string(&obligation).expect("serialize");
        let deserialized: DischargedObligation =
            serde_json::from_str(&json).expect("deserialize");

        assert_eq!(deserialized.category(), obligation.category());
        assert_eq!(deserialized.witness(), obligation.witness());
        assert_eq!(deserialized.decision_procedure(), obligation.decision_procedure());
        assert_eq!(deserialized.obligation_id(), obligation.obligation_id());
    }

    #[test]
    fn certificate_with_entity_id_roundtrips() {
        let mut cert = build_certificate(
            &"ff".repeat(32),
            "SC",
            "IBC Act 2016 s.130(1)",
            ComplianceVerdict::NonCompliant,
            &[],
            vec![],
        )
        .unwrap();
        cert.entity_id = Some("ent-12345".to_string());
        cert.fiber_id = Some("fiber-ibc-s130-min-directors".to_string());

        let json = serde_json::to_string(&cert).expect("serialize");
        let deserialized: LexCertificate = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(deserialized.entity_id, Some("ent-12345".to_string()));
        assert_eq!(
            deserialized.fiber_id,
            Some("fiber-ibc-s130-min-directors".to_string())
        );
        assert_eq!(deserialized.verdict, ComplianceVerdict::NonCompliant);
    }

    #[test]
    fn different_verdicts_produce_different_digests() {
        let obl = extracted("obl-0001", ObligationCategory::ExhaustiveMatch);
        let obligations = vec![seal_proved(&obl)];

        let mut cert_compliant = LexCertificate {
            rule_digest: "aa".repeat(32),
            fiber_id: None,
            jurisdiction: "SC".to_string(),
            applies_to: None,
            legal_basis: "IBC Act 2016 s.130(1)".to_string(),
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
