//! Elaboration certificates proving refinement-preservation across
//! surface-to-core Lex elaboration.
//!
//! An [`ElaborationCertificate`] binds a surface source hash to a core output
//! hash and records which refinement predicates and effect rows were preserved
//! through elaboration. This lets downstream consumers (tensor evaluation,
//! fiber registry, corridor proofs) verify that elaboration did not silently
//! drop semantic content.
//!
//! A [`ScopeClosureCertificate`] records the free-identifier analysis for a
//! fiber's closure, proving that all captured identifiers resolve to known
//! definition sites.

use mez_core::canonical::CanonicalBytes;
use mez_core::digest::sha256_digest;
use serde::{Deserialize, Serialize};

/// Certificate proving that elaboration from surface Lex to core Lex
/// preserved refinement predicates and effect annotations.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ElaborationCertificate {
    /// SHA-256 hex digest of the surface source text.
    pub surface_hash: String,
    /// SHA-256 hex digest of the core output (elaborated AST serialization).
    pub core_hash: String,
    /// Refinement predicates preserved through elaboration (e.g.,
    /// `"exhaustive_match"`, `"threshold_monotonicity"`).
    pub refinement_predicates_preserved: Vec<String>,
    /// Effect rows preserved through elaboration (e.g.,
    /// `"Sanctions"`, `"DataPrivacy"`).
    pub effects_preserved: Vec<String>,
    /// ISO 8601 timestamp when the certificate was produced.
    pub certified_at: String,
    /// SHA-256 hex digest of the certificate itself (content address).
    pub certificate_digest: String,
}

/// Certificate recording the free-identifier analysis of a fiber closure.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScopeClosureCertificate {
    /// Fiber identifier this closure analysis pertains to.
    pub fiber_id: String,
    /// Free identifiers found in the fiber body, paired with their
    /// definition-site binding descriptions (e.g., `"prelude::is_sanctioned"`).
    pub free_identifiers: Vec<FreeIdentifierBinding>,
    /// Whether the closure is capture-free (all identifiers are either
    /// bound locally or resolved through the prelude).
    pub capture_free: bool,
}

/// A free identifier and the definition site where it is bound.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FreeIdentifierBinding {
    /// The identifier name as it appears in the surface source.
    pub name: String,
    /// The definition site that binds this identifier (e.g.,
    /// `"prelude"`, `"let-binding at line 12"`, `"lambda parameter"`).
    pub definition_site: String,
}

/// Errors that can occur during elaboration certificate construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ElaborationCertError {
    /// The surface source text is empty.
    EmptySource,
    /// The core output text is empty.
    EmptyOutput,
    /// No refinement predicates were preserved (elaboration should preserve
    /// at least one semantic predicate).
    NoPredicatesPreserved,
    /// Canonical serialization failed.
    CanonicalizationFailed(String),
    /// System clock is before the UNIX epoch.
    ClockBeforeEpoch,
    /// Structural preservation analysis is not yet implemented.
    ///
    /// The elaboration certificate cannot assert preservation of refinement
    /// predicates or effect rows until the sound structural check is in
    /// place — a walk over both the surface and core ASTs that verifies each
    /// surface refinement survives on the corresponding core term.
    /// Substring matching on source text is unsound because any comment that
    /// happens to mention a keyword would trivially pass.
    PreservationCheckUnimplemented,
}

impl std::fmt::Display for ElaborationCertError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptySource => write!(f, "surface source text is empty"),
            Self::EmptyOutput => write!(f, "core output text is empty"),
            Self::NoPredicatesPreserved => {
                write!(f, "no refinement predicates preserved through elaboration")
            }
            Self::CanonicalizationFailed(msg) => {
                write!(f, "elaboration certificate canonicalization failed: {msg}")
            }
            Self::ClockBeforeEpoch => {
                write!(f, "system clock is before the UNIX epoch")
            }
            Self::PreservationCheckUnimplemented => write!(
                f,
                "refinement-predicate and effect-row preservation check is not yet implemented"
            ),
        }
    }
}

impl std::error::Error for ElaborationCertError {}

/// Produce an [`ElaborationCertificate`] binding the surface source to the
/// core output and recording preserved refinement predicates.
///
/// Both `surface_source` and `core_output` are hashed with SHA-256 via
/// `mez_core::digest`. The certificate is content-addressed: its own
/// `certificate_digest` is the SHA-256 of the canonical serialization
/// with `certificate_digest` set to the empty string.
///
/// Currently returns [`ElaborationCertError::PreservationCheckUnimplemented`]
/// because the sound structural preservation check is not yet in place.
/// See [`extract_preserved_predicates`] and [`extract_preserved_effects`]
/// for the contract.
pub fn produce_elaboration_certificate(
    surface_source: &str,
    core_output: &str,
) -> Result<ElaborationCertificate, ElaborationCertError> {
    if surface_source.is_empty() {
        return Err(ElaborationCertError::EmptySource);
    }
    if core_output.is_empty() {
        return Err(ElaborationCertError::EmptyOutput);
    }

    let surface_canonical = CanonicalBytes::new(&surface_source)
        .map_err(|e| ElaborationCertError::CanonicalizationFailed(e.to_string()))?;
    let _surface_hash = sha256_digest(&surface_canonical).to_hex();

    let core_canonical = CanonicalBytes::new(&core_output)
        .map_err(|e| ElaborationCertError::CanonicalizationFailed(e.to_string()))?;
    let _core_hash = sha256_digest(&core_canonical).to_hex();

    // Extract preserved refinement predicates and effect rows. Both must be
    // computed by a sound structural walk over the elaborated AST; the
    // public API currently refuses to issue a certificate because that
    // check is not yet implemented.
    let _predicates = extract_preserved_predicates(surface_source, core_output)?;
    let _effects = extract_preserved_effects(surface_source, core_output)?;

    // Unreachable once the preservation check exists; reachable today
    // because the calls above always return
    // `PreservationCheckUnimplemented`.
    Err(ElaborationCertError::PreservationCheckUnimplemented)
}

/// Verify that an elaboration certificate is structurally valid.
///
/// Checks:
/// - `surface_hash` is non-empty and 64 hex chars
/// - `core_hash` is non-empty and 64 hex chars
/// - at least one refinement predicate is preserved
/// - `certificate_digest` is non-empty and 64 hex chars
/// - `certified_at` is a plausible ISO 8601 timestamp
pub fn verify_elaboration_certificate(cert: &ElaborationCertificate) -> bool {
    is_valid_sha256_hex(&cert.surface_hash)
        && is_valid_sha256_hex(&cert.core_hash)
        && !cert.refinement_predicates_preserved.is_empty()
        && is_valid_sha256_hex(&cert.certificate_digest)
        && cert.certified_at.ends_with('Z')
        && cert.certified_at.contains('T')
}

/// Check whether a string is a valid 64-character hex-encoded SHA-256 digest.
fn is_valid_sha256_hex(s: &str) -> bool {
    s.len() == 64 && s.chars().all(|c| c.is_ascii_hexdigit())
}

/// Extract preserved refinement predicates.
///
/// TODO: a sound structural check must walk the AST of the surface term and
/// the corresponding core term, verifying each surface refinement survives
/// on the corresponding core term. Substring matching on source text is
/// unsound and has been withdrawn — any comment mentioning a keyword would
/// have trivially passed the old check.
///
/// Until the structural walk is implemented, this function returns
/// [`ElaborationCertError::PreservationCheckUnimplemented`].
fn extract_preserved_predicates(
    _surface: &str,
    _core: &str,
) -> Result<Vec<String>, ElaborationCertError> {
    Err(ElaborationCertError::PreservationCheckUnimplemented)
}

/// Extract preserved effect annotations.
///
/// TODO: a sound structural check must walk the AST of the surface term and
/// the corresponding core term, verifying each surface effect annotation
/// appears in the effect row of the corresponding core term. Substring
/// matching on source text is unsound and has been withdrawn.
///
/// Until the structural walk is implemented, this function returns
/// [`ElaborationCertError::PreservationCheckUnimplemented`].
fn extract_preserved_effects(
    _surface: &str,
    _core: &str,
) -> Result<Vec<String>, ElaborationCertError> {
    Err(ElaborationCertError::PreservationCheckUnimplemented)
}

/// Unsound substring-based preservation detection. RETAINED for reference
/// only; callers must not use this. The sound replacement walks the ASTs.
#[allow(dead_code, non_snake_case)]
fn extract_preserved_predicates_STUB(surface: &str, core: &str) -> Vec<String> {
    let candidate_predicates = [
        ("match", "exhaustive_match"),
        ("if", "conditional_branch"),
        ("let", "let_binding"),
        ("fun", "lambda_abstraction"),
        ("forall", "universal_quantification"),
        ("exists", "existential_quantification"),
        ("effect", "effect_annotation"),
        ("rule", "rule_definition"),
        ("exception", "exception_clause"),
        ("obligation", "obligation_marker"),
        ("defeasible", "defeasible_reasoning"),
        ("scope", "scope_constraint"),
    ];

    candidate_predicates
        .iter()
        .filter(|(keyword, _)| surface.contains(keyword) && core.contains(keyword))
        .map(|(_, predicate)| predicate.to_string())
        .collect()
}

/// Unsound substring-based effect-preservation detection. RETAINED for
/// reference only; callers must not use this. The sound replacement walks
/// the ASTs and inspects effect rows.
#[allow(dead_code, non_snake_case)]
fn extract_preserved_effects_STUB(surface: &str, core: &str) -> Vec<String> {
    let candidate_effects = [
        "Sanctions",
        "DataPrivacy",
        "Aml",
        "Kyc",
        "Tax",
        "Securities",
        "Corporate",
        "Custody",
        "Banking",
        "Payments",
        "Licensing",
        "DigitalAssets",
        "Employment",
        "Immigration",
        "Arbitration",
        "Trade",
        "Insurance",
        "AntiBribery",
    ];

    candidate_effects
        .iter()
        .filter(|eff| surface.contains(*eff) && core.contains(*eff))
        .map(|eff| eff.to_string())
        .collect()
}

/// Convert UNIX epoch seconds to an ISO 8601 UTC timestamp string.
///
/// Produces `YYYY-MM-DDTHH:MM:SSZ` without pulling in `chrono`. RETAINED
/// for the public API that will issue certificates once the structural
/// preservation check is implemented.
#[allow(dead_code)]
fn unix_secs_to_iso8601(epoch_secs: u64) -> String {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn produce_certificate_refuses_without_structural_check() {
        let surface = "rule check_sanctions { match entity { Sanctioned => NonCompliant } }";
        let core = "rule check_sanctions { match entity { Sanctioned => NonCompliant } }";
        let err = produce_elaboration_certificate(surface, core).unwrap_err();
        assert_eq!(err, ElaborationCertError::PreservationCheckUnimplemented);
    }

    #[test]
    fn verify_valid_manually_constructed_certificate() {
        // The public API refuses to issue certificates until the structural
        // preservation walk is implemented; construct one by hand here
        // solely to exercise `verify_elaboration_certificate`'s invariants.
        let cert = ElaborationCertificate {
            surface_hash: "ab".repeat(32),
            core_hash: "cd".repeat(32),
            refinement_predicates_preserved: vec!["exhaustive_match".to_string()],
            effects_preserved: vec!["Sanctions".to_string()],
            certified_at: "2026-04-15T00:00:00Z".to_string(),
            certificate_digest: "ef".repeat(32),
        };
        assert!(verify_elaboration_certificate(&cert));
    }

    #[test]
    fn verify_rejects_empty_surface_hash() {
        let cert = ElaborationCertificate {
            surface_hash: String::new(),
            core_hash: "ab".repeat(32),
            refinement_predicates_preserved: vec!["exhaustive_match".to_string()],
            effects_preserved: vec![],
            certified_at: "2026-04-15T00:00:00Z".to_string(),
            certificate_digest: "cd".repeat(32),
        };
        assert!(!verify_elaboration_certificate(&cert));
    }

    #[test]
    fn verify_rejects_empty_predicates() {
        let cert = ElaborationCertificate {
            surface_hash: "ab".repeat(32),
            core_hash: "cd".repeat(32),
            refinement_predicates_preserved: vec![],
            effects_preserved: vec![],
            certified_at: "2026-04-15T00:00:00Z".to_string(),
            certificate_digest: "ef".repeat(32),
        };
        assert!(!verify_elaboration_certificate(&cert));
    }

    #[test]
    fn produce_rejects_empty_source() {
        let err = produce_elaboration_certificate("", "core output").unwrap_err();
        assert_eq!(err, ElaborationCertError::EmptySource);
    }

    #[test]
    fn produce_rejects_empty_output() {
        let err = produce_elaboration_certificate("surface source", "").unwrap_err();
        assert_eq!(err, ElaborationCertError::EmptyOutput);
    }

    #[test]
    fn stub_substring_logic_still_detects_keywords_for_reference() {
        // Sanity-check that the withdrawn substring detectors, preserved
        // under `_STUB` names for reference, still behave as before. This
        // documents the old (unsound) behavior so reviewers can see what
        // was replaced.
        let surface_a = "rule a { match x { A => let y = 1 in y } }";
        let core_a = "rule a { match x { A => let y = 1 in y } }";
        let predicates = extract_preserved_predicates_STUB(surface_a, core_a);
        assert!(predicates.contains(&"exhaustive_match".to_string()));
        assert!(predicates.contains(&"let_binding".to_string()));

        let surface_b = "rule r { effect Sanctions; match x { A => let y = 1 in y } }";
        let core_b = "rule r { effect Sanctions; match x { A => let y = 1 in y } }";
        let effects = extract_preserved_effects_STUB(surface_b, core_b);
        assert!(effects.contains(&"Sanctions".to_string()));
    }

    #[test]
    fn effect_extractor_public_api_refuses_without_structural_check() {
        let surface = "rule r { effect Sanctions; match x { A => let y = 1 in y } }";
        let core = "rule r { effect Sanctions; match x { A => let y = 1 in y } }";
        let err = extract_preserved_effects(surface, core).unwrap_err();
        assert_eq!(err, ElaborationCertError::PreservationCheckUnimplemented);
    }

    #[test]
    fn predicate_extractor_public_api_refuses_without_structural_check() {
        let surface = "rule r { match x { A => let y = 1 in y } }";
        let core = "rule r { match x { A => let y = 1 in y } }";
        let err = extract_preserved_predicates(surface, core).unwrap_err();
        assert_eq!(err, ElaborationCertError::PreservationCheckUnimplemented);
    }

    #[test]
    fn scope_closure_certificate_construction() {
        let cert = ScopeClosureCertificate {
            fiber_id: "fiber-ibc-s66-min-directors".to_string(),
            free_identifiers: vec![
                FreeIdentifierBinding {
                    name: "is_sanctioned".to_string(),
                    definition_site: "prelude".to_string(),
                },
                FreeIdentifierBinding {
                    name: "check_kyc".to_string(),
                    definition_site: "prelude".to_string(),
                },
            ],
            capture_free: true,
        };

        assert_eq!(cert.fiber_id, "fiber-ibc-s66-min-directors");
        assert_eq!(cert.free_identifiers.len(), 2);
        assert!(cert.capture_free);

        // Serde roundtrip
        let json = serde_json::to_string(&cert).unwrap();
        let deserialized: ScopeClosureCertificate = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, cert);
    }

    #[test]
    fn serde_roundtrip_elaboration_certificate() {
        // Construct by hand — the public API refuses to issue a certificate
        // until the structural preservation check is implemented.
        let cert = ElaborationCertificate {
            surface_hash: "ab".repeat(32),
            core_hash: "cd".repeat(32),
            refinement_predicates_preserved: vec!["exhaustive_match".to_string()],
            effects_preserved: vec!["Sanctions".to_string()],
            certified_at: "2026-04-15T00:00:00Z".to_string(),
            certificate_digest: "ef".repeat(32),
        };

        let json = serde_json::to_string(&cert).unwrap();
        let deserialized: ElaborationCertificate = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, cert);
    }
}
