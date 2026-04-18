//! Fiber composition for multi-fiber compliance evaluation.
//!
//! A "fiber" is a single compliance rule (a Lex term) evaluated against an
//! entity context. Multiple fibers may target the same compliance domain
//! for the same entity — for instance, an AML fiber from the Seychelles IBC
//! Act and a separate AML fiber from a cross-border treaty.
//!
//! This module composes multiple fiber results into a per-domain compliance
//! assessment using the **meet** operation on the compliance lattice:
//!
//! - `NonCompliant` absorbs everything (worst wins).
//! - `Pending` dominates `Compliant` but yields to `NonCompliant`.
//! - `Compliant` is the top (best case).
//!
//! These semantics match `mez-tensor::ComplianceState::meet()` — the
//! composition is pessimistic, ensuring that a single failing fiber for a
//! domain blocks the domain.

use std::collections::BTreeMap;

#[cfg(not(feature = "kernel-integration"))]
use mez_core_min::ComplianceDomain;
#[cfg(feature = "kernel-integration")]
use mez_core::ComplianceDomain;
use serde::{Deserialize, Serialize};

use crate::ast::Term;
use crate::certificate::{ComplianceVerdict, LexCertificate};

// ---------------------------------------------------------------------------
// verdict_meet — lattice meet for ComplianceVerdict
// ---------------------------------------------------------------------------

/// Lattice ordering value for a verdict. Lower is more restrictive.
///
/// `NonCompliant = 0 < Pending = 1 < Compliant = 2`
fn verdict_rank(v: ComplianceVerdict) -> u8 {
    match v {
        ComplianceVerdict::NonCompliant => 0,
        ComplianceVerdict::Pending => 1,
        ComplianceVerdict::Compliant => 2,
    }
}

/// Lattice meet (greatest lower bound) — pessimistic composition.
///
/// Returns the more restrictive of the two verdicts. This is the core
/// operation for composing multiple fiber results for the same domain.
///
/// # Security invariant
///
/// `NonCompliant` is absorbing: `verdict_meet(x, NonCompliant) == NonCompliant`
/// for all x. A single non-compliant fiber blocks the domain.
pub fn verdict_meet(a: ComplianceVerdict, b: ComplianceVerdict) -> ComplianceVerdict {
    if verdict_rank(a) <= verdict_rank(b) {
        a
    } else {
        b
    }
}

// ---------------------------------------------------------------------------
// FiberContext — entity context for fiber evaluation
// ---------------------------------------------------------------------------

/// The runtime context against which fibers are evaluated.
///
/// Carries the entity facts needed by Lex rule terms. This is a
/// string-keyed map because the set of facts varies by jurisdiction
/// and entity classification. Type-safe access is enforced by the
/// rule terms themselves (via pattern matching on expected keys).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FiberContext {
    /// Entity identifier.
    pub entity_id: String,
    /// Jurisdiction code (e.g., "sc", "adgm", "pk").
    pub jurisdiction: String,
    /// Key-value facts about the entity (e.g., "entity_type" -> "IBC").
    pub facts: BTreeMap<String, String>,
}

// ---------------------------------------------------------------------------
// FiberResult — the output of a single fiber evaluation
// ---------------------------------------------------------------------------

/// Result of evaluating a single compliance fiber.
///
/// A fiber is a (rule term, domain) pair. Evaluating it against an entity
/// context produces a verdict and optionally a proof certificate.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FiberResult {
    /// Unique identifier for this fiber (e.g., "sc_ibc_aml_001").
    pub fiber_id: String,
    /// The compliance domain this fiber targets.
    pub domain: ComplianceDomain,
    /// The compliance verdict from evaluation.
    pub verdict: ComplianceVerdict,
    /// Optional proof certificate (present when the decision procedure
    /// produces a witness).
    pub certificate: Option<LexCertificate>,
}

// ---------------------------------------------------------------------------
// compose_fiber_results — domain-level meet over fibers
// ---------------------------------------------------------------------------

/// Compose multiple fiber results into a per-domain compliance assessment.
///
/// For each domain that appears in the fiber results:
/// - If **any** fiber returns `NonCompliant`, the domain is `NonCompliant`.
/// - If **all** fibers return `Compliant`, the domain is `Compliant`.
/// - If any fiber returns `Pending` and none returns `NonCompliant`, the
///   domain is `Pending`.
///
/// This is the meet operation on the compliance lattice, applied per domain.
/// Domains with no fibers do not appear in the output.
pub fn compose_fiber_results(
    results: &[FiberResult],
) -> BTreeMap<ComplianceDomain, ComplianceVerdict> {
    let mut domain_verdicts: BTreeMap<ComplianceDomain, ComplianceVerdict> = BTreeMap::new();

    for result in results {
        let entry = domain_verdicts
            .entry(result.domain)
            .or_insert(ComplianceVerdict::Compliant);
        *entry = verdict_meet(*entry, result.verdict);
    }

    domain_verdicts
}

// ---------------------------------------------------------------------------
// evaluate_all_fibers — apply fibers to a context
// ---------------------------------------------------------------------------

/// Apply all registered fibers for a jurisdiction to an entity context.
///
/// Each fiber is a `(fiber_id, rule_term)` pair. Evaluation runs the
/// decision procedure against the runtime context and produces a
/// `FiberResult` per fiber.
///
/// The jurisdiction parameter filters which fibers are applicable.
/// Fibers that do not match the context's jurisdiction are skipped.
///
/// # Current implementation
///
/// This is a structural stub that maps each fiber to a `Pending` verdict.
/// When `evaluate.rs` is created by the parallel agent, this function
/// will delegate to the full Lex evaluation pipeline (elaborate ->
/// typecheck -> decide -> certificate).
#[must_use]
pub fn evaluate_all_fibers(
    fibers: &[(String, Term)],
    context: &FiberContext,
    jurisdiction: &str,
) -> Vec<FiberResult> {
    tracing::warn!(
        entity_id = %context.entity_id,
        jurisdiction = %jurisdiction,
        fiber_count = fibers.len(),
        "evaluate_all_fibers is a stub — all verdicts will be Pending"
    );
    if context.jurisdiction != jurisdiction {
        return Vec::new();
    }

    fibers
        .iter()
        .filter_map(|(fiber_id, _rule_term)| {
            domain_from_fiber_id(fiber_id).map(|domain| FiberResult {
                fiber_id: fiber_id.clone(),
                domain,
                verdict: ComplianceVerdict::Pending,
                certificate: None,
            })
        })
        .collect()
}

/// Extract the compliance domain from a fiber ID by convention.
///
/// Fiber IDs follow the pattern `{jurisdiction}_{domain}_{sequence}`,
/// e.g., `sc_aml_001`, `adgm_sanctions_002`. This function parses the
/// domain segment. Returns `None` if the domain segment cannot be
/// recognized, so the caller can decide how to handle the unknown fiber.
fn domain_from_fiber_id(fiber_id: &str) -> Option<ComplianceDomain> {
    let parts: Vec<&str> = fiber_id.split('_').collect();
    if parts.len() >= 2 {
        // Try single-segment domain first, then two-segment (e.g., "data_privacy")
        if let Ok(domain) = parts[1].parse::<ComplianceDomain>() {
            return Some(domain);
        }
        if parts.len() >= 3 {
            let two_seg = format!("{}_{}", parts[1], parts[2]);
            if let Ok(domain) = two_seg.parse::<ComplianceDomain>() {
                return Some(domain);
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // ── Helpers ────────────────────────────────────────────────────────

    fn fiber(id: &str, domain: ComplianceDomain, verdict: ComplianceVerdict) -> FiberResult {
        FiberResult {
            fiber_id: id.to_string(),
            domain,
            verdict,
            certificate: None,
        }
    }

    fn context(entity_id: &str, jurisdiction: &str) -> FiberContext {
        FiberContext {
            entity_id: entity_id.to_string(),
            jurisdiction: jurisdiction.to_string(),
            facts: BTreeMap::new(),
        }
    }

    // ── verdict_meet lattice tests ────────────────────────────────────

    #[test]
    fn verdict_rank_ordering() {
        assert!(verdict_rank(ComplianceVerdict::NonCompliant) < verdict_rank(ComplianceVerdict::Pending));
        assert!(verdict_rank(ComplianceVerdict::Pending) < verdict_rank(ComplianceVerdict::Compliant));
        assert!(verdict_rank(ComplianceVerdict::NonCompliant) < verdict_rank(ComplianceVerdict::Compliant));
    }

    #[test]
    fn meet_noncompliant_absorbs() {
        assert_eq!(
            verdict_meet(ComplianceVerdict::Compliant, ComplianceVerdict::NonCompliant),
            ComplianceVerdict::NonCompliant,
        );
        assert_eq!(
            verdict_meet(ComplianceVerdict::NonCompliant, ComplianceVerdict::Compliant),
            ComplianceVerdict::NonCompliant,
        );
        assert_eq!(
            verdict_meet(ComplianceVerdict::Pending, ComplianceVerdict::NonCompliant),
            ComplianceVerdict::NonCompliant,
        );
        assert_eq!(
            verdict_meet(ComplianceVerdict::NonCompliant, ComplianceVerdict::NonCompliant),
            ComplianceVerdict::NonCompliant,
        );
    }

    #[test]
    fn meet_pending_dominates_compliant() {
        assert_eq!(
            verdict_meet(ComplianceVerdict::Compliant, ComplianceVerdict::Pending),
            ComplianceVerdict::Pending,
        );
        assert_eq!(
            verdict_meet(ComplianceVerdict::Pending, ComplianceVerdict::Compliant),
            ComplianceVerdict::Pending,
        );
    }

    #[test]
    fn meet_compliant_is_identity() {
        assert_eq!(
            verdict_meet(ComplianceVerdict::Compliant, ComplianceVerdict::Compliant),
            ComplianceVerdict::Compliant,
        );
    }

    #[test]
    fn meet_is_commutative() {
        let pairs = [
            (ComplianceVerdict::Compliant, ComplianceVerdict::Pending),
            (ComplianceVerdict::Compliant, ComplianceVerdict::NonCompliant),
            (ComplianceVerdict::Pending, ComplianceVerdict::NonCompliant),
        ];
        for (a, b) in pairs {
            assert_eq!(
                verdict_meet(a, b),
                verdict_meet(b, a),
                "meet must be commutative for ({a:?}, {b:?})",
            );
        }
    }

    #[test]
    fn meet_is_associative() {
        let values = [
            ComplianceVerdict::Compliant,
            ComplianceVerdict::Pending,
            ComplianceVerdict::NonCompliant,
        ];
        for a in values {
            for b in values {
                for c in values {
                    assert_eq!(
                        verdict_meet(verdict_meet(a, b), c),
                        verdict_meet(a, verdict_meet(b, c)),
                        "meet must be associative for ({a:?}, {b:?}, {c:?})",
                    );
                }
            }
        }
    }

    #[test]
    fn meet_is_idempotent() {
        for v in [
            ComplianceVerdict::Compliant,
            ComplianceVerdict::Pending,
            ComplianceVerdict::NonCompliant,
        ] {
            assert_eq!(verdict_meet(v, v), v, "meet must be idempotent for {v:?}");
        }
    }

    // ── compose_fiber_results tests ───────────────────────────────────

    #[test]
    fn single_fiber_compliant() {
        let results = vec![fiber("f1", ComplianceDomain::Aml, ComplianceVerdict::Compliant)];
        let composed = compose_fiber_results(&results);

        assert_eq!(composed.len(), 1);
        assert_eq!(composed[&ComplianceDomain::Aml], ComplianceVerdict::Compliant);
    }

    #[test]
    fn single_fiber_noncompliant() {
        let results = vec![fiber(
            "f1",
            ComplianceDomain::Sanctions,
            ComplianceVerdict::NonCompliant,
        )];
        let composed = compose_fiber_results(&results);

        assert_eq!(composed.len(), 1);
        assert_eq!(
            composed[&ComplianceDomain::Sanctions],
            ComplianceVerdict::NonCompliant,
        );
    }

    #[test]
    fn single_fiber_pending() {
        let results = vec![fiber("f1", ComplianceDomain::Kyc, ComplianceVerdict::Pending)];
        let composed = compose_fiber_results(&results);

        assert_eq!(composed.len(), 1);
        assert_eq!(composed[&ComplianceDomain::Kyc], ComplianceVerdict::Pending);
    }

    #[test]
    fn multiple_fibers_same_domain_worst_verdict_wins() {
        // Two AML fibers: one compliant, one non-compliant. Meet = NonCompliant.
        let results = vec![
            fiber("aml_1", ComplianceDomain::Aml, ComplianceVerdict::Compliant),
            fiber(
                "aml_2",
                ComplianceDomain::Aml,
                ComplianceVerdict::NonCompliant,
            ),
        ];
        let composed = compose_fiber_results(&results);

        assert_eq!(composed.len(), 1);
        assert_eq!(composed[&ComplianceDomain::Aml], ComplianceVerdict::NonCompliant);
    }

    #[test]
    fn multiple_fibers_same_domain_pending_beats_compliant() {
        let results = vec![
            fiber("kyc_1", ComplianceDomain::Kyc, ComplianceVerdict::Compliant),
            fiber("kyc_2", ComplianceDomain::Kyc, ComplianceVerdict::Pending),
            fiber("kyc_3", ComplianceDomain::Kyc, ComplianceVerdict::Compliant),
        ];
        let composed = compose_fiber_results(&results);

        assert_eq!(composed.len(), 1);
        assert_eq!(composed[&ComplianceDomain::Kyc], ComplianceVerdict::Pending);
    }

    #[test]
    fn multiple_fibers_same_domain_all_compliant() {
        let results = vec![
            fiber("tax_1", ComplianceDomain::Tax, ComplianceVerdict::Compliant),
            fiber("tax_2", ComplianceDomain::Tax, ComplianceVerdict::Compliant),
        ];
        let composed = compose_fiber_results(&results);

        assert_eq!(composed.len(), 1);
        assert_eq!(composed[&ComplianceDomain::Tax], ComplianceVerdict::Compliant);
    }

    #[test]
    fn multiple_domains_independent_composition() {
        let results = vec![
            fiber("aml_1", ComplianceDomain::Aml, ComplianceVerdict::Compliant),
            fiber(
                "sanctions_1",
                ComplianceDomain::Sanctions,
                ComplianceVerdict::NonCompliant,
            ),
            fiber("kyc_1", ComplianceDomain::Kyc, ComplianceVerdict::Pending),
            fiber("tax_1", ComplianceDomain::Tax, ComplianceVerdict::Compliant),
        ];
        let composed = compose_fiber_results(&results);

        assert_eq!(composed.len(), 4);
        assert_eq!(composed[&ComplianceDomain::Aml], ComplianceVerdict::Compliant);
        assert_eq!(
            composed[&ComplianceDomain::Sanctions],
            ComplianceVerdict::NonCompliant,
        );
        assert_eq!(composed[&ComplianceDomain::Kyc], ComplianceVerdict::Pending);
        assert_eq!(composed[&ComplianceDomain::Tax], ComplianceVerdict::Compliant);
    }

    #[test]
    fn multiple_domains_with_multiple_fibers_per_domain() {
        let results = vec![
            // AML: compliant + compliant = compliant
            fiber("aml_1", ComplianceDomain::Aml, ComplianceVerdict::Compliant),
            fiber("aml_2", ComplianceDomain::Aml, ComplianceVerdict::Compliant),
            // Sanctions: compliant + noncompliant = noncompliant
            fiber(
                "sanc_1",
                ComplianceDomain::Sanctions,
                ComplianceVerdict::Compliant,
            ),
            fiber(
                "sanc_2",
                ComplianceDomain::Sanctions,
                ComplianceVerdict::NonCompliant,
            ),
            // KYC: pending + compliant = pending
            fiber("kyc_1", ComplianceDomain::Kyc, ComplianceVerdict::Pending),
            fiber("kyc_2", ComplianceDomain::Kyc, ComplianceVerdict::Compliant),
        ];
        let composed = compose_fiber_results(&results);

        assert_eq!(composed.len(), 3);
        assert_eq!(composed[&ComplianceDomain::Aml], ComplianceVerdict::Compliant);
        assert_eq!(
            composed[&ComplianceDomain::Sanctions],
            ComplianceVerdict::NonCompliant,
        );
        assert_eq!(composed[&ComplianceDomain::Kyc], ComplianceVerdict::Pending);
    }

    #[test]
    fn empty_fiber_list_produces_empty_map() {
        let composed = compose_fiber_results(&[]);
        assert!(composed.is_empty());
    }

    #[test]
    fn noncompliant_dominates_pending_in_same_domain() {
        let results = vec![
            fiber("f1", ComplianceDomain::Tax, ComplianceVerdict::Pending),
            fiber(
                "f2",
                ComplianceDomain::Tax,
                ComplianceVerdict::NonCompliant,
            ),
            fiber("f3", ComplianceDomain::Tax, ComplianceVerdict::Compliant),
        ];
        let composed = compose_fiber_results(&results);

        assert_eq!(
            composed[&ComplianceDomain::Tax],
            ComplianceVerdict::NonCompliant,
        );
    }

    // ── evaluate_all_fibers tests ─────────────────────────────────────

    #[test]
    fn evaluate_all_fibers_returns_pending_for_matching_jurisdiction() {
        let fibers = vec![
            ("sc_aml_001".to_string(), Term::prop()),
            ("sc_kyc_001".to_string(), Term::prop()),
        ];
        let ctx = context("entity-1", "sc");

        let results = evaluate_all_fibers(&fibers, &ctx, "sc");

        assert_eq!(results.len(), 2);
        for result in &results {
            assert_eq!(result.verdict, ComplianceVerdict::Pending);
        }
    }

    #[test]
    fn evaluate_all_fibers_skips_mismatched_jurisdiction() {
        let fibers = vec![("adgm_aml_001".to_string(), Term::prop())];
        let ctx = context("entity-1", "sc");

        let results = evaluate_all_fibers(&fibers, &ctx, "adgm");

        assert!(results.is_empty());
    }

    #[test]
    fn evaluate_all_fibers_empty_fibers() {
        let ctx = context("entity-1", "sc");
        let results = evaluate_all_fibers(&[], &ctx, "sc");
        assert!(results.is_empty());
    }

    // ── domain_from_fiber_id tests ────────────────────────────────────

    #[test]
    fn domain_from_fiber_id_parses_known_domains() {
        assert_eq!(domain_from_fiber_id("sc_aml_001"), Some(ComplianceDomain::Aml));
        assert_eq!(domain_from_fiber_id("sc_kyc_001"), Some(ComplianceDomain::Kyc));
        assert_eq!(
            domain_from_fiber_id("adgm_sanctions_001"),
            Some(ComplianceDomain::Sanctions),
        );
        assert_eq!(domain_from_fiber_id("pk_tax_001"), Some(ComplianceDomain::Tax));
    }

    #[test]
    fn domain_from_fiber_id_parses_two_segment_domains() {
        assert_eq!(
            domain_from_fiber_id("sc_data_privacy_001"),
            Some(ComplianceDomain::DataPrivacy),
        );
        assert_eq!(
            domain_from_fiber_id("adgm_digital_assets_001"),
            Some(ComplianceDomain::DigitalAssets),
        );
        assert_eq!(
            domain_from_fiber_id("sc_consumer_protection_001"),
            Some(ComplianceDomain::ConsumerProtection),
        );
        assert_eq!(
            domain_from_fiber_id("sc_anti_bribery_001"),
            Some(ComplianceDomain::AntiBribery),
        );
    }

    #[test]
    fn domain_from_fiber_id_returns_none_on_unknown() {
        assert_eq!(domain_from_fiber_id("sc_unknown_001"), None);
        assert_eq!(domain_from_fiber_id("bad"), None);
        assert_eq!(domain_from_fiber_id(""), None);
    }

    #[test]
    fn evaluate_all_fibers_skips_unrecognized_domain() {
        let fibers = vec![
            ("sc_aml_001".to_string(), Term::prop()),
            ("sc_bogus_001".to_string(), Term::prop()),
        ];
        let ctx = context("entity-1", "sc");
        let results = evaluate_all_fibers(&fibers, &ctx, "sc");
        // Only the recognized fiber is returned; the bogus one is skipped.
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].fiber_id, "sc_aml_001");
    }

    // ── Serde roundtrip ──────────────────────────────────────────────

    #[test]
    fn fiber_result_serde_roundtrip() {
        let result = fiber("sc_aml_001", ComplianceDomain::Aml, ComplianceVerdict::Compliant);
        let json = serde_json::to_string(&result).unwrap();
        let parsed: FiberResult = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.fiber_id, "sc_aml_001");
        assert_eq!(parsed.domain, ComplianceDomain::Aml);
        assert_eq!(parsed.verdict, ComplianceVerdict::Compliant);
    }

    #[test]
    fn runtime_context_serde_roundtrip() {
        let mut ctx = context("entity-42", "sc");
        ctx.facts.insert("entity_type".to_string(), "IBC".to_string());
        ctx.facts.insert("registered_agent".to_string(), "true".to_string());

        let json = serde_json::to_string(&ctx).unwrap();
        let parsed: FiberContext = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.entity_id, "entity-42");
        assert_eq!(parsed.jurisdiction, "sc");
        assert_eq!(parsed.facts.len(), 2);
        assert_eq!(parsed.facts["entity_type"], "IBC");
    }
}
