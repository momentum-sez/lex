//! Commitment 5 — Proof summary layer.
//!
//! Every proof term has an associated human-readable summary produced by
//! verified compilation that preserves semantic fidelity at lower granularity.
//! Regulators read summaries; auditors verify proofs; both are supported.
//!
//! The summary preserves three invariants (property-tested below):
//!
//! 1. **Obligation preservation** — every obligation in the proof appears
//!    in the summary's obligation set (possibly aggregated, never elided).
//! 2. **Verdict preservation** — the summary-level verdict equals the
//!    proof-level verdict.
//! 3. **Discretion preservation** — every unfilled hole in the proof
//!    appears in the summary's discretion frontier.

use super::cert::{DerivationCertificate, Verdict};
use super::digest::sha256_hex;
use super::hole::HoleId;
use super::monotone::FourTuple;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

/// A summary of a derivation. Semantic fidelity at lower granularity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofSummary {
    /// One-line narrative summary of the evaluation (regulator-facing).
    pub narrative: String,
    /// Aggregated obligation categories (preserved from the proof).
    pub obligations: BTreeSet<String>,
    /// Verdict carried forward from the proof.
    pub verdict: Verdict,
    /// Discretion frontier carried forward (names and authorities preserved).
    pub discretion_frontier: Vec<DiscretionFrontierEntry>,
    /// 4-tuple scope.
    pub four_tuple: FourTuple,
    /// Digest of the underlying proof.
    pub proof_digest: String,
    /// Summary's own digest.
    pub summary_digest: String,
}

/// An entry in the summary's discretion frontier.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiscretionFrontierEntry {
    pub hole_id: HoleId,
    pub authority_id: String,
    /// Human-readable description of the judgment demanded (may abstract
    /// the term body).
    pub description: String,
}

/// Compile a [`ProofSummary`] from a [`DerivationCertificate`] and the
/// observable obligation set.
///
/// `obligations` is the set of obligation categories (from the proof's
/// obligation tracker). The summary's obligation set is their `BTreeSet`
/// closure — duplicates are merged, but no category is elided (preserving
/// invariant 1).
pub fn compile_summary(
    cert: &DerivationCertificate,
    obligations: impl IntoIterator<Item = String>,
    hole_descriptions: &[(HoleId, String, String)], // (id, authority_id, description)
) -> ProofSummary {
    let obligations: BTreeSet<String> = obligations.into_iter().collect();

    let mut discretion_frontier: Vec<DiscretionFrontierEntry> = cert
        .discretion_frontier
        .iter()
        .map(|id| {
            let (authority_id, description) = hole_descriptions
                .iter()
                .find(|(hid, _, _)| hid == id)
                .map(|(_, a, d)| (a.clone(), d.clone()))
                .unwrap_or_else(|| ("unknown".to_string(), "unfilled hole".to_string()));
            DiscretionFrontierEntry {
                hole_id: id.clone(),
                authority_id,
                description,
            }
        })
        .collect();
    discretion_frontier.sort_by(|a, b| a.hole_id.cmp(&b.hole_id));

    let narrative = narrative_for(cert);

    let mut summary = ProofSummary {
        narrative,
        obligations,
        verdict: cert.verdict,
        discretion_frontier,
        four_tuple: cert.four_tuple.clone(),
        proof_digest: cert.proof_digest.clone(),
        summary_digest: String::new(),
    };
    summary.summary_digest = sha256_hex(&summary);
    summary
}

fn narrative_for(cert: &DerivationCertificate) -> String {
    let verdict = match cert.verdict {
        Verdict::Compliant => "compliant",
        Verdict::NonCompliant => "non-compliant",
        Verdict::Pending => "pending",
        Verdict::NotApplicable => "not applicable",
        Verdict::Indeterminate => "indeterminate",
    };
    if cert.mechanical_check {
        format!(
            "Under tribunal {} in jurisdiction {} (version {}, asof {}): {} (mechanical).",
            cert.four_tuple.tribunal,
            cert.four_tuple.jurisdiction,
            cert.four_tuple.version,
            cert.four_tuple.time,
            verdict
        )
    } else {
        format!(
            "Under tribunal {} in jurisdiction {} (version {}, asof {}): {} ({} outstanding discretionary judgment(s)).",
            cert.four_tuple.tribunal,
            cert.four_tuple.jurisdiction,
            cert.four_tuple.version,
            cert.four_tuple.time,
            verdict,
            cert.discretion_frontier.len()
        )
    }
}

// ---------------------------------------------------------------------------
// Preservation invariants (exposed as functions for property testing).
// ---------------------------------------------------------------------------

/// Verify invariant 1: every obligation in `source` appears in `summary.obligations`.
pub fn check_obligation_preservation(summary: &ProofSummary, source: &[String]) -> bool {
    source.iter().all(|o| summary.obligations.contains(o))
}

/// Verify invariant 2: verdict preservation.
pub fn check_verdict_preservation(summary: &ProofSummary, cert: &DerivationCertificate) -> bool {
    summary.verdict == cert.verdict
}

/// Verify invariant 3: every unfilled hole in `cert` appears in
/// `summary.discretion_frontier`.
pub fn check_discretion_preservation(
    summary: &ProofSummary,
    cert: &DerivationCertificate,
) -> bool {
    cert.discretion_frontier.iter().all(|h| {
        summary
            .discretion_frontier
            .iter()
            .any(|e| &e.hole_id == h)
    })
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

    fn cert_mechanical() -> DerivationCertificate {
        DerivationCertificate::build(
            ft(),
            "pd".into(),
            "sd".into(),
            vec![],
            BTreeSet::new(),
            Verdict::Compliant,
        )
        .unwrap()
    }

    fn cert_with_frontier(ids: &[&str]) -> DerivationCertificate {
        let frontier: BTreeSet<HoleId> = ids.iter().map(|s| HoleId(s.to_string())).collect();
        DerivationCertificate::build(
            ft(),
            "pd".into(),
            "sd".into(),
            vec![],
            frontier,
            Verdict::Pending,
        )
        .unwrap()
    }

    #[test]
    fn summary_preserves_obligations() {
        let cert = cert_mechanical();
        let obligations = vec![
            "ExhaustiveMatch".to_string(),
            "ThresholdComparison".to_string(),
        ];
        let summary = compile_summary(&cert, obligations.clone(), &[]);
        assert!(check_obligation_preservation(&summary, &obligations));
    }

    #[test]
    fn summary_preserves_verdict() {
        let cert = cert_mechanical();
        let summary = compile_summary(&cert, vec![], &[]);
        assert!(check_verdict_preservation(&summary, &cert));
        assert_eq!(summary.verdict, Verdict::Compliant);
    }

    #[test]
    fn summary_preserves_discretion_frontier() {
        let cert = cert_with_frontier(&["h1", "h2"]);
        let summary = compile_summary(
            &cert,
            vec![],
            &[
                (
                    HoleId("h1".into()),
                    "ADGM-FSRA".into(),
                    "fit and proper".into(),
                ),
                (
                    HoleId("h2".into()),
                    "Adjudicator".into(),
                    "material adverse change".into(),
                ),
            ],
        );
        assert!(check_discretion_preservation(&summary, &cert));
        assert_eq!(summary.discretion_frontier.len(), 2);
    }

    #[test]
    fn summary_obligations_deduplicate_but_never_elide() {
        let cert = cert_mechanical();
        let obligations = vec![
            "A".to_string(),
            "A".to_string(),
            "B".to_string(),
            "A".to_string(),
        ];
        let summary = compile_summary(&cert, obligations, &[]);
        assert_eq!(summary.obligations.len(), 2);
        assert!(summary.obligations.contains("A"));
        assert!(summary.obligations.contains("B"));
    }

    #[test]
    fn summary_narrative_mentions_tribunal() {
        let cert = cert_mechanical();
        let summary = compile_summary(&cert, vec![], &[]);
        assert!(summary.narrative.contains("ADGM-FSRA"));
        assert!(summary.narrative.contains("mechanical"));
    }

    #[test]
    fn summary_narrative_reports_frontier_count() {
        let cert = cert_with_frontier(&["h1", "h2", "h3"]);
        let summary = compile_summary(&cert, vec![], &[]);
        assert!(summary.narrative.contains("3 outstanding"));
    }

    #[test]
    fn summary_digest_is_populated() {
        let cert = cert_mechanical();
        let summary = compile_summary(&cert, vec![], &[]);
        assert!(!summary.summary_digest.is_empty());
    }
}
