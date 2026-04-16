//! Integration tests for the Lex core calculus frontier.
//!
//! The worked examples from `docs/frontier-work/08-lex-core-calculus.md` §4
//! are exercised end-to-end here: construct a hole, fill it, compile a
//! summary, produce a certificate, verify cross-module invariants.

use super::cert::{DerivationCertificate, DiscretionStep, Verdict};
use super::hole::{
    Authority, AuthorityError, FilledHoleRecord, Hole, HoleId, NamedAuthority, PCAuthWitness,
    ScopeConstraint,
};
use super::monotone::{FourTuple, Proof};
use super::oracle::{Horizon, OracleResponse, WitnessSupplyOracle};
use super::principle::{CaseCategory, PriorityGraph, PrincipleId, ProductNode};
use super::summary::{
    check_discretion_preservation, check_obligation_preservation, check_verdict_preservation,
    compile_summary,
};
use super::temporal::{Asof, RewriteKind, RewriteWitness};
use crate::ast::{QualIdent, Term};
use std::collections::BTreeSet;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn adgm_fsra() -> NamedAuthority {
    NamedAuthority {
        id: "ADGM-FSRA".into(),
        public_key_hash: "pk:adgm-fsra".into(),
    }
}

fn adjudicator() -> NamedAuthority {
    NamedAuthority {
        id: "CreditAgreementAdjudicator".into(),
        public_key_hash: "pk:adjudicator".into(),
    }
}

fn national_regulator() -> NamedAuthority {
    NamedAuthority {
        id: "NationalRegulator".into(),
        public_key_hash: "pk:national".into(),
    }
}

fn witness_for(authority: &NamedAuthority) -> PCAuthWitness {
    PCAuthWitness {
        signer_public_key_hash: authority.public_key_hash.clone(),
        signature: vec![0xab, 0xcd],
        signed_at: "2026-04-15T00:00:00Z".into(),
        cryptographic_epoch: 1,
    }
}

fn ft(tribunal: &str, jurisdiction: &str) -> FourTuple {
    FourTuple {
        time: "2026-04-15T00:00:00Z".into(),
        jurisdiction: jurisdiction.into(),
        version: "v2026.04.15".into(),
        tribunal: tribunal.into(),
    }
}

// ---------------------------------------------------------------------------
// Worked example 4.1 — fit and proper person
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct FitAndProper {
    pub fit: bool,
    pub basis: String,
}

#[test]
fn worked_example_fit_and_proper() {
    let hole: Hole<FitAndProper, _> = Hole::new(
        Some("fit_check"),
        adgm_fsra(),
        ScopeConstraint {
            jurisdiction: Some("ADGM".into()),
            entity_class: Some("Principal".into()),
            ..Default::default()
        },
        Term::Constant(QualIdent::simple("FitAndProperJudgment")),
    );

    // Before filling, the discretion frontier is non-empty.
    let mut frontier = BTreeSet::new();
    frontier.insert(hole.id().clone());
    let pending_cert = DerivationCertificate::build(
        ft("ADGM-FSRA", "ADGM"),
        "pd".into(),
        "sd".into(),
        vec![],
        frontier,
        Verdict::Pending,
    )
    .unwrap();
    assert!(!pending_cert.mechanical_check);
    assert_eq!(pending_cert.verdict, Verdict::Pending);

    // Fill the hole.
    let filled = hole
        .fill(
            FitAndProper {
                fit: true,
                basis: "on-site inspection, 2026-04-10".into(),
            },
            witness_for(&adgm_fsra()),
        )
        .expect("valid witness");
    let record = filled.to_record(ft("ADGM-FSRA", "ADGM"));

    // Build a post-fill certificate with empty frontier.
    let cert = DerivationCertificate::build(
        ft("ADGM-FSRA", "ADGM"),
        "pd".into(),
        "sd".into(),
        vec![DiscretionStep {
            record,
            rationale_digest: None,
        }],
        BTreeSet::new(),
        Verdict::Compliant,
    )
    .unwrap();
    assert!(cert.mechanical_check);
    assert_eq!(cert.discretion_steps.len(), 1);
    assert_eq!(cert.verdict, Verdict::Compliant);
}

// ---------------------------------------------------------------------------
// Worked example 4.2 — material adverse change
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct MaterialAdverseChange {
    pub material: bool,
    pub rationale: String,
}

#[test]
fn worked_example_material_adverse_change() {
    // asof is stratum-0.
    let asof = Asof::<0>::freeze("2026-04-15T00:00:00Z");

    // Time window: asof - 90 days .. asof. Encoded as ISO strings here.
    let hole: Hole<MaterialAdverseChange, _> = Hole::new(
        Some("mac_event"),
        adjudicator(),
        ScopeConstraint {
            time_window: Some((
                "2026-01-15T00:00:00Z".into(),
                "2026-04-15T00:00:00Z".into(),
            )),
            entity_class: Some("Borrower".into()),
            ..Default::default()
        },
        Term::Constant(QualIdent::simple("MaterialAdverseChange")),
    );

    // The mechanical branch (hard covenant breach) is absent; the adjudicator
    // fills the hole with a "not material" verdict.
    let filled = hole
        .fill(
            MaterialAdverseChange {
                material: false,
                rationale: "no change in creditworthiness within 90-day window".into(),
            },
            witness_for(&adjudicator()),
        )
        .expect("adjudicator authorized");

    let record = filled.to_record(ft("CreditAgreementAdjudicator", "NY"));
    let cert = DerivationCertificate::build(
        ft("CreditAgreementAdjudicator", "NY"),
        "pd".into(),
        "sd".into(),
        vec![DiscretionStep {
            record,
            rationale_digest: None,
        }],
        BTreeSet::new(),
        Verdict::Compliant,
    )
    .unwrap();

    // asof-0 is preserved.
    let (asof_iso, _token) = asof.into_frozen();
    assert_eq!(asof_iso, "2026-04-15T00:00:00Z");
    assert!(cert.mechanical_check);
}

// ---------------------------------------------------------------------------
// Worked example 4.3 — adequate systems and controls (Basel III)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct SystemsAndControls {
    pub overlay_bp: i32,
    pub finding_summary: String,
}

#[test]
fn worked_example_systems_and_controls_awaiting_regulator() {
    let hole: Hole<SystemsAndControls, _> = Hole::new(
        Some("sys_controls"),
        national_regulator(),
        ScopeConstraint {
            time_window: Some((
                "2025-04-15T00:00:00Z".into(),
                "2026-04-15T00:00:00Z".into(),
            )),
            entity_class: Some("DepositoryInstitution".into()),
            ..Default::default()
        },
        Term::Constant(QualIdent::simple("SystemsAndControlsAdjustment")),
    );

    // Nothing filled yet — certificate must be Pending.
    let mut frontier = BTreeSet::new();
    frontier.insert(hole.id().clone());

    let cert = DerivationCertificate::build(
        ft("NationalRegulator", "US"),
        "pd".into(),
        "sd".into(),
        vec![],
        frontier,
        Verdict::Pending,
    )
    .unwrap();

    assert!(!cert.mechanical_check);
    assert_eq!(cert.verdict, Verdict::Pending);
    assert_eq!(cert.discretion_frontier.len(), 1);

    // Regulator shows up with a different key — reject.
    let wrong_key = PCAuthWitness {
        signer_public_key_hash: "pk:imposter".into(),
        signature: vec![1],
        signed_at: "2026-04-15T00:00:00Z".into(),
        cryptographic_epoch: 1,
    };
    let rejected = hole.fill(
        SystemsAndControls {
            overlay_bp: 200,
            finding_summary: "systems gaps".into(),
        },
        wrong_key,
    );
    assert!(matches!(
        rejected,
        Err(AuthorityError::SignerMismatch { .. })
    ));
}

// ---------------------------------------------------------------------------
// Cross-module invariants
// ---------------------------------------------------------------------------

#[test]
fn summary_round_trip_through_certificate() {
    let mut frontier = BTreeSet::new();
    frontier.insert(HoleId("h1".into()));
    let cert = DerivationCertificate::build(
        ft("ADGM-FSRA", "ADGM"),
        "pd".into(),
        "sd".into(),
        vec![],
        frontier,
        Verdict::Pending,
    )
    .unwrap();
    let obligations = vec!["ExhaustiveMatch".to_string(), "Decidability".to_string()];
    let summary = compile_summary(
        &cert,
        obligations.clone(),
        &[(HoleId("h1".into()), "ADGM-FSRA".into(), "fit check".into())],
    );
    assert!(check_obligation_preservation(&summary, &obligations));
    assert!(check_verdict_preservation(&summary, &cert));
    assert!(check_discretion_preservation(&summary, &cert));
}

#[test]
fn four_tuple_proof_composes_within_scope() {
    struct ADGM;
    struct V1;
    struct T2026;
    struct FSRA;
    let p: Proof<T2026, ADGM, V1, FSRA, u32> = Proof::axiom(1);
    let q: Proof<T2026, ADGM, V1, FSRA, u32> = Proof::axiom(2);
    let r = p.and(q);
    assert_eq!(r.witness(), &(1, 2));
}

#[test]
fn temporal_stratification_preserves_asof0_source() {
    let t0 = Asof::<0>::freeze("2026-01-01T00:00:00Z");
    let w = RewriteWitness::new(
        RewriteKind::Tolling,
        "Limitation Act s.28",
        "2026-07-01T00:00:00Z",
    );
    let t1 = t0.lift0(w);
    assert_eq!(t1.source_asof0(), Some("2026-01-01T00:00:00Z"));
    assert_eq!(t1.iso8601(), "2026-07-01T00:00:00Z");
}

#[test]
fn principle_graph_acyclicity_passes_for_dag() {
    let mut g = PriorityGraph::new();
    g.add_edge(
        ProductNode {
            principle: PrincipleId("life".into()),
            category: CaseCategory("emergency".into()),
        },
        ProductNode {
            principle: PrincipleId("property".into()),
            category: CaseCategory("emergency".into()),
        },
    );
    assert!(g.check_acyclic().is_ok());
}

#[test]
fn principle_graph_acyclicity_rejects_cycle() {
    let mut g = PriorityGraph::new();
    g.add_edge(
        ProductNode {
            principle: PrincipleId("a".into()),
            category: CaseCategory("x".into()),
        },
        ProductNode {
            principle: PrincipleId("b".into()),
            category: CaseCategory("x".into()),
        },
    );
    g.add_edge(
        ProductNode {
            principle: PrincipleId("b".into()),
            category: CaseCategory("x".into()),
        },
        ProductNode {
            principle: PrincipleId("a".into()),
            category: CaseCategory("x".into()),
        },
    );
    assert!(g.check_acyclic().is_err());
}

#[test]
fn oracle_beyond_horizon_emits_hole() {
    use super::oracle::{UBOOracle, UBOQuery};
    let edges: std::collections::BTreeSet<(String, String)> = [
        ("a", "b"),
        ("b", "c"),
        ("c", "d"),
        ("d", "e"),
        ("e", "f"),
    ]
    .iter()
    .map(|(x, y)| (x.to_string(), y.to_string()))
    .collect();
    let o = UBOOracle::new("ubo-v2", edges);
    let r: OracleResponse<_> = o.supply_bounded_horizon(UBOQuery { root: "a".into() }, Horizon(2));
    assert!(!r.is_complete());
    assert!(r.beyond_horizon.is_some());
    assert_eq!(r.oracle_id, "ubo-v2");
}

#[test]
fn certificate_is_content_addressed() {
    let c1 = DerivationCertificate::build(
        ft("ADGM-FSRA", "ADGM"),
        "pd".into(),
        "sd".into(),
        vec![],
        BTreeSet::new(),
        Verdict::Compliant,
    )
    .unwrap();
    let c2 = DerivationCertificate::build(
        ft("ADGM-FSRA", "ADGM"),
        "pd".into(),
        "sd".into(),
        vec![],
        BTreeSet::new(),
        Verdict::Compliant,
    )
    .unwrap();
    assert_eq!(c1.certificate_digest, c2.certificate_digest);
    // Different scope yields different digest.
    let c3 = DerivationCertificate::build(
        ft("ADGM-FSRA", "Seychelles"),
        "pd".into(),
        "sd".into(),
        vec![],
        BTreeSet::new(),
        Verdict::Compliant,
    )
    .unwrap();
    assert_ne!(c1.certificate_digest, c3.certificate_digest);
}

#[test]
fn hole_filled_record_includes_authority_id() {
    let hole: Hole<FitAndProper, _> = Hole::new(
        Some("fit_check"),
        adgm_fsra(),
        ScopeConstraint::default(),
        Term::Constant(QualIdent::simple("FitAndProperJudgment")),
    );
    let filled = hole
        .fill(
            FitAndProper {
                fit: true,
                basis: "basis".into(),
            },
            witness_for(&adgm_fsra()),
        )
        .unwrap();
    let rec: FilledHoleRecord = filled.to_record(ft("ADGM-FSRA", "ADGM"));
    assert_eq!(rec.authority_id, "ADGM-FSRA");
}

#[test]
fn authority_mismatch_is_exact() {
    // Configure a hole that only the NationalRegulator can fill.
    let hole: Hole<SystemsAndControls, _> = Hole::new(
        Some("sys"),
        national_regulator(),
        ScopeConstraint::default(),
        Term::Constant(QualIdent::simple("SystemsAndControlsAdjustment")),
    );
    // Attempt fill with FSRA witness — must reject.
    let filler = SystemsAndControls {
        overlay_bp: 0,
        finding_summary: "".into(),
    };
    let r = hole.fill(filler, witness_for(&adgm_fsra()));
    match r {
        Err(AuthorityError::SignerMismatch { expected, got }) => {
            assert_eq!(expected, "pk:national");
            assert_eq!(got, "pk:adgm-fsra");
        }
        _ => panic!("expected SignerMismatch"),
    }
}

// ---------------------------------------------------------------------------
// Negative tests / invariant enforcement
// ---------------------------------------------------------------------------

#[test]
fn cannot_build_compliant_with_unfilled_frontier() {
    let mut frontier = BTreeSet::new();
    frontier.insert(HoleId("stuck".into()));
    let r = DerivationCertificate::build(
        ft("ADGM-FSRA", "ADGM"),
        "pd".into(),
        "sd".into(),
        vec![],
        frontier,
        Verdict::Compliant,
    );
    assert!(r.is_err());
}

#[test]
fn cannot_build_pending_with_empty_frontier() {
    let r = DerivationCertificate::build(
        ft("ADGM-FSRA", "ADGM"),
        "pd".into(),
        "sd".into(),
        vec![],
        BTreeSet::new(),
        Verdict::Pending,
    );
    assert!(r.is_err());
}

#[test]
fn mechanical_bit_tracks_frontier_size() {
    for n in 0..5 {
        let frontier: BTreeSet<HoleId> =
            (0..n).map(|i| HoleId(format!("h{}", i))).collect();
        let verdict = if n == 0 {
            Verdict::Compliant
        } else {
            Verdict::Pending
        };
        let cert = DerivationCertificate::build(
            ft("X", "X"),
            "pd".into(),
            "sd".into(),
            vec![],
            frontier,
            verdict,
        )
        .unwrap();
        assert_eq!(cert.mechanical_check, n == 0);
    }
}

// Summary preservation — property-ish tests on many obligation sets.
#[test]
fn obligation_preservation_holds_across_sizes() {
    let cert = DerivationCertificate::build(
        ft("X", "X"),
        "pd".into(),
        "sd".into(),
        vec![],
        BTreeSet::new(),
        Verdict::Compliant,
    )
    .unwrap();
    for n in 0..10 {
        let obligations: Vec<String> = (0..n).map(|i| format!("O{}", i)).collect();
        let summary = compile_summary(&cert, obligations.clone(), &[]);
        assert!(check_obligation_preservation(&summary, &obligations));
    }
}

#[test]
fn verdict_preservation_holds_for_all_verdicts() {
    for (v, frontier_len) in [
        (Verdict::Compliant, 0),
        (Verdict::NonCompliant, 0),
        (Verdict::NotApplicable, 0),
        (Verdict::Indeterminate, 0),
        (Verdict::Pending, 1),
    ] {
        let frontier: BTreeSet<HoleId> = (0..frontier_len)
            .map(|i| HoleId(format!("h{}", i)))
            .collect();
        let cert = DerivationCertificate::build(
            ft("X", "X"),
            "pd".into(),
            "sd".into(),
            vec![],
            frontier,
            v,
        )
        .unwrap();
        let s = compile_summary(&cert, vec![], &[]);
        assert!(check_verdict_preservation(&s, &cert));
    }
}

#[test]
fn oracle_exclusion_commitment_is_stable_across_invocations() {
    use super::oracle::{UBOOracle, UBOQuery};
    let edges: BTreeSet<(String, String)> = [("a", "b"), ("b", "c")]
        .iter()
        .map(|(x, y)| (x.to_string(), y.to_string()))
        .collect();
    let o = UBOOracle::new("ubo", edges);
    let r1 = o.supply_bounded_horizon(UBOQuery { root: "a".into() }, Horizon(5));
    let r2 = o.supply_bounded_horizon(UBOQuery { root: "a".into() }, Horizon(5));
    assert_eq!(r1.exclusion_commitment, r2.exclusion_commitment);
}

#[test]
fn identity_tribunal_coercion_is_total() {
    use super::monotone::{IdentityCoercion, TribunalCoercion};
    struct T;
    struct J;
    struct V;
    struct Tr;
    let p: Proof<T, J, V, Tr, u32> = Proof::axiom(42);
    let c = IdentityCoercion;
    let r = c.coerce(p);
    assert!(r.is_some());
}

#[test]
fn nobridge_tribunal_coercion_is_total_none() {
    use super::monotone::{NoBridge, TribunalCoercion};
    struct T;
    struct J;
    struct V;
    struct TrA;
    struct TrB;
    let p: Proof<T, J, V, TrA, u32> = Proof::axiom(7);
    let c = NoBridge;
    let r: Option<Proof<T, J, V, TrB, _>> = c.coerce(p);
    assert!(r.is_none());
}
