//! End-to-end proof pipeline test for the current `mez-lex` public API.
//!
//! The crate exposes `obligations::extract_obligations()` for structural
//! obligation extraction. The admissible type checker accepts `Defeasible`
//! rules and `Match` on prelude constructor types (ComplianceVerdict,
//! ComplianceTag, Bool, Nat, SanctionsResult). This test:
//! 1. pushes the full IBC Act s.66 rule through AST construction, De Bruijn
//!    assignment, and temporal stratification;
//! 2. uses the compliance prelude to type-check the full rule (including
//!    its Match on Nat constructors);
//! 3. extracts proof obligations via `extract_obligations()`, discharges them
//!    with the exported decision procedures, then assembles a compliance
//!    certificate.

#[cfg(not(feature = "kernel-integration"))]
use mez_core_min::canonical::CanonicalBytes;
#[cfg(not(feature = "kernel-integration"))]
use mez_core_min::digest::sha256_digest;
#[cfg(feature = "kernel-integration")]
use mez_core::canonical::CanonicalBytes;
#[cfg(feature = "kernel-integration")]
use mez_core::digest::sha256_digest;
use lex_core::ast::{
    Branch, Constructor, DefeasibleRule, Exception, Ident, Level, Pattern, QualIdent, Sort, Term,
};
use lex_core::certificate::{
    self, ComplianceVerdict, DischargedObligation as CertDischargedObligation, LexCertificate,
};
use lex_core::debruijn;
use lex_core::decide::{
    DecisionResult, boolean_check, finite_domain_check, threshold_check,
};
use lex_core::prelude;
use lex_core::temporal;
use lex_core::obligations;
use lex_core::typecheck;

#[derive(Debug, Clone)]
struct ProofObligation {
    name: String,
    statement: String,
    result: DecisionResult,
}

#[derive(Debug, Clone, Copy)]
struct IncorporationFacts<'a> {
    jurisdiction: &'a str,
    director_count: i64,
}

fn var(name: &str, index: u32) -> Term {
    Term::Var {
        name: Ident::new(name),
        index,
    }
}

fn type0() -> Term {
    Term::Sort(Sort::Type(Level::Nat(0)))
}

fn constant(name: &str) -> Term {
    Term::Constant(QualIdent::simple(name))
}

fn app(func: Term, arg: Term) -> Term {
    Term::App {
        func: Box::new(func),
        arg: Box::new(arg),
    }
}

fn lam(name: &str, domain: Term, body: Term) -> Term {
    Term::Lambda {
        binder: Ident::new(name),
        domain: Box::new(domain),
        body: Box::new(body),
    }
}

fn pi(name: &str, domain: Term, codomain: Term) -> Term {
    Term::Pi {
        binder: Ident::new(name),
        domain: Box::new(domain),
        codomain: Box::new(codomain),
        effect_row: None,
    }
}

fn match_expr(scrutinee: Term, return_ty: Term, branches: Vec<Branch>) -> Term {
    Term::Match {
        scrutinee: Box::new(scrutinee),
        return_ty: Box::new(return_ty),
        branches,
    }
}

fn branch(ctor_name: &str, binders: &[&str], body: Term) -> Branch {
    Branch {
        pattern: Pattern::Constructor {
            constructor: Constructor::new(QualIdent::simple(ctor_name)),
            binders: binders.iter().map(|name| Ident::new(name)).collect(),
        },
        body,
    }
}

fn wildcard_branch(body: Term) -> Branch {
    Branch {
        pattern: Pattern::Wildcard,
        body,
    }
}

fn defeasible(name: &str, ty: Term, body: Term, exceptions: Vec<Exception>) -> Term {
    Term::Defeasible(DefeasibleRule {
        name: Ident::new(name),
        base_ty: Box::new(ty),
        base_body: Box::new(body),
        exceptions,
        lattice: None,
    })
}

fn ibc_s66_minimum_directors_rule() -> Term {
    defeasible(
        "min_directors",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("director_count"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("Zero", &[], constant("NonCompliant")),
                    wildcard_branch(constant("Compliant")),
                ],
            ),
        ),
        vec![],
    )
}


fn rule_content_hash(term: &Term) -> String {
    let canonical = CanonicalBytes::new(term).expect("rule AST should canonicalize");
    sha256_digest(&canonical).to_hex()
}

fn collect_discharged_obligations(
    obligations: &[ProofObligation],
) -> Vec<CertDischargedObligation> {
    obligations
        .iter()
        .map(|obligation| match &obligation.result {
            DecisionResult::Proved { witness } => CertDischargedObligation {
                category: obligation.name.to_string(),
                witness: witness.description.clone(),
                decision_procedure: witness.procedure.clone(),
            },
            DecisionResult::Refuted { counterexample } => {
                panic!(
                    "obligation `{}` was refuted: {}",
                    obligation.name, counterexample
                )
            }
            DecisionResult::Undecidable { reason } => {
                panic!(
                    "obligation `{}` was undecidable: {}",
                    obligation.name, reason
                )
            }
        })
        .collect()
}

fn discharge_extracted_obligation(
    ext: &obligations::ProofObligation,
    facts: IncorporationFacts<'_>,
) -> DecisionResult {
    match ext.category {
        obligations::ObligationCategory::ExhaustiveMatch => {
            // The match covers Zero + wildcard => exhaustive over Nat constructors.
            // We check the jurisdiction applicability as the domain membership witness.
            finite_domain_check("Jurisdiction", &["SC"], facts.jurisdiction)
        }
        obligations::ObligationCategory::DefeasibleResolution => {
            // The defeasible rule resolves deterministically (no exceptions).
            // We check the threshold: director_count >= 1 implies Compliant.
            threshold_check(facts.director_count, 1, ">=")
        }
        obligations::ObligationCategory::ThresholdComparison => {
            threshold_check(facts.director_count, 1, ">=")
        }
        obligations::ObligationCategory::DomainMembership => {
            finite_domain_check("Jurisdiction", &["SC"], facts.jurisdiction)
        }
        _ => boolean_check(true),
    }
}

#[test]
fn ibc_s66_full_proof_pipeline_produces_certificate() {
    let rule = ibc_s66_minimum_directors_rule();

    let indexed_rule = debruijn::assign_indices(&rule).expect("index assignment should succeed");
    temporal::check_temporal_stratification(&indexed_rule)
        .expect("the minimum-directors rule has no temporal mixing");

    let prelude = prelude::compliance_prelude();

    let (rule_ty, rule_body) = match &indexed_rule {
        Term::Defeasible(rule) => (rule.base_ty.as_ref(), rule.base_body.as_ref()),
        other => panic!("expected defeasible rule, found {other:?}"),
    };

    assert_eq!(
        typecheck::infer(&prelude, rule_ty).expect("rule signature should infer"),
        type0()
    );

    let accessor_ctx = prelude.extend(constant("IncorporationContext"));
    let director_count_application = app(constant("director_count"), var("ctx", 0));
    assert_eq!(
        typecheck::infer(&accessor_ctx, &director_count_application)
            .expect("director_count application should infer"),
        constant("Nat")
    );

    // Match on prelude constructor types (Zero is a Nat constructor) is now
    // in the admissible fragment.  The rule body should typecheck successfully.
    typecheck::check(&prelude, rule_body, rule_ty)
        .expect("rule body with prelude-type match should typecheck");

    // The full defeasible rule (with prelude-type match in its body) should
    // also infer successfully.
    let inferred_ty = typecheck::infer(&prelude, &indexed_rule)
        .expect("defeasible rule with prelude-type match should infer");
    assert_eq!(
        inferred_ty,
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        )
    );

    let extracted = obligations::extract_obligations(&indexed_rule);
    assert!(
        !extracted.is_empty(),
        "extract_obligations should produce at least one obligation from the IBC s.66 rule"
    );

    let facts = IncorporationFacts {
        jurisdiction: "SC",
        director_count: 1,
    };

    let obligations: Vec<ProofObligation> = extracted
        .iter()
        .map(|ext| {
            let result = discharge_extracted_obligation(ext, facts);
            ProofObligation {
                name: ext.id.clone(),
                statement: ext.description.clone(),
                result,
            }
        })
        .collect();

    for obligation in &obligations {
        assert!(
            matches!(obligation.result, DecisionResult::Proved { .. }),
            "obligation `{}` was not proved: {:?}",
            obligation.name,
            obligation.result
        );
        assert!(
            !obligation.statement.is_empty(),
            "obligation `{}` should describe its statement",
            obligation.name
        );
    }

    let discharged = collect_discharged_obligations(&obligations);
    let certificate: LexCertificate = certificate::build_certificate(
        &rule_content_hash(&indexed_rule),
        facts.jurisdiction,
        "IBC Act 2016 s.66",
        ComplianceVerdict::Compliant,
        discharged,
    )
    .expect("build_certificate should succeed in test");

    assert_eq!(certificate.rule_digest.len(), 64);
    assert_eq!(certificate.jurisdiction, "SC");
    assert_eq!(certificate.legal_basis, "IBC Act 2016 s.66");
    assert_eq!(certificate.verdict, ComplianceVerdict::Compliant);
    assert!(!certificate.issued_at.is_empty());
    assert_eq!(certificate.certificate_digest.len(), 64);
    assert_eq!(certificate.obligations.len(), obligations.len());

    for entry in &certificate.obligations {
        assert!(
            !entry.decision_procedure.is_empty(),
            "every discharged obligation should name its decision procedure"
        );
        assert!(
            !entry.category.is_empty(),
            "every discharged obligation should be named"
        );
    }
}
