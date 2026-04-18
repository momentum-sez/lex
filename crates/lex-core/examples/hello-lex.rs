//! hello-lex — the smallest self-contained Lex program that exercises every
//! non-trivial primitive of the calculus.
//!
//! Run from the workspace root with:
//!
//! ```bash
//! cargo run --example hello-lex -p lex-core
//! ```
//!
//! The program walks the full Lex proof pipeline on a real statute
//! (Seychelles International Business Companies Act 2016, section 66 —
//! "A company shall have at least one director who is a natural person"),
//! then illustrates the typed discretion hole — the primitive that makes
//! Lex distinct from every other rule engine.
//!
//! Output layout:
//!   1. The rule, as an AST constructed in Rust.
//!   2. De Bruijn indexing and temporal-stratification check.
//!   3. Type inference against the compliance prelude.
//!   4. Proof-obligation extraction.
//!   5. Obligation discharge against concrete facts.
//!   6. Compliance-certificate assembly.
//!   7. A typed discretion hole — the frontier between machine derivation
//!      and human judgment — and the obligations it emits.

use lex_core::ast::{
    AuthorityRef, Branch, Constructor, DefeasibleRule, Hole, Ident, Level, Pattern, QualIdent,
    ScopeConstraint, ScopeField, Sort, Term, TimeLiteral, TimeTerm,
};
use lex_core::certificate::{
    self, ComplianceVerdict, DischargedObligation as CertDischargedObligation,
};
use lex_core::debruijn;
use lex_core::decide::{self, DecisionResult};
use lex_core::obligations::{self, ObligationCategory, ProofObligation};
use lex_core::prelude;
use lex_core::temporal;
use lex_core::typecheck;

use mez_core::canonical::CanonicalBytes;
use mez_core::digest::sha256_digest;

// ── AST helpers ────────────────────────────────────────────────────────────

fn var(name: &str, index: u32) -> Term {
    Term::Var {
        name: Ident::new(name),
        index,
    }
}

#[allow(dead_code)]
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

fn branch_ctor(name: &str, body: Term) -> Branch {
    Branch {
        pattern: Pattern::Constructor {
            constructor: Constructor::new(QualIdent::simple(name)),
            binders: Vec::new(),
        },
        body,
    }
}

fn branch_wildcard(body: Term) -> Branch {
    Branch {
        pattern: Pattern::Wildcard,
        body,
    }
}

// ── The rule: IBC Act 2016 s.66 (minimum directors) ────────────────────────

/// Construct the defeasible Lex rule for IBC Act 2016 s.66.
///
/// Surface form:
///
/// ```text
/// defeasible min_directors : IncorporationContext -> ComplianceVerdict :=
///   lambda (ctx : IncorporationContext).
///     match director_count(ctx) return ComplianceVerdict with
///     | Zero => NonCompliant
///     | _    => Compliant
///   priority 0
/// ```
fn ibc_s66_rule() -> Term {
    Term::Defeasible(DefeasibleRule {
        name: Ident::new("min_directors"),
        base_ty: Box::new(pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        )),
        base_body: Box::new(lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("director_count"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch_ctor("Zero", constant("NonCompliant")),
                    branch_wildcard(constant("Compliant")),
                ],
            ),
        )),
        exceptions: Vec::new(),
        lattice: None,
    })
}

// ── Facts and obligation discharge ─────────────────────────────────────────

#[derive(Debug, Clone, Copy)]
struct IncorporationFacts<'a> {
    jurisdiction: &'a str,
    director_count: i64,
}

fn discharge(obligation: &ProofObligation, facts: IncorporationFacts<'_>) -> DecisionResult {
    match obligation.category {
        ObligationCategory::ExhaustiveMatch => {
            decide::finite_domain_check("Jurisdiction", &["SC"], facts.jurisdiction)
        }
        ObligationCategory::DefeasibleResolution
        | ObligationCategory::ThresholdComparison => {
            decide::threshold_check(facts.director_count, 1, ">=")
        }
        ObligationCategory::DomainMembership => {
            decide::finite_domain_check("Jurisdiction", &["SC"], facts.jurisdiction)
        }
        _ => decide::boolean_check(true),
    }
}

fn obligation_to_discharged(
    obligation: &ProofObligation,
    result: &DecisionResult,
) -> CertDischargedObligation {
    match result {
        DecisionResult::Proved { witness } => CertDischargedObligation {
            category: format!("{:?}", obligation.category),
            witness: witness.description.clone(),
            decision_procedure: witness.procedure.clone(),
        },
        DecisionResult::Refuted { counterexample } => CertDischargedObligation {
            category: format!("{:?}", obligation.category),
            witness: format!("refuted: {counterexample}"),
            decision_procedure: obligation.suggested_procedure.clone(),
        },
        DecisionResult::Undecidable { reason } => CertDischargedObligation {
            category: format!("{:?}", obligation.category),
            witness: format!("undecidable: {reason}"),
            decision_procedure: obligation.suggested_procedure.clone(),
        },
    }
}

// ── Typed discretion hole: the Lex primitive ───────────────────────────────

/// A typed discretion hole marking a "fit and proper" judgment.
///
/// The hole has a type (`ComplianceVerdict`), an authority entitled to fill
/// it (`authority.fsa.seychelles`), and a scope (Seychelles, March 2026).
/// It is part of the Lex calculus, not an after-the-fact annotation: the
/// obligation extractor emits `DomainMembership` and `TemporalOrdering`
/// proof obligations directly from the hole's scope.
fn fit_and_proper_hole() -> Term {
    Term::Hole(Hole {
        name: Some(Ident::new("fit_and_proper_director")),
        ty: Box::new(constant("ComplianceVerdict")),
        authority: AuthorityRef::Named(QualIdent::new(
            ["authority", "fsa", "seychelles"].iter().copied(),
        )),
        scope: Some(ScopeConstraint {
            fields: vec![
                ScopeField::Jurisdiction(QualIdent::simple("SC")),
                ScopeField::TimeWindow {
                    from: TimeTerm::Literal(TimeLiteral {
                        iso8601: "2026-03-01T00:00:00Z".to_string(),
                    }),
                    to: TimeTerm::Literal(TimeLiteral {
                        iso8601: "2026-03-31T23:59:59Z".to_string(),
                    }),
                },
            ],
        }),
    })
}

// ── Driver ─────────────────────────────────────────────────────────────────

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("hello-lex");
    println!("========");
    println!();
    println!("Rule: Seychelles IBC Act 2016 s.66");
    println!("  \"A company shall have at least one director who is a natural person.\"");
    println!();

    // 1. Construct the AST.
    let rule = ibc_s66_rule();
    println!("[1] AST constructed — Term::Defeasible(min_directors).");

    // 2. Assign De Bruijn indices, then run the temporal-stratification check.
    let indexed = debruijn::assign_indices(&rule)?;
    temporal::check_temporal_stratification(&indexed)?;
    println!("[2] De Bruijn indices assigned; temporal stratification verified.");

    // 3. Type-check the rule against the compliance prelude.
    let ctx = prelude::compliance_prelude();
    let inferred = typecheck::infer(&ctx, &indexed)?;
    let expected = pi(
        "ctx",
        constant("IncorporationContext"),
        constant("ComplianceVerdict"),
    );
    assert_eq!(inferred, expected);
    println!("[3] Type-checked: min_directors : IncorporationContext -> ComplianceVerdict.");

    // 4. Extract proof obligations from the AST.
    let extracted = obligations::extract_obligations(&indexed);
    println!(
        "[4] Extracted {} proof obligation(s) from the rule.",
        extracted.len()
    );
    for (i, o) in extracted.iter().enumerate() {
        println!("      {}: [{:?}] {}", i + 1, o.category, o.id);
    }

    // 5. Discharge each obligation against concrete facts.
    let facts = IncorporationFacts {
        jurisdiction: "SC",
        director_count: 1,
    };
    println!();
    println!(
        "[5] Facts: jurisdiction = {}, director_count = {}.",
        facts.jurisdiction, facts.director_count
    );

    let mut discharged = Vec::with_capacity(extracted.len());
    for o in &extracted {
        let result = discharge(o, facts);
        match &result {
            DecisionResult::Proved { witness } => {
                println!(
                    "      [{:?}] proved — procedure: {}",
                    o.category, witness.procedure
                );
            }
            DecisionResult::Refuted { counterexample } => {
                println!("      [{:?}] refuted: {}", o.category, counterexample);
            }
            DecisionResult::Undecidable { reason } => {
                println!("      [{:?}] undecidable: {}", o.category, reason);
            }
        }
        discharged.push(obligation_to_discharged(o, &result));
    }

    // 6. Build the compliance certificate.
    let canonical = CanonicalBytes::new(&indexed)?;
    let rule_digest = sha256_digest(&canonical).to_hex();
    let cert = certificate::build_certificate(
        &rule_digest,
        facts.jurisdiction,
        "IBC Act 2016 s.66",
        ComplianceVerdict::Compliant,
        discharged,
    )?;
    println!();
    println!("[6] Certificate issued.");
    println!("      verdict           : {}", cert.verdict);
    println!("      jurisdiction      : {}", cert.jurisdiction);
    println!("      legal basis       : {}", cert.legal_basis);
    println!("      rule digest       : {}", cert.rule_digest);
    println!("      certificate digest: {}", cert.certificate_digest);
    println!("      issued at         : {}", cert.issued_at);

    // 7. The typed discretion hole — the Lex primitive.
    println!();
    println!("[7] Typed discretion hole.");
    println!(
        "      The \"fit and proper person\" judgment is not computable. Lex\n\
         \x20     marks it with a hole — a typed value slot that names the\n\
         \x20     authority authorized to fill it and the scope in which the\n\
         \x20     judgment applies."
    );
    let hole = fit_and_proper_hole();
    let hole_obligations = obligations::extract_obligations(&hole);
    println!(
        "      Hole: ? : ComplianceVerdict @ authority.fsa.seychelles (SC, 2026-03)."
    );
    println!(
        "      Extractor produced {} obligation(s) from the hole's scope:",
        hole_obligations.len()
    );
    for o in &hole_obligations {
        println!("        [{:?}] {}", o.category, o.description);
    }

    println!();
    println!("Done. Lex admitted the machine-computable part, flagged the");
    println!("human-judgment part, and emitted a content-addressed");
    println!("certificate that can be signed and submitted to a kernel.");
    Ok(())
}
