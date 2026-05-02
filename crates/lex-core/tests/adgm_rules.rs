//! Integration tests: ADGM Companies Regulations 2020 rules through the Lex pipeline.
//!
//! Each test constructs an ADGM compliance rule as a Core Lex AST term and
//! verifies it through:
//! 1. De Bruijn index assignment (well-scoped)
//! 2. Temporal stratification (no Time0/Time1 mixing)
//! 3. Structural survival through the existing Lex pipeline

use lex_core::ast::*;
use lex_core::debruijn;
use lex_core::temporal;

/// Helper: create a simple variable term.
fn var(name: &str, index: u32) -> Term {
    Term::Var {
        name: Ident::new(name),
        index,
    }
}

/// Helper: create a constant reference.
fn constant(name: &str) -> Term {
    Term::Constant(QualIdent::simple(name))
}

/// Helper: create an application.
fn app(func: Term, arg: Term) -> Term {
    Term::App {
        func: Box::new(func),
        arg: Box::new(arg),
    }
}

/// Helper: create a lambda.
fn lam(name: &str, domain: Term, body: Term) -> Term {
    Term::Lambda {
        binder: Ident::new(name),
        domain: Box::new(domain),
        body: Box::new(body),
    }
}

/// Helper: create a Pi type.
fn pi(name: &str, domain: Term, codomain: Term) -> Term {
    Term::Pi {
        binder: Ident::new(name),
        domain: Box::new(domain),
        codomain: Box::new(codomain),
        effect_row: None,
    }
}

/// Helper: create a match expression.
fn match_expr(scrutinee: Term, return_ty: Term, branches: Vec<Branch>) -> Term {
    Term::Match {
        scrutinee: Box::new(scrutinee),
        return_ty: Box::new(return_ty),
        branches,
    }
}

/// Helper: create a constructor pattern branch.
fn branch(ctor_name: &str, binders: &[&str], body: Term) -> Branch {
    Branch {
        pattern: Pattern::Constructor {
            constructor: Constructor::new(QualIdent::simple(ctor_name)),
            binders: binders.iter().map(|s| Ident::new(s)).collect(),
        },
        body,
    }
}

/// Helper: wildcard branch.
fn wildcard_branch(body: Term) -> Branch {
    Branch {
        pattern: Pattern::Wildcard,
        body,
    }
}

/// Helper: create a defeasible rule.
fn defeasible(name: &str, ty: Term, body: Term, exceptions: Vec<Exception>) -> Term {
    Term::Defeasible(DefeasibleRule {
        name: Ident::new(name),
        base_ty: Box::new(ty),
        base_body: Box::new(body),
        exceptions,
        lattice: None,
    })
}

// ---------------------------------------------------------------------------
// Rule 1 — Minimum directors
// ---------------------------------------------------------------------------

#[test]
fn adgm_rule_1_minimum_directors() {
    let rule = defeasible(
        "minimum_directors",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("natural_person_director_count"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("Zero", &[], constant("NonCompliant")),
                    wildcard_branch(constant("Compliant")),
                ],
            ),
        ),
        vec![],
    );

    let indexed = debruijn::assign_indices(&rule).expect("index assignment should succeed");
    temporal::check_temporal_stratification(&indexed).expect("no temporal terms - should pass");
    let _ = &indexed;
}

// ---------------------------------------------------------------------------
// Rule 2 — Registered office in ADGM
// ---------------------------------------------------------------------------

#[test]
fn adgm_rule_2_registered_office() {
    let rule = defeasible(
        "registered_office_adgm",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("registered_office_location"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("ADGM", &[], constant("Compliant")),
                    wildcard_branch(constant("NonCompliant")),
                ],
            ),
        ),
        vec![],
    );

    let indexed = debruijn::assign_indices(&rule).expect("index assignment should succeed");
    temporal::check_temporal_stratification(&indexed).expect("should pass");
    let _ = &indexed;
}

// ---------------------------------------------------------------------------
// Rule 3 — Company secretary for public companies
// ---------------------------------------------------------------------------

#[test]
fn adgm_rule_3_public_company_secretary() {
    let rule = defeasible(
        "public_company_secretary",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("company_class"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch(
                        "PublicCompany",
                        &[],
                        match_expr(
                            app(constant("company_secretary"), var("ctx", 0)),
                            constant("ComplianceVerdict"),
                            vec![
                                branch("None", &[], constant("NonCompliant")),
                                branch("Some", &["secretary"], constant("Compliant")),
                            ],
                        ),
                    ),
                    wildcard_branch(constant("Compliant")),
                ],
            ),
        ),
        vec![],
    );

    let indexed = debruijn::assign_indices(&rule).expect("index assignment should succeed");
    temporal::check_temporal_stratification(&indexed).expect("should pass");
    let _ = &indexed;
}

// ---------------------------------------------------------------------------
// Rule 4 — No minimum capital
// ---------------------------------------------------------------------------

#[test]
fn adgm_rule_4_no_minimum_capital() {
    let rule = lam(
        "ctx",
        constant("IncorporationContext"),
        constant("Compliant"),
    );

    let indexed = debruijn::assign_indices(&rule).expect("index assignment should succeed");
    temporal::check_temporal_stratification(&indexed).expect("should pass");
    let _ = &indexed;
}

// ---------------------------------------------------------------------------
// Rule 5 — Public company authorized capital minimum
// ---------------------------------------------------------------------------

#[test]
fn adgm_rule_5_public_company_authorized_capital_minimum() {
    let rule = defeasible(
        "public_company_authorized_capital_minimum",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("company_class"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch(
                        "PublicCompany",
                        &[],
                        match_expr(
                            app(
                                constant("public_company_authorized_capital_satisfied"),
                                var("ctx", 0),
                            ),
                            constant("ComplianceVerdict"),
                            vec![
                                branch("True", &[], constant("Compliant")),
                                branch("False", &[], constant("NonCompliant")),
                            ],
                        ),
                    ),
                    wildcard_branch(constant("Compliant")),
                ],
            ),
        ),
        vec![],
    );

    let indexed = debruijn::assign_indices(&rule).expect("index assignment should succeed");
    temporal::check_temporal_stratification(&indexed).expect("should pass");
    let _ = &indexed;
}

// ---------------------------------------------------------------------------
// Rule 6 — Confirmation statement filing
// ---------------------------------------------------------------------------

#[test]
fn adgm_rule_6_confirmation_statement_filing() {
    let rule = defeasible(
        "confirmation_statement_filing",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("confirmation_statement_status"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("WithinOneMonthOfAnniversary", &[], constant("Compliant")),
                    branch("DueSoon", &[], constant("Pending")),
                    branch("Overdue", &[], constant("NonCompliant")),
                ],
            ),
        ),
        vec![],
    );

    let indexed = debruijn::assign_indices(&rule).expect("index assignment should succeed");
    temporal::check_temporal_stratification(&indexed).expect("should pass");
    let _ = &indexed;
}

// ---------------------------------------------------------------------------
// Rule 7 — KYC/AML compliance
// ---------------------------------------------------------------------------

#[test]
fn adgm_rule_7_kyc_aml_compliance() {
    let rule = defeasible(
        "kyc_aml_compliance",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("kyc_aml_status"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("AmlCompliant", &[], constant("Compliant")),
                    branch("AmlRemediationRequired", &[], constant("Pending")),
                    branch("AmlFailed", &[], constant("NonCompliant")),
                ],
            ),
        ),
        vec![],
    );

    let indexed = debruijn::assign_indices(&rule).expect("index assignment should succeed");
    temporal::check_temporal_stratification(&indexed).expect("should pass");
    let _ = &indexed;
}

// ---------------------------------------------------------------------------
// Rule 8 — Statutory sanctions screening with effectful lookup
// ---------------------------------------------------------------------------

#[test]
fn adgm_rule_8_statutory_sanctions_screening() {
    let rule = Term::Lambda {
        binder: Ident::new("ctx"),
        domain: Box::new(constant("IncorporationContext")),
        body: Box::new(Term::Let {
            binder: Ident::new("result"),
            ty: Box::new(constant("SanctionsResult")),
            val: Box::new(app(
                constant("adgm_statutory_sanctions_screen"),
                var("ctx", 0),
            )),
            body: Box::new(match_expr(
                var("result", 0),
                constant("ComplianceVerdict"),
                vec![
                    branch("Clear", &[], constant("Compliant")),
                    wildcard_branch(constant("NonCompliant")),
                ],
            )),
        }),
    };

    let indexed = debruijn::assign_indices(&rule).expect("should succeed");
    temporal::check_temporal_stratification(&indexed).expect("should pass - no temporal terms");
    let _ = &indexed;
}

// ---------------------------------------------------------------------------
// Rule 9 — Beneficial ownership register and 15-day change notice
// ---------------------------------------------------------------------------

#[test]
fn adgm_rule_9_beneficial_ownership_register_and_change_notice() {
    let rule = defeasible(
        "beneficial_ownership_register_and_change_notice",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(
                    constant("beneficial_ownership_register_status"),
                    var("ctx", 0),
                ),
                constant("ComplianceVerdict"),
                vec![
                    branch("RegisterCurrent", &[], constant("Compliant")),
                    branch("ChangePendingWithin15Days", &[], constant("Pending")),
                    branch("ChangeOverdue", &[], constant("NonCompliant")),
                    branch("RegisterMissing", &[], constant("NonCompliant")),
                ],
            ),
        ),
        vec![],
    );

    let indexed = debruijn::assign_indices(&rule).expect("should succeed");
    temporal::check_temporal_stratification(&indexed).expect("should pass");
    let _ = &indexed;
}

// ---------------------------------------------------------------------------
// Rule 10 — Data protection
// ---------------------------------------------------------------------------

#[test]
fn adgm_rule_10_data_protection() {
    let rule = defeasible(
        "data_protection",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("data_protection_status"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("DpCompliant", &[], constant("Compliant")),
                    branch("DpRemediationPending", &[], constant("Pending")),
                    branch("DpNonCompliant", &[], constant("NonCompliant")),
                ],
            ),
        ),
        vec![],
    );

    let indexed = debruijn::assign_indices(&rule).expect("should succeed");
    temporal::check_temporal_stratification(&indexed).expect("should pass");
    let _ = &indexed;
}

// ---------------------------------------------------------------------------
// Rule 11 — Financial services permission with exemption
// ---------------------------------------------------------------------------

#[test]
fn adgm_rule_11_financial_services_permission() {
    let rule = defeasible(
        "financial_services_permission",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("conducts_regulated_activity"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("False", &[], constant("Compliant")),
                    branch(
                        "True",
                        &[],
                        match_expr(
                            app(constant("fsra_permission_status"), var("ctx", 0)),
                            constant("ComplianceVerdict"),
                            vec![
                                branch("Granted", &[], constant("Compliant")),
                                branch("Applied", &[], constant("Pending")),
                                wildcard_branch(constant("NonCompliant")),
                            ],
                        ),
                    ),
                ],
            ),
        ),
        vec![Exception {
            guard: Box::new(lam(
                "ctx",
                constant("IncorporationContext"),
                app(constant("regulated_activity_exemption"), var("ctx", 0)),
            )),
            body: Box::new(lam(
                "ctx",
                constant("IncorporationContext"),
                constant("Compliant"),
            )),
            priority: Some(1),
            authority: Some(AuthorityRef::Named(QualIdent::simple("fsra.adgm"))),
        }],
    );

    let indexed = debruijn::assign_indices(&rule).expect("should succeed");
    temporal::check_temporal_stratification(&indexed).expect("should pass");
    let _ = &indexed;
}

// ---------------------------------------------------------------------------
// Summary: pipeline verification for representative rules
// ---------------------------------------------------------------------------

#[test]
fn all_adgm_rules_serde_roundtrip() {
    let rules: Vec<Term> = vec![
        defeasible(
            "minimum_directors",
            pi(
                "ctx",
                constant("IncorporationContext"),
                constant("ComplianceVerdict"),
            ),
            lam(
                "ctx",
                constant("IncorporationContext"),
                match_expr(
                    app(constant("natural_person_director_count"), var("ctx", 0)),
                    constant("ComplianceVerdict"),
                    vec![
                        branch("Zero", &[], constant("NonCompliant")),
                        wildcard_branch(constant("Compliant")),
                    ],
                ),
            ),
            vec![],
        ),
        Term::Lambda {
            binder: Ident::new("ctx"),
            domain: Box::new(constant("IncorporationContext")),
            body: Box::new(Term::Let {
                binder: Ident::new("result"),
                ty: Box::new(constant("SanctionsResult")),
                val: Box::new(app(
                    constant("adgm_statutory_sanctions_screen"),
                    var("ctx", 0),
                )),
                body: Box::new(match_expr(
                    var("result", 0),
                    constant("ComplianceVerdict"),
                    vec![
                        branch("Clear", &[], constant("Compliant")),
                        wildcard_branch(constant("NonCompliant")),
                    ],
                )),
            }),
        },
        defeasible(
            "financial_services_permission",
            pi(
                "ctx",
                constant("IncorporationContext"),
                constant("ComplianceVerdict"),
            ),
            lam(
                "ctx",
                constant("IncorporationContext"),
                match_expr(
                    app(constant("conducts_regulated_activity"), var("ctx", 0)),
                    constant("ComplianceVerdict"),
                    vec![
                        branch("False", &[], constant("Compliant")),
                        branch(
                            "True",
                            &[],
                            match_expr(
                                app(constant("fsra_permission_status"), var("ctx", 0)),
                                constant("ComplianceVerdict"),
                                vec![
                                    branch("Granted", &[], constant("Compliant")),
                                    branch("Applied", &[], constant("Pending")),
                                    wildcard_branch(constant("NonCompliant")),
                                ],
                            ),
                        ),
                    ],
                ),
            ),
            vec![Exception {
                guard: Box::new(lam(
                    "ctx",
                    constant("IncorporationContext"),
                    app(constant("regulated_activity_exemption"), var("ctx", 0)),
                )),
                body: Box::new(lam(
                    "ctx",
                    constant("IncorporationContext"),
                    constant("Compliant"),
                )),
                priority: Some(1),
                authority: Some(AuthorityRef::Named(QualIdent::simple("fsra.adgm"))),
            }],
        ),
    ];

    for (i, rule) in rules.iter().enumerate() {
        let json = serde_json::to_string(rule)
            .unwrap_or_else(|e| panic!("rule {i} failed to serialize: {e}"));
        let roundtripped: Term = serde_json::from_str(&json)
            .unwrap_or_else(|e| panic!("rule {i} failed to deserialize: {e}"));
        assert_eq!(rule, &roundtripped, "rule {i} failed serde roundtrip");
    }
}
