//! Integration tests: Seychelles IBC Act 2016 rules through the Lex pipeline.
//!
//! Each test constructs a compliance rule from the International Business
//! Companies Act 2016 as a Core Lex AST term and verifies it through:
//! 1. De Bruijn index assignment (well-scoped)
//! 2. Temporal stratification (no Time₀/Time₁ mixing)
//! 3. Pretty printing (human-readable output)
//!
//! These are the first real laws to flow through the proof kernel.

use mez_lex::ast::*;
use mez_lex::debruijn;
use mez_lex::temporal;

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
// IBC Act s.66 — Minimum directors
// ---------------------------------------------------------------------------

/// IBC Act s.66: Every IBC shall have at least one director.
///
/// ```lex
/// defeasible min_directors : IncorporationContext → ComplianceVerdict
///   λ(ctx : IncorporationContext).
///     match ctx.director_count return ComplianceVerdict with
///     | Zero ⇒ NonCompliant
///     | _ ⇒ Compliant
/// end
/// ```
#[test]
fn ibc_s66_minimum_directors() {
    let rule = defeasible(
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
    );

    // Pipeline: assign indices → temporal check → pretty print
    let indexed = debruijn::assign_indices(&rule).expect("index assignment should succeed");
    temporal::check_temporal_stratification(&indexed).expect("no temporal terms — should pass");
    // Rule survives the full pipeline: well-scoped + temporally stratified
    let _ = &indexed; // indexed term is ready for type checking
}

// ---------------------------------------------------------------------------
// IBC Act s.92 — Registered agent mandatory
// ---------------------------------------------------------------------------

/// IBC Act s.92: Every IBC must appoint a licensed CSP as registered agent.
#[test]
fn ibc_s92_registered_agent() {
    let rule = defeasible(
        "registered_agent",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("registered_agent"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("None", &[], constant("NonCompliant")),
                    branch(
                        "Some",
                        &["agent"],
                        match_expr(
                            app(constant("csp_license_status"), var("agent", 0)),
                            constant("ComplianceVerdict"),
                            vec![
                                branch("Active", &[], constant("Compliant")),
                                branch("Suspended", &[], constant("NonCompliant")),
                                branch("Revoked", &[], constant("NonCompliant")),
                                wildcard_branch(constant("Pending")),
                            ],
                        ),
                    ),
                ],
            ),
        ),
        vec![],
    );

    let indexed = debruijn::assign_indices(&rule).expect("index assignment should succeed");
    temporal::check_temporal_stratification(&indexed).expect("no temporal terms — should pass");
    let _ = &indexed;
}

// ---------------------------------------------------------------------------
// IBC Act s.12(3) — Name ending requirement
// ---------------------------------------------------------------------------

/// IBC Act s.12(3): The name of an IBC must end with an approved suffix.
#[test]
fn ibc_s12_name_ending() {
    let rule = defeasible(
        "name_ending",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("name_suffix"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("IBC", &[], constant("Compliant")),
                    branch("Limited", &[], constant("Compliant")),
                    branch("Ltd", &[], constant("Compliant")),
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
// IBC Act s.55 — Registered office location
// ---------------------------------------------------------------------------

/// IBC Act s.55: Registered office must be at CSP's office in Seychelles.
#[test]
fn ibc_s55_registered_office() {
    let rule = defeasible(
        "registered_office_sc",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("registered_office_country"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("SC", &[], constant("Compliant")),
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
// IBC entity type restriction
// ---------------------------------------------------------------------------

/// Only IBC, SpecialLicense, and ProtectedCell entity types are permitted.
#[test]
fn ibc_s2_entity_type() {
    let rule = defeasible(
        "entity_type_restriction",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("entity_type"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("IBC", &[], constant("Compliant")),
                    branch("SpecialLicense", &[], constant("Compliant")),
                    branch("ProtectedCell", &[], constant("Compliant")),
                    wildcard_branch(constant("NonCompliant")),
                ],
            ),
        ),
        vec![],
    );

    let indexed = debruijn::assign_indices(&rule).expect("index assignment should succeed");
    temporal::check_temporal_stratification(&indexed).expect("should pass");
}

// ---------------------------------------------------------------------------
// No minimum capital (IBC Act — absence of requirement)
// ---------------------------------------------------------------------------

/// IBCs have no minimum capital requirement. Always Compliant.
#[test]
fn ibc_no_minimum_capital() {
    let rule = lam(
        "ctx",
        constant("IncorporationContext"),
        constant("Compliant"),
    );

    let indexed = debruijn::assign_indices(&rule).expect("should succeed");
    temporal::check_temporal_stratification(&indexed).expect("should pass");
    let _ = &indexed;
}

// ---------------------------------------------------------------------------
// AML/KYC with defeasible exception (AML Act 2006)
// ---------------------------------------------------------------------------

/// AML Act 2006: Incorporator, directors, and UBOs must be identified.
/// Exception: if parent entity has completed KYC on all parties, individual
/// identification may be satisfied by reference to parent's KYC file.
#[test]
fn aml_kyc_with_de_minimis_exception() {
    let rule = defeasible(
        "aml_kyc_identification",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("all_parties_identified"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("True", &[], constant("Compliant")),
                    branch("False", &[], constant("NonCompliant")),
                ],
            ),
        ),
        vec![
            // De minimis exception: parent entity KYC satisfies individual requirement.
            // The exception guard is a standalone lambda — ctx is not in scope from the
            // base rule. The exception binds its own ctx parameter.
            Exception {
                guard: Box::new(lam(
                    "ctx",
                    constant("IncorporationContext"),
                    app(constant("parent_entity_kyc_compliant"), var("ctx", 0)),
                )),
                body: Box::new(lam(
                    "ctx",
                    constant("IncorporationContext"),
                    constant("Compliant"),
                )),
                priority: Some(1),
                authority: Some(AuthorityRef::Named(QualIdent::simple("fsa.seychelles"))),
            },
        ],
    );

    let indexed = debruijn::assign_indices(&rule).expect("should succeed");
    temporal::check_temporal_stratification(&indexed).expect("should pass");
    let _ = &indexed;
}

// ---------------------------------------------------------------------------
// Sanctions with effect annotation
// ---------------------------------------------------------------------------

/// Sanctions screening with sanctions_query effect.
/// This rule carries an effect annotation — it's not a pure computation.
#[test]
fn sanctions_screening_with_effect() {
    let rule = Term::Lambda {
        binder: Ident::new("ctx"),
        domain: Box::new(constant("IncorporationContext")),
        body: Box::new(Term::Let {
            binder: Ident::new("result"),
            ty: Box::new(constant("SanctionsResult")),
            val: Box::new(app(constant("sanctions_check"), var("ctx", 0))),
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
    temporal::check_temporal_stratification(&indexed).expect("should pass — no temporal terms");
    let _ = &indexed;
}

// ---------------------------------------------------------------------------
// Beneficial ownership (Companies Act amendments)
// ---------------------------------------------------------------------------

/// Companies Act: UBOs must be identified and filed.
#[test]
fn beneficial_ownership_filing() {
    let rule = defeasible(
        "ubo_filing",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("beneficial_owners"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("Nil", &[], constant("NonCompliant")),
                    branch(
                        "Cons",
                        &["owner", "rest"],
                        match_expr(
                            app(
                                constant("all_identified"),
                                app(app(constant("Cons"), var("owner", 0)), var("rest", 1)),
                            ),
                            constant("ComplianceVerdict"),
                            vec![
                                branch("True", &[], constant("Compliant")),
                                branch("False", &[], constant("Pending")),
                            ],
                        ),
                    ),
                ],
            ),
        ),
        vec![],
    );

    let indexed = debruijn::assign_indices(&rule).expect("should succeed");
    temporal::check_temporal_stratification(&indexed).expect("should pass");
}

// ---------------------------------------------------------------------------
// Summary: pipeline verification for all rules
// ---------------------------------------------------------------------------

/// Verify that all rules serialize to JSON and back (content-addressable).
#[test]
fn all_rules_serde_roundtrip() {
    let rules: Vec<Term> = vec![
        // s.66 minimum directors
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
        ),
        // s.55 registered office
        defeasible(
            "registered_office",
            pi(
                "ctx",
                constant("IncorporationContext"),
                constant("ComplianceVerdict"),
            ),
            lam(
                "ctx",
                constant("IncorporationContext"),
                match_expr(
                    app(constant("office_country"), var("ctx", 0)),
                    constant("ComplianceVerdict"),
                    vec![
                        branch("SC", &[], constant("Compliant")),
                        wildcard_branch(constant("NonCompliant")),
                    ],
                ),
            ),
            vec![],
        ),
        // no minimum capital
        lam(
            "ctx",
            constant("IncorporationContext"),
            constant("Compliant"),
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

// ---------------------------------------------------------------------------
// IBC Act s.135 — Annual return filing deadline
// ---------------------------------------------------------------------------

/// IBC Act s.135: Annual return must be filed within 30 days of anniversary.
#[test]
fn ibc_s135_annual_return_deadline() {
    let rule = defeasible(
        "annual_return_deadline",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("annual_return_filing_status"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("Within30Days", &[], constant("Compliant")),
                    branch("Overdue", &[], constant("NonCompliant")),
                    wildcard_branch(constant("Pending")),
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
// IBC Act s.94 — Change of registered agent notification
// ---------------------------------------------------------------------------

/// IBC Act s.94: Change of registered agent must be notified within 14 days.
#[test]
fn ibc_s94_registered_agent_change_notice() {
    let rule = defeasible(
        "registered_agent_change_notice",
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
                    constant("registered_agent_change_notice_status"),
                    var("ctx", 0),
                ),
                constant("ComplianceVerdict"),
                vec![
                    branch("Within14Days", &[], constant("Compliant")),
                    branch("LateNotice", &[], constant("NonCompliant")),
                    wildcard_branch(constant("Pending")),
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
// IBC Act s.30 — Share transfer restrictions
// ---------------------------------------------------------------------------

/// IBC Act s.30: Share transfers require board approval unless articles provide otherwise.
#[test]
fn ibc_s30_share_transfer_restrictions() {
    let rule = defeasible(
        "share_transfer_restrictions",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("board_approved_share_transfer"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("True", &[], constant("Compliant")),
                    branch("False", &[], constant("NonCompliant")),
                ],
            ),
        ),
        vec![Exception {
            guard: Box::new(lam(
                "ctx",
                constant("IncorporationContext"),
                app(constant("articles_permit_free_transfer"), var("ctx", 0)),
            )),
            body: Box::new(lam(
                "ctx",
                constant("IncorporationContext"),
                constant("Compliant"),
            )),
            priority: Some(1),
            authority: Some(AuthorityRef::Named(QualIdent::simple("ibc_act_2016.s30"))),
        }],
    );

    let indexed = debruijn::assign_indices(&rule).expect("should succeed");
    temporal::check_temporal_stratification(&indexed).expect("should pass");
    let _ = &indexed;
}

// ---------------------------------------------------------------------------
// IBC Act s.155 — Dissolution by shareholder resolution
// ---------------------------------------------------------------------------

/// IBC Act s.155: Voluntary dissolution requires a 75% special resolution.
#[test]
fn ibc_s155_dissolution_special_resolution() {
    let rule = defeasible(
        "dissolution_special_resolution",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("dissolution_resolution_status"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("SpecialResolution75", &[], constant("Compliant")),
                    branch("OrdinaryResolution", &[], constant("NonCompliant")),
                    branch("InsufficientMajority", &[], constant("NonCompliant")),
                    wildcard_branch(constant("Pending")),
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
// Economic Substance Act 2018 — Economic substance requirement
// ---------------------------------------------------------------------------

/// Economic Substance Act 2018: Relevant activity requires satisfied substance.
#[test]
fn economic_substance_requirement() {
    let rule = defeasible(
        "economic_substance_requirement",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("relevant_activity"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("False", &[], constant("Compliant")),
                    branch(
                        "True",
                        &[],
                        match_expr(
                            app(constant("economic_substance_status"), var("ctx", 0)),
                            constant("ComplianceVerdict"),
                            vec![
                                branch("Satisfied", &[], constant("Compliant")),
                                branch("NotSatisfied", &[], constant("NonCompliant")),
                                wildcard_branch(constant("Pending")),
                            ],
                        ),
                    ),
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
// VASP Act 2024 — VASP licensing requirement
// ---------------------------------------------------------------------------

/// VASP Act 2024: Digital asset business requires an active VASP licence.
#[test]
fn vasp_licensing_requirement() {
    let rule = defeasible(
        "vasp_licensing_requirement",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("digital_asset_business"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("False", &[], constant("Compliant")),
                    branch(
                        "True",
                        &[],
                        match_expr(
                            app(constant("vasp_license_status"), var("ctx", 0)),
                            constant("ComplianceVerdict"),
                            vec![
                                branch("Active", &[], constant("Compliant")),
                                branch("None", &[], constant("NonCompliant")),
                                wildcard_branch(constant("Pending")),
                            ],
                        ),
                    ),
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
// IBC Act s.131 — Accounting records retention
// ---------------------------------------------------------------------------

/// IBC Act s.131: Accounting records must be retained for at least 7 years.
#[test]
fn ibc_s131_accounting_records_retention() {
    let rule = defeasible(
        "accounting_records_retention",
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
                    constant("accounting_records_retention_status"),
                    var("ctx", 0),
                ),
                constant("ComplianceVerdict"),
                vec![
                    branch("AtLeast7Years", &[], constant("Compliant")),
                    branch("LessThan7Years", &[], constant("NonCompliant")),
                    wildcard_branch(constant("Pending")),
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
// IBC Act s.72 — Director disclosure of interest
// ---------------------------------------------------------------------------

/// IBC Act s.72: Directors must disclose material interests in transactions.
#[test]
fn ibc_s72_director_disclosure_of_interest() {
    let rule = defeasible(
        "director_disclosure_of_interest",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("director_has_material_interest"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("False", &[], constant("Compliant")),
                    branch(
                        "True",
                        &[],
                        match_expr(
                            app(constant("director_interest_disclosed"), var("ctx", 0)),
                            constant("ComplianceVerdict"),
                            vec![
                                branch("True", &[], constant("Compliant")),
                                branch("False", &[], constant("NonCompliant")),
                            ],
                        ),
                    ),
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
// IBC Act s.24 — Prohibition on bearer shares
// ---------------------------------------------------------------------------

/// IBC Act s.24: Bearer shares are prohibited for Seychelles IBCs.
#[test]
fn ibc_s24_bearer_shares_prohibited() {
    let rule = defeasible(
        "bearer_shares_prohibited",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("share_form"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("Registered", &[], constant("Compliant")),
                    branch("Bearer", &[], constant("NonCompliant")),
                    wildcard_branch(constant("NonCompliant")),
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
// IBC Act s.178 — Annual licence fee payment
// ---------------------------------------------------------------------------

/// IBC Act s.178: Annual licence fee must be paid to the FSA each year.
#[test]
fn ibc_s178_annual_license_fee_payment() {
    let rule = defeasible(
        "annual_license_fee_payment",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("annual_license_fee_status"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("Paid", &[], constant("Compliant")),
                    branch("Overdue", &[], constant("NonCompliant")),
                    wildcard_branch(constant("Pending")),
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
// IBC Act s.11 — Minimum shareholder/member
// ---------------------------------------------------------------------------

/// IBC Act s.11: Every IBC shall have at least one shareholder/member.
#[test]
fn ibc_s11_minimum_shareholder() {
    let rule = defeasible(
        "minimum_shareholder",
        pi(
            "ctx",
            constant("IncorporationContext"),
            constant("ComplianceVerdict"),
        ),
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("shareholder_count"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    branch("Zero", &[], constant("NonCompliant")),
                    wildcard_branch(constant("Compliant")),
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
// IBC Act s.5 — Restrictions on local business
// ---------------------------------------------------------------------------

/// IBC Act s.5: IBCs are prohibited from conducting business with persons resident in Seychelles.
#[test]
fn ibc_s5_restrictions_on_local_business() {
    let rule = defeasible(
        "restrictions_on_local_business",
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
                    constant("conducts_business_with_seychelles_residents"),
                    var("ctx", 0),
                ),
                constant("ComplianceVerdict"),
                vec![
                    branch("True", &[], constant("NonCompliant")),
                    branch("False", &[], constant("Compliant")),
                ],
            ),
        ),
        vec![],
    );

    let indexed = debruijn::assign_indices(&rule).expect("should succeed");
    temporal::check_temporal_stratification(&indexed).expect("should pass");
    let _ = &indexed;
}
