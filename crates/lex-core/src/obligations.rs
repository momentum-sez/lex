//! Proof obligation extraction for typed Lex terms.
//!
//! The extractor walks the Core Lex AST and emits proof obligations for
//! structurally significant nodes such as matches, defeasible rules,
//! sanctions queries, threshold checks, identity checks, and temporal terms.

use crate::ast::{
    Branch, Effect, EffectRow, Pattern, QualIdent, ScopeConstraint, ScopeField, Term, TimeTerm,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObligationCategory {
    DomainMembership,
    ThresholdComparison,
    ExhaustiveMatch,
    SanctionsCheck,
    TemporalOrdering,
    IdentityVerification,
    DefeasibleResolution,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofObligation {
    pub id: String,
    pub description: String,
    pub category: ObligationCategory,
    pub term: Term,
    pub expected: String,
    pub suggested_procedure: String,
}

pub fn extract_obligations(term: &Term) -> Vec<ProofObligation> {
    let mut obligations = Vec::new();
    let mut counter = 0usize;
    collect_term(term, &mut obligations, &mut counter);
    obligations
}

fn collect_term(term: &Term, obligations: &mut Vec<ProofObligation>, counter: &mut usize) {
    match term {
        Term::Match {
            scrutinee,
            return_ty,
            branches,
        } => {
            push_obligation(
                obligations,
                counter,
                ObligationCategory::ExhaustiveMatch,
                term,
                format!(
                    "match over `{}` must cover every constructor in the scrutinee domain ({})",
                    summarize_term(scrutinee),
                    summarize_branches(branches)
                ),
                "all match arms jointly cover the scrutinee domain".to_string(),
                "finite_domain_enumeration".to_string(),
            );

            if match_requires_domain_membership(scrutinee, branches) {
                push_obligation(
                    obligations,
                    counter,
                    ObligationCategory::DomainMembership,
                    term,
                    format!(
                        "match scrutinee `{}` must inhabit the finite branch domain before coverage can be certified",
                        summarize_term(scrutinee)
                    ),
                    "the scrutinee is a member of the matched finite domain".to_string(),
                    "finite_domain_enumeration".to_string(),
                );
            }

            collect_term(scrutinee, obligations, counter);
            collect_term(return_ty, obligations, counter);
            for branch in branches {
                collect_term(&branch.body, obligations, counter);
            }
        }

        Term::Defeasible(rule) => {
            push_obligation(
                obligations,
                counter,
                ObligationCategory::DefeasibleResolution,
                term,
                format!(
                    "defeasible rule `{}` requires decidable guards and stable priority resolution across {} exception(s)",
                    rule.name.name,
                    rule.exceptions.len()
                ),
                "each exception guard is decidable and the highest-priority satisfied exception determines the outcome"
                    .to_string(),
                "fuel_bounded_defeasible_search".to_string(),
            );

            collect_term(&rule.base_ty, obligations, counter);
            collect_term(&rule.base_body, obligations, counter);
            for exception in &rule.exceptions {
                collect_term(&exception.guard, obligations, counter);
                collect_term(&exception.body, obligations, counter);
            }
        }

        Term::App { func, arg } => {
            if let Some(head) = application_head_name(term) {
                if is_sanctions_name(&head) {
                    push_obligation(
                        obligations,
                        counter,
                        ObligationCategory::SanctionsCheck,
                        term,
                        format!(
                            "application `{}` requires a sanctions proof before the rule may conclude",
                            head
                        ),
                        "the sanctions screening resolves to a clear or compliant outcome"
                            .to_string(),
                        "bdd_style_boolean_compliance".to_string(),
                    );
                }

                if is_threshold_name(&head) {
                    push_obligation(
                        obligations,
                        counter,
                        ObligationCategory::ThresholdComparison,
                        term,
                        format!(
                            "application `{}` must establish the threshold comparison on the supplied amounts",
                            head
                        ),
                        "the comparison is provable in the arithmetic fragment".to_string(),
                        "presburger_arithmetic".to_string(),
                    );
                }

                if is_identity_name(&head) {
                    push_obligation(
                        obligations,
                        counter,
                        ObligationCategory::IdentityVerification,
                        term,
                        format!(
                            "application `{}` requires verified identity evidence for the referenced party",
                            head
                        ),
                        "the referenced subject is identity-verified".to_string(),
                        "identity_attestation_chain".to_string(),
                    );
                }

                if is_temporal_name(&head) {
                    push_obligation(
                        obligations,
                        counter,
                        ObligationCategory::TemporalOrdering,
                        term,
                        format!(
                            "application `{}` requires a provable temporal ordering or filing window constraint",
                            head
                        ),
                        "the temporal relation is ordered and non-contradictory".to_string(),
                        "temporal_stratification_check".to_string(),
                    );
                }
            }

            collect_app_func(func, obligations, counter);
            collect_term(arg, obligations, counter);
        }

        Term::SanctionsDominance { proof } => {
            push_obligation(
                obligations,
                counter,
                ObligationCategory::SanctionsCheck,
                term,
                "sanctions-dominance requires proof that a sanctions non-compliance result overrides competing outcomes"
                    .to_string(),
                "sanctions non-compliance is established and dominates the downstream branch"
                    .to_string(),
                "bdd_style_boolean_compliance".to_string(),
            );
            collect_term(proof, obligations, counter);
        }

        Term::Lift0 { time } => {
            push_obligation(
                obligations,
                counter,
                ObligationCategory::TemporalOrdering,
                term,
                "lift₀ requires a well-ordered promotion from Time₀ to Time₁".to_string(),
                "the lifted term originates from a valid Time₀ witness".to_string(),
                "temporal_stratification_check".to_string(),
            );
            collect_term(time, obligations, counter);
        }

        Term::Derive1 { time, witness } => {
            push_obligation(
                obligations,
                counter,
                ObligationCategory::TemporalOrdering,
                term,
                "derive₁ requires a justified temporal rewrite from frozen time".to_string(),
                "the derived Time₁ term is backed by a valid rewrite witness".to_string(),
                "temporal_stratification_check".to_string(),
            );
            collect_term(time, obligations, counter);
            collect_term(witness, obligations, counter);
        }

        Term::Lambda { domain, body, .. } => {
            collect_term(domain, obligations, counter);
            collect_term(body, obligations, counter);
        }

        Term::Pi {
            domain,
            effect_row,
            codomain,
            ..
        } => {
            if let Some(row) = effect_row {
                if ast_effect_row_has_sanctions(row) {
                    push_obligation(
                        obligations,
                        counter,
                        ObligationCategory::SanctionsCheck,
                        term,
                        "effectful function type carries `sanctions_query` and therefore requires sanctions clearance"
                            .to_string(),
                        "every use of the effect row can discharge the sanctions query".to_string(),
                        "bdd_style_boolean_compliance".to_string(),
                    );
                }
                collect_effect_row(term, row, obligations, counter);
            }

            collect_term(domain, obligations, counter);
            collect_term(codomain, obligations, counter);
        }

        Term::Sigma { fst_ty, snd_ty, .. } => {
            collect_term(fst_ty, obligations, counter);
            collect_term(snd_ty, obligations, counter);
        }

        Term::Annot { term: inner, ty } => {
            collect_term(inner, obligations, counter);
            collect_term(ty, obligations, counter);
        }

        Term::Let { ty, val, body, .. } => {
            collect_term(ty, obligations, counter);
            collect_term(val, obligations, counter);
            collect_term(body, obligations, counter);
        }

        Term::Rec { ty, body, .. } => {
            collect_term(ty, obligations, counter);
            collect_term(body, obligations, counter);
        }

        Term::ModalAt { time, body } => {
            push_obligation(
                obligations,
                counter,
                ObligationCategory::TemporalOrdering,
                term,
                "modal `@` requires a well-formed temporal witness".to_string(),
                "the body is evaluated at a coherent time point".to_string(),
                "temporal_stratification_check".to_string(),
            );
            collect_time_term(time, obligations, counter);
            collect_term(body, obligations, counter);
        }

        Term::ModalEventually { time, body } => {
            push_obligation(
                obligations,
                counter,
                ObligationCategory::TemporalOrdering,
                term,
                "eventual modality requires a provable future witness".to_string(),
                "the body holds at some admissible future time".to_string(),
                "temporal_stratification_check".to_string(),
            );
            collect_time_term(time, obligations, counter);
            collect_term(body, obligations, counter);
        }

        Term::ModalAlways { from, to, body } => {
            push_obligation(
                obligations,
                counter,
                ObligationCategory::TemporalOrdering,
                term,
                "always modality requires an ordered interval with `from <= to`".to_string(),
                "the interval bounds are ordered and the body is stable throughout the interval"
                    .to_string(),
                "temporal_stratification_check".to_string(),
            );
            collect_time_term(from, obligations, counter);
            collect_time_term(to, obligations, counter);
            collect_term(body, obligations, counter);
        }

        Term::ModalIntro { body, .. } => {
            collect_term(body, obligations, counter);
        }

        Term::ModalElim {
            term: inner,
            witness,
            ..
        } => {
            collect_term(inner, obligations, counter);
            collect_term(witness, obligations, counter);
        }

        Term::Hole(hole) => {
            if let Some(scope) = &hole.scope {
                if scope_has_domain_constraint(scope) {
                    push_obligation(
                        obligations,
                        counter,
                        ObligationCategory::DomainMembership,
                        term,
                        "hole scope constrains the filler to a specific jurisdiction or entity class"
                            .to_string(),
                        "the chosen filler inhabits the scoped domain".to_string(),
                        "finite_domain_enumeration".to_string(),
                    );
                }

                if scope_has_time_window(scope) {
                    push_obligation(
                        obligations,
                        counter,
                        ObligationCategory::TemporalOrdering,
                        term,
                        "hole scope includes a time window that must be temporally ordered"
                            .to_string(),
                        "the time window bounds are coherent and non-retroactive".to_string(),
                        "temporal_stratification_check".to_string(),
                    );
                }

                collect_scope(scope, obligations, counter);
            }

            collect_term(&hole.ty, obligations, counter);
        }

        Term::HoleFill { filler, pcauth, .. } => {
            collect_term(filler, obligations, counter);
            collect_term(pcauth, obligations, counter);
        }

        Term::PrincipleBalance(step) => {
            collect_term(&step.verdict, obligations, counter);
            collect_term(&step.rationale, obligations, counter);
        }

        Term::Unlock { effect_row, body } => {
            collect_term(effect_row, obligations, counter);
            collect_term(body, obligations, counter);
        }

        Term::Pair { fst, snd } => {
            collect_term(fst, obligations, counter);
            collect_term(snd, obligations, counter);
        }

        Term::Proj { pair, .. } => {
            collect_term(pair, obligations, counter);
        }

        Term::InductiveIntro { args, .. } => {
            for arg in args {
                collect_term(arg, obligations, counter);
            }
        }

        Term::DefeatElim { rule } => {
            collect_term(rule, obligations, counter);
        }

        Term::Constant(name) => {
            collect_name_obligations(name_to_string(name), term, obligations, counter);
        }

        Term::AxiomUse { axiom } => {
            collect_name_obligations(name_to_string(axiom), term, obligations, counter);
        }

        Term::Var { name, .. } => {
            collect_name_obligations(name.name.clone(), term, obligations, counter);
        }

        Term::ContentRefTerm(_)
        | Term::Sort(_)
        | Term::IntLit(_)
        | Term::RatLit(_, _)
        | Term::StringLit(_) => {}
    }
}

fn collect_time_term(
    time: &TimeTerm,
    obligations: &mut Vec<ProofObligation>,
    counter: &mut usize,
) {
    match time {
        TimeTerm::Literal(_) | TimeTerm::Var { .. } => {}
        TimeTerm::AsOf0(term) | TimeTerm::AsOf1(term) => collect_term(term, obligations, counter),
        TimeTerm::Lift0(inner) => collect_time_term(inner, obligations, counter),
        TimeTerm::Derive1 { time, witness } => {
            collect_time_term(time, obligations, counter);
            collect_term(&witness.term, obligations, counter);
        }
    }
}

fn collect_effect_row(
    _owner: &Term,
    row: &EffectRow,
    obligations: &mut Vec<ProofObligation>,
    counter: &mut usize,
) {
    match row {
        EffectRow::Empty | EffectRow::Var(_) => {}
        EffectRow::Effects(effects) => {
            for effect in effects {
                if let Effect::Write(scope) = effect {
                    collect_term(scope, obligations, counter);
                }
            }
        }
        EffectRow::Join(left, right) => {
            collect_effect_row(_owner, left, obligations, counter);
            collect_effect_row(_owner, right, obligations, counter);
        }
        EffectRow::BranchSensitive(inner) => {
            collect_effect_row(_owner, inner, obligations, counter)
        }
    }
}

fn collect_scope(
    scope: &ScopeConstraint,
    obligations: &mut Vec<ProofObligation>,
    counter: &mut usize,
) {
    for field in &scope.fields {
        match field {
            ScopeField::TimeWindow { from, to } => {
                collect_time_term(from, obligations, counter);
                collect_time_term(to, obligations, counter);
            }
            ScopeField::EntityClass(term) => collect_term(term, obligations, counter),
            ScopeField::Corridor(_) | ScopeField::Jurisdiction(_) => {}
        }
    }
}

fn collect_name_obligations(
    raw_name: String,
    term: &Term,
    obligations: &mut Vec<ProofObligation>,
    counter: &mut usize,
) {
    if is_identity_name(&raw_name) {
        push_obligation(
            obligations,
            counter,
            ObligationCategory::IdentityVerification,
            term,
            format!(
                "symbol `{}` carries an identity-verification obligation",
                raw_name
            ),
            "the referenced subject is identity-verified".to_string(),
            "identity_attestation_chain".to_string(),
        );
    }

    if is_temporal_name(&raw_name) {
        push_obligation(
            obligations,
            counter,
            ObligationCategory::TemporalOrdering,
            term,
            format!(
                "symbol `{}` denotes a temporal ordering or deadline predicate",
                raw_name
            ),
            "the referenced temporal predicate is satisfiable and ordered".to_string(),
            "temporal_stratification_check".to_string(),
        );
    }
}

fn push_obligation(
    obligations: &mut Vec<ProofObligation>,
    counter: &mut usize,
    category: ObligationCategory,
    term: &Term,
    description: String,
    expected: String,
    suggested_procedure: String,
) {
    *counter += 1;
    obligations.push(ProofObligation {
        id: format!("obl-{:04}", *counter),
        description,
        category,
        term: term.clone(),
        expected,
        suggested_procedure,
    });
}

fn application_head_name(term: &Term) -> Option<String> {
    let mut cursor = term;
    loop {
        match cursor {
            Term::App { func, .. } => cursor = func.as_ref(),
            Term::Constant(name) => return Some(name_to_string(name)),
            Term::AxiomUse { axiom } => return Some(name_to_string(axiom)),
            Term::Var { name, .. } => return Some(name.name.clone()),
            _ => return None,
        }
    }
}

fn collect_app_func(term: &Term, obligations: &mut Vec<ProofObligation>, counter: &mut usize) {
    match term {
        Term::App { func, arg } => {
            collect_app_func(func, obligations, counter);
            collect_term(arg, obligations, counter);
        }
        Term::Constant(_) | Term::AxiomUse { .. } | Term::Var { .. } => {}
        _ => collect_term(term, obligations, counter),
    }
}

fn summarize_term(term: &Term) -> String {
    match term {
        Term::Var { name, .. } => name.name.clone(),
        Term::Constant(name) => name_to_string(name),
        Term::AxiomUse { axiom } => name_to_string(axiom),
        Term::App { .. } => application_head_name(term).unwrap_or_else(|| "application".to_string()),
        Term::Match { .. } => "match".to_string(),
        Term::Defeasible(rule) => rule.name.name.clone(),
        Term::StringLit(value) => value.clone(),
        Term::IntLit(value) => value.to_string(),
        _ => "term".to_string(),
    }
}

fn summarize_branches(branches: &[Branch]) -> String {
    let labels = branches
        .iter()
        .map(|branch| match &branch.pattern {
            Pattern::Constructor { constructor, .. } => name_to_string(&constructor.name),
            Pattern::Wildcard => "_".to_string(),
        })
        .collect::<Vec<_>>();
    labels.join(", ")
}

fn match_requires_domain_membership(scrutinee: &Term, branches: &[Branch]) -> bool {
    let has_constructor_pattern = branches
        .iter()
        .any(|branch| matches!(branch.pattern, Pattern::Constructor { .. }));

    has_constructor_pattern
        || application_head_name(scrutinee)
            .map(|name| is_domain_name(&name))
            .unwrap_or(false)
}

fn scope_has_domain_constraint(scope: &ScopeConstraint) -> bool {
    scope.fields.iter().any(|field| {
        matches!(
            field,
            ScopeField::Jurisdiction(_) | ScopeField::EntityClass(_)
        )
    })
}

fn scope_has_time_window(scope: &ScopeConstraint) -> bool {
    scope
        .fields
        .iter()
        .any(|field| matches!(field, ScopeField::TimeWindow { .. }))
}

fn name_to_string(name: &QualIdent) -> String {
    name.segments.join(".")
}

fn normalize_name(name: &str) -> String {
    name.chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() {
                ch.to_ascii_lowercase()
            } else {
                '_'
            }
        })
        .collect()
}

fn is_sanctions_name(name: &str) -> bool {
    normalize_name(name).contains("sanction")
}

fn is_threshold_name(name: &str) -> bool {
    let normalized = normalize_name(name);
    let exact = [
        "gt",
        "gte",
        "lt",
        "lte",
        "eq",
        "ge",
        "le",
        "threshold_check",
    ];
    exact.contains(&normalized.as_str())
        || [
            "threshold",
            "compare",
            "comparison",
            "greater_than",
            "less_than",
            "at_least",
            "at_most",
            "amount_exceeds",
            "amount_below",
            "amount_above",
        ]
        .iter()
        .any(|needle| normalized.contains(needle))
}

fn is_identity_name(name: &str) -> bool {
    let normalized = normalize_name(name);
    [
        "identity",
        "passport",
        "kyc",
        "identified",
        "beneficial_owner",
        "beneficial_owners",
        "holder_verification",
        "document_check",
    ]
    .iter()
    .any(|needle| normalized.contains(needle))
}

fn is_temporal_name(name: &str) -> bool {
    let normalized = normalize_name(name);
    [
        "before",
        "after",
        "within",
        "deadline",
        "expiry",
        "expires",
        "effective",
        "not_before",
        "not_after",
        "time_window",
        "asof",
    ]
    .iter()
    .any(|needle| normalized.contains(needle))
}

fn is_domain_name(name: &str) -> bool {
    let normalized = normalize_name(name);
    [
        "jurisdiction",
        "country",
        "entity_type",
        "company_class",
        "status",
        "verdict",
        "result",
        "share_form",
        "suffix",
    ]
    .iter()
    .any(|needle| normalized.contains(needle))
}

fn ast_effect_row_has_sanctions(row: &EffectRow) -> bool {
    match row {
        EffectRow::Empty | EffectRow::Var(_) => false,
        EffectRow::Effects(effects) => effects
            .iter()
            .any(|effect| matches!(effect, Effect::SanctionsQuery)),
        EffectRow::Join(left, right) => {
            ast_effect_row_has_sanctions(left) || ast_effect_row_has_sanctions(right)
        }
        EffectRow::BranchSensitive(inner) => ast_effect_row_has_sanctions(inner),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{
        AuthorityRef, Branch, Constructor, Exception, Hole, Ident, Pattern, QualIdent,
        ScopeConstraint, ScopeField, Sort, TimeLiteral,
    };

    fn ident(name: &str) -> Ident {
        Ident::new(name)
    }

    fn qual(name: &str) -> QualIdent {
        QualIdent::simple(name)
    }

    fn constructor(name: &str) -> Constructor {
        Constructor::new(qual(name))
    }

    fn constant(name: &str) -> Term {
        Term::constant(name)
    }

    fn var(name: &str) -> Term {
        Term::var(name, 0)
    }

    fn app2(head: &str, left: Term, right: Term) -> Term {
        Term::app(Term::app(constant(head), left), right)
    }

    fn app3(head: &str, first: Term, second: Term, third: Term) -> Term {
        Term::app(app2(head, first, second), third)
    }

    fn ctor_branch(name: &str, body: Term) -> Branch {
        Branch {
            pattern: Pattern::Constructor {
                constructor: constructor(name),
                binders: Vec::new(),
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

    fn time_literal(iso8601: &str) -> TimeTerm {
        TimeTerm::Literal(TimeLiteral {
            iso8601: iso8601.to_string(),
        })
    }

    fn find_categories(obligations: &[ProofObligation]) -> Vec<ObligationCategory> {
        obligations.iter().map(|obligation| obligation.category).collect()
    }

    fn count_category(
        obligations: &[ProofObligation],
        category: ObligationCategory,
    ) -> usize {
        obligations
            .iter()
            .filter(|obligation| obligation.category == category)
            .count()
    }

    fn first_by_category(
        obligations: &[ProofObligation],
        category: ObligationCategory,
    ) -> &ProofObligation {
        obligations
            .iter()
            .find(|obligation| obligation.category == category)
            .unwrap_or_else(|| panic!("missing obligation for {category:?}"))
    }

    fn sample_defeasible_rule() -> Term {
        Term::Defeasible(crate::ast::DefeasibleRule {
            name: ident("late_filing_exception"),
            base_ty: Box::new(Term::Sort(Sort::Prop)),
            base_body: Box::new(constant("report_required")),
            exceptions: vec![
                Exception {
                    guard: Box::new(constant("is_market_maker")),
                    body: Box::new(constant("market_maker_exception")),
                    priority: Some(50),
                    authority: None,
                },
                Exception {
                    guard: Box::new(constant("is_regulated_bank")),
                    body: Box::new(constant("bank_exception")),
                    priority: Some(20),
                    authority: None,
                },
            ],
            lattice: None,
        })
    }

    #[test]
    fn ibc_jurisdiction_match_extracts_domain_and_exhaustive_obligations() {
        let term = Term::match_expr(
            Term::app(constant("jurisdiction_status"), var("ctx")),
            constant("ComplianceVerdict"),
            vec![
                ctor_branch("IBC", constant("Compliant")),
                ctor_branch("ADGM", constant("Pending")),
                ctor_branch("SC", constant("NonCompliant")),
            ],
        );

        let obligations = extract_obligations(&term);
        let categories = find_categories(&obligations);

        assert!(categories.contains(&ObligationCategory::ExhaustiveMatch));
        assert!(categories.contains(&ObligationCategory::DomainMembership));
        assert_eq!(count_category(&obligations, ObligationCategory::ExhaustiveMatch), 1);
    }

    #[test]
    fn wildcard_jurisdiction_match_still_requires_exhaustive_coverage() {
        let term = Term::match_expr(
            Term::app(constant("office_country"), var("company")),
            constant("ComplianceVerdict"),
            vec![
                ctor_branch("IBC", constant("Compliant")),
                wildcard_branch(constant("Pending")),
            ],
        );

        let obligations = extract_obligations(&term);
        let exhaustive = first_by_category(&obligations, ObligationCategory::ExhaustiveMatch);

        assert!(exhaustive.description.contains("IBC, _"));
        assert_eq!(count_category(&obligations, ObligationCategory::ExhaustiveMatch), 1);
    }

    #[test]
    fn defeasible_rule_extracts_defeasible_resolution_obligation() {
        let term = sample_defeasible_rule();

        let obligations = extract_obligations(&term);
        let obligation =
            first_by_category(&obligations, ObligationCategory::DefeasibleResolution);

        assert!(obligation.description.contains("late_filing_exception"));
        assert_eq!(
            obligation.suggested_procedure,
            "fuel_bounded_defeasible_search"
        );
    }

    #[test]
    fn sanctions_check_application_extracts_sanctions_obligation() {
        let term = Term::app(constant("sanctions_check"), var("counterparty"));

        let obligations = extract_obligations(&term);
        let obligation = first_by_category(&obligations, ObligationCategory::SanctionsCheck);

        assert_eq!(obligation.term, term);
        assert!(obligation.description.contains("sanctions_check"));
    }

    #[test]
    fn adgm_screening_application_extracts_sanctions_obligation() {
        let term = Term::app(
            constant("adgm_statutory_sanctions_screen"),
            var("applicant"),
        );

        let obligations = extract_obligations(&term);

        assert_eq!(count_category(&obligations, ObligationCategory::SanctionsCheck), 1);
    }

    #[test]
    fn threshold_check_application_extracts_threshold_obligation() {
        let term = app3(
            "threshold_check",
            var("transaction_amount"),
            Term::IntLit(100_000),
            Term::StringLit(">=".to_string()),
        );

        let obligations = extract_obligations(&term);
        let obligation =
            first_by_category(&obligations, ObligationCategory::ThresholdComparison);

        assert_eq!(obligation.suggested_procedure, "presburger_arithmetic");
        assert_eq!(obligation.term, term);
    }

    #[test]
    fn amount_exceeds_application_extracts_threshold_obligation() {
        let term = app2("amount_exceeds", var("wire_amount"), Term::IntLit(1_000_000));

        let obligations = extract_obligations(&term);

        assert_eq!(
            count_category(&obligations, ObligationCategory::ThresholdComparison),
            1
        );
    }

    #[test]
    fn all_identified_application_extracts_identity_obligation() {
        let term = Term::app(constant("all_identified"), var("ubo_register"));

        let obligations = extract_obligations(&term);
        let obligation =
            first_by_category(&obligations, ObligationCategory::IdentityVerification);

        assert!(obligation.description.contains("all_identified"));
        assert_eq!(obligation.expected, "the referenced subject is identity-verified");
    }

    #[test]
    fn modal_always_extracts_temporal_ordering_obligation() {
        let term = Term::ModalAlways {
            from: time_literal("2026-01-01T00:00:00Z"),
            to: time_literal("2026-12-31T23:59:59Z"),
            body: Box::new(constant("annual_return_on_time")),
        };

        let obligations = extract_obligations(&term);
        let obligation = first_by_category(&obligations, ObligationCategory::TemporalOrdering);

        assert!(obligation.description.contains("from <= to"));
        assert_eq!(obligation.term, term);
    }

    #[test]
    fn before_deadline_application_extracts_temporal_ordering_obligation() {
        let term = app2("before_deadline", var("submitted_at"), var("cutoff"));

        let obligations = extract_obligations(&term);

        assert_eq!(
            count_category(&obligations, ObligationCategory::TemporalOrdering),
            1
        );
    }

    #[test]
    fn hole_scope_extracts_domain_membership_and_temporal_ordering() {
        let term = Term::Hole(Hole {
            name: Some(ident("board_resolution_window")),
            ty: Box::new(Term::Sort(Sort::Prop)),
            authority: AuthorityRef::Named(qual("registrar")),
            scope: Some(ScopeConstraint {
                fields: vec![
                    ScopeField::Jurisdiction(qual("IBC")),
                    ScopeField::TimeWindow {
                        from: time_literal("2026-03-01T00:00:00Z"),
                        to: time_literal("2026-03-31T23:59:59Z"),
                    },
                ],
            }),
        });

        let obligations = extract_obligations(&term);
        let categories = find_categories(&obligations);

        assert!(categories.contains(&ObligationCategory::DomainMembership));
        assert!(categories.contains(&ObligationCategory::TemporalOrdering));
    }

    #[test]
    fn recursive_let_walk_collects_nested_ibc_rule_obligations() {
        let term = Term::let_in(
            "screening",
            Term::type_sort(0),
            Term::app(constant("sanctions_check"), var("counterparty")),
            Term::match_expr(
                app3(
                    "threshold_check",
                    var("transaction_amount"),
                    Term::IntLit(50_000),
                    Term::StringLit(">=".to_string()),
                ),
                constant("ComplianceVerdict"),
                vec![
                    ctor_branch("Compliant", sample_defeasible_rule()),
                    ctor_branch(
                        "Pending",
                        Term::app(constant("all_identified"), var("beneficial_owners")),
                    ),
                    ctor_branch(
                        "NonCompliant",
                        Term::ModalAt {
                            time: time_literal("2026-06-01T00:00:00Z"),
                            body: Box::new(constant("freeze_account")),
                        },
                    ),
                ],
            ),
        );

        let obligations = extract_obligations(&term);
        let categories = find_categories(&obligations);

        assert!(categories.contains(&ObligationCategory::SanctionsCheck));
        assert!(categories.contains(&ObligationCategory::ThresholdComparison));
        assert!(categories.contains(&ObligationCategory::ExhaustiveMatch));
        assert!(categories.contains(&ObligationCategory::DomainMembership));
        assert!(categories.contains(&ObligationCategory::DefeasibleResolution));
        assert!(categories.contains(&ObligationCategory::IdentityVerification));
        assert!(categories.contains(&ObligationCategory::TemporalOrdering));
    }

    #[test]
    fn pi_with_sanctions_effect_row_extracts_sanctions_obligation() {
        let term = Term::Pi {
            binder: ident("_"),
            domain: Box::new(constant("Entity")),
            effect_row: Some(EffectRow::Effects(vec![Effect::SanctionsQuery])),
            codomain: Box::new(constant("SanctionsResult")),
        };

        let obligations = extract_obligations(&term);

        assert!(
            count_category(&obligations, ObligationCategory::SanctionsCheck) >= 1
        );
    }

    #[test]
    fn obligation_ids_are_sequential_and_stable() {
        let term = Term::let_in(
            "verification",
            Term::type_sort(0),
            Term::app(constant("sanctions_check"), var("counterparty")),
            app2("amount_exceeds", var("wire_amount"), Term::IntLit(75_000)),
        );

        let obligations = extract_obligations(&term);
        let ids = obligations
            .iter()
            .map(|obligation| obligation.id.as_str())
            .collect::<Vec<_>>();

        assert_eq!(ids, vec!["obl-0001", "obl-0002"]);
    }
}
