use super::*;
use crate::ast::{Branch, Constructor, DefeasibleRule, Exception, Ident};

fn var(i: u32) -> Term {
    Term::var("v", i)
}
fn pi(a: Term, b: Term) -> Term {
    Term::pi("x", a, b)
}
fn lam(a: Term, b: Term) -> Term {
    Term::lam("x", a, b)
}
fn app(f: Term, a: Term) -> Term {
    Term::app(f, a)
}
fn eq(a: &Term, b: &Term) -> bool {
    let mut fuel = MAX_WHNF_FUEL;
    conv_eq(a, b, 0, &mut fuel).unwrap()
}
fn reduce(t: &Term) -> Term {
    let mut fuel = MAX_WHNF_FUEL;
    whnf(t, 0, &mut fuel).unwrap()
}
fn branch(name: &str, n: usize, body: Term) -> Branch {
    Branch {
        pattern: Pattern::Constructor {
            constructor: Constructor::new(QualIdent::simple(name)),
            binders: (0..n).map(|i| Ident::new(&format!("b{i}"))).collect(),
        },
        body,
    }
}
fn bool_type(scrutinee: Term) -> Term {
    Term::match_expr(
        scrutinee,
        Term::type_sort(1),
        vec![
            branch("True", 0, Term::prop()),
            branch("False", 0, Term::type_sort(0)),
        ],
    )
}
fn rule(guard: Option<Term>) -> Term {
    Term::Defeasible(DefeasibleRule {
        name: Ident::new("r"),
        base_ty: Box::new(Term::type_sort(1)),
        base_body: Box::new(Term::type_sort(0)),
        exceptions: guard
            .map(|g| {
                vec![Exception {
                    guard: Box::new(g),
                    body: Box::new(Term::prop()),
                    priority: Some(10),
                    authority: None,
                }]
            })
            .unwrap_or_default(),
        lattice: None,
        applies_to: None,
    })
}

#[test]
fn malformed_conversion_target_rejected_by_public_check() {
    let bad = Term::annot(Term::type_sort(1), Term::IntLit(0));
    assert!(infer(&Context::empty(), &bad).is_err());
    assert!(check(&Context::empty(), &Term::prop(), &bad).is_err());
}

#[test]
fn malformed_lambda_domain_cannot_hide_behind_annotation_reduction() {
    let bad = Term::annot(Term::type_sort(0), Term::IntLit(0));
    assert!(check(
        &Context::empty(),
        &lam(bad, var(0)),
        &pi(Term::type_sort(0), Term::type_sort(0))
    )
    .is_err());
}

#[test]
fn dependent_context_lookup_keeps_outer_type() {
    let ctx = Context::empty().extend(Term::type_sort(0)).extend(var(0));
    assert!(eq(&infer(&ctx, &var(0)).unwrap(), &var(1)));
    assert!(eq(&infer(&ctx, &var(1)).unwrap(), &Term::type_sort(0)));
}

#[test]
fn dependent_polymorphic_identity_and_application_remain_useful() {
    let id = lam(Term::type_sort(0), lam(var(0), var(0)));
    let ty = pi(Term::type_sort(0), pi(var(0), var(1)));
    check(&Context::empty(), &id, &ty).unwrap();
    let applied = app(Term::annot(id, ty), Term::Sort(Sort::Time0));
    let got = infer(&Context::empty(), &applied).unwrap();
    assert!(eq(
        &got,
        &pi(Term::Sort(Sort::Time0), Term::Sort(Sort::Time0))
    ));
}

#[test]
fn dependent_let_retains_its_type_after_substitution() {
    let body = Term::annot(lam(var(0), var(0)), pi(var(0), var(1)));
    let term = Term::Let {
        binder: Ident::new("A"),
        ty: Box::new(Term::type_sort(0)),
        val: Box::new(Term::Sort(Sort::Time0)),
        body: Box::new(body),
    };
    assert!(eq(
        &infer(&Context::empty(), &term).unwrap(),
        &pi(Term::Sort(Sort::Time0), Term::Sort(Sort::Time0))
    ));
}

#[test]
fn formed_match_type_reduces_through_public_check() {
    let ctx = crate::prelude::compliance_prelude().with_named_constant("p", Term::prop());
    check(
        &ctx,
        &Term::constant("p"),
        &bool_type(Term::constant("True")),
    )
    .unwrap();
    assert!(check(
        &ctx,
        &Term::constant("p"),
        &bool_type(Term::constant("False"))
    )
    .is_err());
}

#[test]
fn source_order_constructor_arguments_reach_public_conversion() {
    let ctx = crate::prelude::compliance_prelude()
        .with_named_constant(
            "Zero",
            pi(
                Term::type_sort(1),
                pi(Term::type_sort(1), Term::constant("Nat")),
            ),
        )
        .with_named_constant("p", Term::prop());
    let ctor = app(
        app(Term::constant("Zero"), Term::prop()),
        Term::type_sort(0),
    );
    let first = Term::match_expr(
        ctor.clone(),
        Term::type_sort(1),
        vec![branch("Zero", 2, var(1))],
    );
    let last = Term::match_expr(ctor, Term::type_sort(1), vec![branch("Zero", 2, var(0))]);
    check(&ctx, &Term::constant("p"), &first).unwrap();
    assert!(check(&ctx, &Term::constant("p"), &last).is_err());
}

#[test]
fn constructor_instantiation_protects_open_arguments_under_lambda() {
    let ctor = app(app(Term::constant("Zero"), var(0)), Term::prop());
    let term = Term::match_expr(
        ctor,
        Term::type_sort(1),
        vec![branch("Zero", 2, lam(Term::type_sort(0), var(2)))],
    );
    assert!(eq(&reduce(&term), &lam(Term::type_sort(0), var(1))));
}

#[test]
fn neutral_constructor_match_suspends_before_later_wildcard() {
    let term = Term::match_expr(
        var(0),
        Term::type_sort(1),
        vec![
            branch("True", 0, Term::prop()),
            Branch {
                pattern: Pattern::Wildcard,
                body: Term::type_sort(0),
            },
        ],
    );
    assert_eq!(reduce(&term), term);
    assert!(eq(&term, &term));
    assert!(!eq(&term, &Term::prop()));
    assert!(!eq(&term, &Term::type_sort(0)));
    assert!(eq(
        &subst(&term, 0, &Term::constant("True"), 0).unwrap(),
        &Term::prop()
    ));
}

#[test]
fn leading_wildcard_reduces_without_resolving_neutral() {
    let term = Term::match_expr(
        var(0),
        Term::type_sort(1),
        vec![Branch {
            pattern: Pattern::Wildcard,
            body: Term::prop(),
        }],
    );
    assert_eq!(reduce(&term), Term::prop());
}

#[test]
fn wrong_observed_constructor_advances_to_matching_branch() {
    assert!(eq(&bool_type(Term::constant("False")), &Term::type_sort(0)));
}

#[test]
fn malformed_constructor_telescope_is_rejected() {
    let ctx = crate::prelude::compliance_prelude()
        .with_named_constant("subject", Term::constant("Nat"))
        .with_named_constant(
            "Zero",
            pi(
                Term::annot(Term::type_sort(0), Term::IntLit(0)),
                Term::constant("Nat"),
            ),
        );
    let term = Term::match_expr(
        Term::constant("subject"),
        Term::constant("Nat"),
        vec![branch("Zero", 1, Term::constant("subject"))],
    );
    assert!(infer(&ctx, &term).is_err());
}

#[test]
fn nonempty_exception_list_is_reflexive_and_never_erased() {
    let term = rule(Some(var(0)));
    assert_eq!(reduce(&term), term);
    assert!(eq(&term, &term));
    assert!(!eq(&term, &Term::prop()));
    assert!(!eq(&term, &Term::type_sort(0)));
}

#[test]
fn changed_exception_guard_or_priority_changes_conversion() {
    let term = rule(Some(var(0)));
    assert!(!eq(&term, &rule(Some(var(1)))));
    let mut other = term.clone();
    if let Term::Defeasible(rule) = &mut other {
        rule.exceptions[0].priority = Some(11);
    }
    assert!(!eq(&term, &other));
}

#[test]
fn beta_substitution_reaches_exception_guard_and_preserves_metadata() {
    let term = app(lam(Term::prop(), rule(Some(var(0)))), Term::constant("p"));
    assert_eq!(reduce(&term), rule(Some(Term::constant("p"))));
}

#[test]
fn empty_defeasible_rule_reduces_through_public_check() {
    check(&Context::empty(), &Term::Sort(Sort::Time0), &rule(None)).unwrap();
}

#[test]
fn match_binder_substitution_distinguishes_bound_and_free_variables() {
    let term = Term::match_expr(var(0), var(1), vec![branch("Zero", 2, app(var(1), var(2)))]);
    let got = subst(&term, 0, &var(0), 0).unwrap();
    let expected = Term::match_expr(var(0), var(0), vec![branch("Zero", 2, app(var(1), var(2)))]);
    assert_eq!(got, expected);
    let shifted = shift(&term, 0, 1, 0).unwrap();
    let expected = Term::match_expr(var(1), var(2), vec![branch("Zero", 2, app(var(1), var(3)))]);
    assert_eq!(shifted, expected);
}

#[test]
fn time_sorts_have_reflexive_conversion_without_cross_identification() {
    assert!(eq(&Term::Sort(Sort::Time0), &Term::Sort(Sort::Time0)));
    assert!(eq(&Term::Sort(Sort::Time1), &Term::Sort(Sort::Time1)));
    assert!(!eq(&Term::Sort(Sort::Time0), &Term::Sort(Sort::Time1)));
}

#[test]
fn forward_global_declarations_validate_in_dependency_order() {
    let ctx = Context::empty()
        .with_named_constant("a", Term::constant("A"))
        .with_named_constant("A", Term::type_sort(0));
    validate_context(&ctx).unwrap();
    check(&ctx, &Term::constant("a"), &Term::constant("A")).unwrap();
}

#[test]
fn dependent_global_function_type_retains_useful_application() {
    let ctx = Context::empty()
        .with_named_constant("id", pi(Term::type_sort(0), pi(var(0), var(1))))
        .with_named_constant("t", Term::Sort(Sort::Time0));
    let term = app(
        app(Term::constant("id"), Term::Sort(Sort::Time0)),
        Term::constant("t"),
    );
    assert!(eq(&infer(&ctx, &term).unwrap(), &Term::Sort(Sort::Time0)));
}

#[test]
fn declaration_replacement_does_not_reuse_stale_formation() {
    let ctx = Context::empty()
        .with_named_constant("A", Term::type_sort(0))
        .with_named_constant("a", Term::constant("A"));
    validate_context(&ctx).unwrap();
    let changed = ctx.with_named_constant("A", Term::annot(Term::type_sort(0), Term::IntLit(0)));
    assert!(check(&changed, &Term::constant("a"), &Term::constant("A")).is_err());
}

#[test]
fn global_declaration_cannot_capture_a_local_binding() {
    let ctx = Context::empty()
        .extend(Term::type_sort(0))
        .with_named_constant("a", var(0));
    assert!(validate_context(&ctx).is_err());
}

#[test]
fn cyclic_declaration_types_have_no_finite_formation_order() {
    let ctx = Context::empty()
        .with_named_constant("A", Term::constant("B"))
        .with_named_constant("B", Term::constant("A"));
    assert!(matches!(
        validate_context(&ctx),
        Err(TypeError::CyclicGlobalSignature { .. })
    ));
}

#[test]
fn unused_declaration_levels_are_bounded_before_validation_or_error_cloning() {
    fn dispose_level_term(term: Term) {
        let Term::Sort(Sort::Type(level)) = term else {
            panic!("level test fixture must remain a type sort");
        };
        // The test isolates checker recursion from the AST's recursive destructor.
        let mut remaining = vec![level];
        while let Some(level) = remaining.pop() {
            match level {
                Level::Succ(base, _) => remaining.push(*base),
                Level::Max(left, right) => {
                    remaining.push(*left);
                    remaining.push(*right);
                }
                _ => {}
            }
        }
    }

    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            for local in [false, true] {
                for unresolved_left in [false, true] {
                    let mut level = Level::Nat(0);
                    for _ in 0..16_384 {
                        level = Level::Succ(Box::new(level), 1);
                    }
                    if unresolved_left {
                        level = Level::Max(
                            Box::new(Level::Var(crate::ast::LevelVar { index: 0 })),
                            Box::new(level),
                        );
                    }
                    let term = Term::Sort(Sort::Type(level));
                    let mut ctx = if local {
                        Context::empty().extend(term)
                    } else {
                        Context::empty().with_named_constant("unused", term)
                    };
                    assert_eq!(
                        infer(&ctx, &Term::prop()),
                        Err(TypeError::RecursionLimitExceeded)
                    );
                    assert_eq!(
                        check(&ctx, &Term::prop(), &Term::type_sort(1)),
                        Err(TypeError::RecursionLimitExceeded),
                    );
                    let term = if local {
                        ctx.entries.pop().unwrap()
                    } else {
                        ctx.globals.remove(&QualIdent::simple("unused")).unwrap()
                    };
                    assert_eq!(
                        check_admissibility_mode(&term, AdmissibilityMode::HoleExtension),
                        Err(TypeError::RecursionLimitExceeded),
                    );
                    dispose_level_term(term);
                }
            }
        })
        .unwrap()
        .join()
        .expect("level validation must preserve the caller stack");
}

#[test]
fn unsupported_declaration_payloads_are_bounded_before_diagnostic_cloning() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            for local in [false, true] {
                for recursive_term in [false, true] {
                    let term = if recursive_term {
                        let mut ty = Term::type_sort(0);
                        for _ in 0..16_384 {
                            ty = Term::annot(ty, Term::type_sort(1));
                        }
                        Term::Rec {
                            binder: Ident::new("f"),
                            ty: Box::new(ty),
                            body: Box::new(Term::prop()),
                        }
                    } else {
                        let mut row = EffectRow::Empty;
                        for _ in 0..16_384 {
                            row = EffectRow::BranchSensitive(Box::new(row));
                        }
                        Term::Pi {
                            binder: Ident::new("x"),
                            domain: Box::new(Term::type_sort(0)),
                            effect_row: Some(row),
                            codomain: Box::new(Term::type_sort(0)),
                        }
                    };
                    let mut ctx = if local {
                        Context::empty().extend(term)
                    } else {
                        Context::empty().with_named_constant("unused", term)
                    };
                    assert_eq!(
                        infer(&ctx, &Term::prop()),
                        Err(TypeError::RecursionLimitExceeded)
                    );
                    let term = if local {
                        ctx.entries.pop().unwrap()
                    } else {
                        ctx.globals.remove(&QualIdent::simple("unused")).unwrap()
                    };
                    // Destruction is separate from the checker boundary under test.
                    match term {
                        Term::Rec { ty, .. } => {
                            let mut term = *ty;
                            while let Term::Annot { term: inner, .. } = term {
                                term = *inner;
                            }
                        }
                        Term::Pi {
                            effect_row: Some(row),
                            ..
                        } => {
                            let mut row = row;
                            while let EffectRow::BranchSensitive(inner) = row {
                                row = *inner;
                            }
                        }
                        _ => unreachable!("unsupported declaration test fixture"),
                    }
                }
            }

            let term = Term::Rec {
                binder: Ident::new("f"),
                ty: Box::new(Term::type_sort(0)),
                body: Box::new(Term::prop()),
            };
            let ctx = Context::empty().with_named_constant("unused", term.clone());
            assert_eq!(
                infer(&ctx, &Term::prop()),
                Err(TypeError::Admissibility {
                    violation: AdmissibilityViolation::RecNotSupported,
                    term,
                })
            );
        })
        .unwrap()
        .join()
        .expect("rejected declaration payloads must preserve the caller stack");
}
