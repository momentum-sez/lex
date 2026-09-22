use lex_core::ast::{Branch, Constructor, Ident, Pattern, QualIdent, Term};
use lex_core::certificate::ComplianceVerdict;
use lex_core::evaluate::{evaluate, EvalError, RuntimeContext};

fn c(name: &str) -> Term {
    Term::Constant(QualIdent::simple(name))
}
fn v(index: u32) -> Term {
    Term::Var {
        name: Ident::new("hint"),
        index,
    }
}
fn branch(name: &str, arity: usize, body: Term) -> Branch {
    Branch {
        pattern: Pattern::Constructor {
            constructor: Constructor::new(QualIdent::simple(name)),
            binders: (0..arity).map(|_| Ident::new("payload")).collect(),
        },
        body,
    }
}
fn matched(scrutinee: Term, branches: Vec<Branch>) -> Term {
    Term::match_expr(scrutinee, c("ComplianceVerdict"), branches)
}
fn verdict(term: &Term) -> Result<ComplianceVerdict, EvalError> {
    evaluate(term, &RuntimeContext::new())
}

#[test]
fn some_payload_reaches_the_verdict() {
    let term = matched(
        Term::app(c("Some"), c("Compliant")),
        vec![branch("Some", 1, v(0))],
    );
    assert_eq!(verdict(&term), Ok(ComplianceVerdict::Compliant));
}

#[test]
fn constructor_payloads_keep_source_order() {
    let value = Term::app(Term::app(c("Cons"), c("Compliant")), c("NonCompliant"));
    for (index, expected) in [
        (1, ComplianceVerdict::Compliant),
        (0, ComplianceVerdict::NonCompliant),
    ] {
        assert_eq!(
            verdict(&matched(value.clone(), vec![branch("Cons", 2, v(index))])),
            Ok(expected)
        );
    }
}

#[test]
fn nested_match_payload_is_instantiated_below_its_own_binders() {
    let body = matched(
        Term::app(c("Some"), c("NonCompliant")),
        vec![branch("Some", 1, v(1))],
    );
    assert_eq!(
        verdict(&matched(
            Term::app(c("Some"), c("Compliant")),
            vec![branch("Some", 1, body)]
        )),
        Ok(ComplianceVerdict::Compliant)
    );
}

#[test]
fn open_payload_is_not_captured_by_later_beta_argument() {
    let body = Term::app(
        Term::lam("local", c("ComplianceVerdict"), v(1)),
        c("Compliant"),
    );
    let term = matched(Term::app(c("Some"), v(0)), vec![branch("Some", 1, body)]);
    assert!(matches!(verdict(&term), Err(EvalError::NotAVerdict { term }) if *term == v(0)));
}

#[test]
fn beta_reduction_exposes_the_constructor_and_substitutes_its_payload() {
    let value = Term::app(
        Term::lam("x", c("ComplianceVerdict"), Term::app(c("Some"), v(0))),
        c("Compliant"),
    );
    assert_eq!(
        verdict(&matched(value, vec![branch("Some", 1, v(0))])),
        Ok(ComplianceVerdict::Compliant)
    );
}

#[test]
fn let_reduction_exposes_the_constructor_and_substitutes_its_payload() {
    let value = Term::Let {
        binder: Ident::new("x"),
        ty: Box::new(c("ComplianceVerdict")),
        val: Box::new(c("Compliant")),
        body: Box::new(Term::app(c("Some"), v(0))),
    };
    assert_eq!(
        verdict(&matched(value, vec![branch("Some", 1, v(0))])),
        Ok(ComplianceVerdict::Compliant)
    );
}

#[test]
fn exact_payload_arity_is_required_before_selecting_an_arm() {
    let value = Term::app(c("Some"), c("Compliant"));
    for arity in [0, 2] {
        assert!(matches!(
            verdict(&matched(
                value.clone(),
                vec![branch("Some", arity, c("Compliant"))]
            )),
            Err(EvalError::NoMatchingBranch { .. })
        ));
    }
}

#[test]
fn beta_reduction_uses_indices_when_binder_names_repeat() {
    let term = Term::app(
        Term::app(
            Term::lam(
                "x",
                c("ComplianceVerdict"),
                Term::lam("x", c("ComplianceVerdict"), v(1)),
            ),
            c("Compliant"),
        ),
        c("NonCompliant"),
    );
    assert_eq!(verdict(&term), Ok(ComplianceVerdict::Compliant));
}

#[test]
fn an_unknown_scrutinee_cannot_skip_a_constructor_for_a_later_wildcard() {
    let term = matched(
        v(0),
        vec![
            branch("Some", 1, c("NonCompliant")),
            Branch {
                pattern: Pattern::Wildcard,
                body: c("Compliant"),
            },
        ],
    );
    assert!(matches!(verdict(&term), Err(EvalError::NotAVerdict { .. })));
}

#[test]
fn beta_divergence_obeys_the_existing_evaluation_limits() {
    let omega = Term::lam("x", c("ComplianceVerdict"), Term::app(v(0), v(0)));
    assert!(matches!(
        verdict(&Term::app(omega.clone(), omega)),
        Err(EvalError::RecursionLimitExceeded | EvalError::ReductionLimitExceeded)
    ));
}

#[test]
fn constructor_names_cannot_be_replaced_by_runtime_accessor_entries() {
    let term = matched(
        Term::app(c("Some"), c("Compliant")),
        vec![branch("Some", 1, v(0))],
    );
    let mut ctx = RuntimeContext::new();
    ctx.insert(
        "Some",
        lex_core::evaluate::RuntimeValue::Tag("NonCompliant".into()),
    );
    assert_eq!(evaluate(&term, &ctx), Ok(ComplianceVerdict::Compliant));
}

#[test]
fn qualified_names_do_not_alias_unqualified_constructors_or_verdicts() {
    let qualified = Term::Constant(QualIdent::from_dotted("other.True"));
    assert!(matches!(
        verdict(&matched(qualified, vec![branch("True", 0, c("Compliant"))])),
        Err(EvalError::NotAVerdict { .. })
    ));
    assert!(matches!(
        verdict(&Term::Constant(QualIdent::from_dotted("other.Compliant"))),
        Err(EvalError::NotAVerdict { .. })
    ));
}

#[test]
fn annotated_and_nested_match_values_expose_constructor_payloads() {
    let value = Term::Annot {
        term: Box::new(matched(
            c("True"),
            vec![branch("True", 0, Term::app(c("Some"), c("Compliant")))],
        )),
        ty: Box::new(c("ComplianceTag")),
    };
    assert_eq!(
        verdict(&matched(value, vec![branch("Some", 1, v(0))])),
        Ok(ComplianceVerdict::Compliant)
    );
}

#[test]
fn wildcard_does_not_hide_missing_accessor_evidence() {
    let term = matched(
        Term::app(c("missing"), v(0)),
        vec![Branch {
            pattern: Pattern::Wildcard,
            body: c("Compliant"),
        }],
    );
    assert_eq!(
        verdict(&term),
        Err(EvalError::UnknownAccessor {
            name: "missing".into()
        })
    );
}

#[test]
fn payloads_evaluate_through_the_parsed_and_typed_rule_path() {
    let source = "λ(ctx : IncorporationContext). match Cons ctx Nil return ComplianceVerdict with | Cons head tail => match tail return ComplianceVerdict with | Nil => Compliant | _ => NonCompliant";
    let tokens = lex_core::lexer::lex(source).unwrap();
    let surface = lex_core::parser::parse(&tokens).unwrap();
    let context = lex_core::prelude::structural_prelude();
    let core = lex_core::elaborate::elaborate(&surface, &context).unwrap();
    let expected = Term::pi("ctx", c("IncorporationContext"), c("ComplianceVerdict"));
    lex_core::typecheck::check(&context, &core, &expected).unwrap();
    assert_eq!(verdict(&core), Ok(ComplianceVerdict::Compliant));
}

#[test]
fn rule_lambda_still_opens_after_annotation_or_let_reduction() {
    let rule = Term::lam("ctx", c("IncorporationContext"), c("Compliant"));
    let annotated = Term::Annot {
        term: Box::new(rule.clone()),
        ty: Box::new(Term::pi(
            "ctx",
            c("IncorporationContext"),
            c("ComplianceVerdict"),
        )),
    };
    let bound = Term::Let {
        binder: Ident::new("rule"),
        ty: Box::new(Term::pi(
            "ctx",
            c("IncorporationContext"),
            c("ComplianceVerdict"),
        )),
        val: Box::new(rule),
        body: Box::new(v(0)),
    };
    assert_eq!(verdict(&annotated), Ok(ComplianceVerdict::Compliant));
    assert_eq!(verdict(&bound), Ok(ComplianceVerdict::Compliant));
}

#[test]
fn opaque_global_cannot_skip_an_earlier_constructor_arm() {
    let term = matched(
        c("unknown_bool"),
        vec![
            branch("True", 0, c("NonCompliant")),
            Branch {
                pattern: Pattern::Wildcard,
                body: c("Compliant"),
            },
        ],
    );
    assert!(matches!(verdict(&term), Err(EvalError::NotAVerdict { .. })));
}

#[test]
fn concrete_runtime_tags_can_use_open_family_wildcards() {
    let term = matched(
        Term::app(c("status"), v(0)),
        vec![
            branch("Active", 0, c("NonCompliant")),
            Branch {
                pattern: Pattern::Wildcard,
                body: c("Compliant"),
            },
        ],
    );
    let mut ctx = RuntimeContext::new();
    ctx.insert(
        "status",
        lex_core::evaluate::RuntimeValue::Tag("NovelStatus".into()),
    );
    assert_eq!(evaluate(&term, &ctx), Ok(ComplianceVerdict::Compliant));
}

#[test]
fn deep_lambda_argument_is_rejected_before_a_recursive_clone() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let mut deep = c("Compliant");
            for _ in 0..10_000 {
                deep = Term::lam("x", c("ComplianceVerdict"), deep);
            }
            let term = Term::app(deep, c("Compliant"));
            let result = verdict(&term);
            // Iterative disposal keeps this test about evaluation, not recursive AST Drop.
            let mut pending = vec![term];
            while let Some(term) = pending.pop() {
                match term {
                    Term::Lambda { domain, body, .. } => {
                        pending.push(*domain);
                        pending.push(*body);
                    }
                    Term::App { func, arg } => {
                        pending.push(*func);
                        pending.push(*arg);
                    }
                    _ => {}
                }
            }
            assert_eq!(result, Err(EvalError::RecursionLimitExceeded));
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn partial_or_overapplied_constructors_cannot_reach_a_wildcard_verdict() {
    let values = [
        c("Some"),
        Term::app(c("Cons"), c("Compliant")),
        Term::app(c("True"), c("Compliant")),
        Term::app(Term::app(c("Some"), c("Compliant")), c("NonCompliant")),
    ];
    for value in values {
        let term = matched(
            value,
            vec![Branch {
                pattern: Pattern::Wildcard,
                body: c("Compliant"),
            }],
        );
        assert!(matches!(verdict(&term), Err(EvalError::NotAVerdict { .. })));
    }
}

#[test]
fn runtime_nullary_tags_cannot_supply_a_payload_constructor() {
    let term = matched(
        Term::app(c("status"), v(0)),
        vec![Branch {
            pattern: Pattern::Wildcard,
            body: c("Compliant"),
        }],
    );
    let mut ctx = RuntimeContext::new();
    ctx.insert(
        "status",
        lex_core::evaluate::RuntimeValue::Tag("Some".into()),
    );
    assert!(matches!(
        evaluate(&term, &ctx),
        Err(EvalError::NotAVerdict { .. })
    ));
}

#[test]
fn an_overflowing_open_payload_is_rejected_without_index_aliasing() {
    let body = Term::lam("inner", c("ComplianceVerdict"), v(1));
    let terms = [
        matched(
            Term::app(c("Some"), v(u32::MAX)),
            vec![branch("Some", 1, body)],
        ),
        matched(
            Term::app(Term::app(c("Cons"), c("Compliant")), v(u32::MAX)),
            vec![branch("Cons", 2, v(0))],
        ),
    ];
    for term in terms {
        assert!(
            matches!(verdict(&term), Err(EvalError::Substitution { error }) if matches!(*error, lex_core::typecheck::TypeError::SubstitutionIndexOverflow { .. }))
        );
    }
}

#[test]
fn returned_tags_cannot_be_called_as_accessors_or_completed_as_constructors() {
    let mut ctx = RuntimeContext::new();
    ctx.insert(
        "status",
        lex_core::evaluate::RuntimeValue::Tag("NovelStatus".into()),
    );
    ctx.insert(
        "NovelStatus",
        lex_core::evaluate::RuntimeValue::Tag("Compliant".into()),
    );
    let extra_call = Term::app(Term::app(c("status"), v(0)), v(0));
    assert!(matches!(
        evaluate(&extra_call, &ctx),
        Err(EvalError::NotAVerdict { .. })
    ));
    ctx.insert(
        "status",
        lex_core::evaluate::RuntimeValue::Tag("Some".into()),
    );
    let forged_constructor = Term::app(Term::app(c("status"), v(0)), c("Compliant"));
    let term = matched(forged_constructor, vec![branch("Some", 1, v(0))]);
    assert!(matches!(
        evaluate(&term, &ctx),
        Err(EvalError::NotAVerdict { .. })
    ));
}

#[test]
fn unsupported_scrutinees_cannot_reach_a_wildcard_verdict() {
    let values = [
        Term::Hole(lex_core::ast::Hole {
            name: None,
            ty: Box::new(c("ComplianceVerdict")),
            authority: lex_core::ast::AuthorityRef::Named(QualIdent::simple("authority")),
            scope: None,
        }),
        Term::Rec {
            binder: Ident::new("x"),
            ty: Box::new(c("ComplianceVerdict")),
            body: Box::new(c("Compliant")),
        },
        Term::Pair {
            fst: Box::new(c("Compliant")),
            snd: Box::new(c("Compliant")),
        },
    ];
    for value in values {
        let term = matched(
            value,
            vec![Branch {
                pattern: Pattern::Wildcard,
                body: c("Compliant"),
            }],
        );
        assert!(matches!(verdict(&term), Err(EvalError::NotAVerdict { .. })));
    }
}
