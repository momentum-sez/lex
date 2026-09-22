use lex_core::ast::{Branch, Constructor, Ident, Pattern, QualIdent, Term};
use lex_core::prelude::{structural_prelude, PreludeRegistry};
use lex_core::typecheck::{check, check_admissibility, infer, validate_context, Context};

fn c(name: &str) -> Term {
    Term::constant(name)
}
fn v(index: u32) -> Term {
    Term::var("x", index)
}
fn app(f: Term, x: Term) -> Term {
    Term::app(f, x)
}
fn pi(a: Term, b: Term) -> Term {
    Term::pi("x", a, b)
}
fn arm(name: &str, count: usize, body: Term) -> Branch {
    Branch {
        pattern: Pattern::Constructor {
            constructor: Constructor::new(QualIdent::simple(name)),
            binders: (0..count).map(|i| Ident::new(&format!("x{i}"))).collect(),
        },
        body,
    }
}
fn otherwise(body: Term) -> Branch {
    Branch {
        pattern: Pattern::Wildcard,
        body,
    }
}
fn ctx() -> Context {
    structural_prelude()
        .with_named_constant("input", c("IncorporationContext"))
        .with_named_constant("tag", c("ComplianceTag"))
        .with_named_constant("nat", c("Nat"))
        .with_named_constant("boolean", c("Bool"))
}
fn mt(scrutinee: Term, branches: Vec<Branch>) -> Term {
    Term::match_expr(scrutinee, c("Bool"), branches)
}

#[test]
fn branch_family_follows_the_inferred_scrutinee() {
    let t = mt(
        c("boolean"),
        vec![arm("Zero", 0, c("True")), otherwise(c("False"))],
    );
    assert!(infer(&ctx(), &t).is_err());
}
#[test]
fn unused_constructor_signature_must_end_in_its_registered_family() {
    let context = ctx().with_named_constant("Some", pi(c("Bool"), c("Nat")));
    assert!(infer(&context, &c("True")).is_err());
}
#[test]
fn pattern_consumes_the_complete_payload_telescope() {
    let context = ctx().with_named_constant("Zero", pi(c("Bool"), pi(c("Bool"), c("Nat"))));
    for count in [0, 1, 3] {
        let t = mt(
            c("nat"),
            vec![arm("Zero", count, c("True")), otherwise(c("False"))],
        );
        assert!(infer(&context, &t).is_err(), "arity {count}");
    }
}
#[test]
fn nullary_patterns_require_the_declared_primary_signature() {
    let context = ctx().with_named_constant("Zero", c("Bool"));
    assert!(validate_context(&context).is_err());
    let missing = mt(
        c("tag"),
        vec![arm("ADGM", 0, c("True")), otherwise(c("False"))],
    );
    assert!(infer(&ctx(), &missing).is_err());
}
#[test]
fn empty_match_cannot_establish_coverage() {
    assert!(infer(&ctx(), &mt(c("boolean"), vec![])).is_err());
    assert!(check_admissibility(&mt(Term::type_sort(0), vec![])).is_err());
}
#[test]
fn natural_family_remains_open_with_a_useful_wildcard() {
    let incomplete = mt(c("nat"), vec![arm("Zero", 0, c("True"))]);
    assert!(infer(&ctx(), &incomplete).is_err());
    let complete = mt(
        c("nat"),
        vec![arm("Zero", 0, c("True")), otherwise(c("False"))],
    );
    assert_eq!(infer(&ctx(), &complete).unwrap(), c("Bool"));
}

#[test]
fn standalone_admission_retains_coverage_for_unknown_tags() {
    use lex_core::typecheck::{check_admissibility_mode, AdmissibilityMode};

    let incomplete = mt(c("tag"), vec![arm("Active", 0, c("True"))]);
    assert!(check_admissibility(&incomplete).is_err());
    assert!(check_admissibility_mode(&incomplete, AdmissibilityMode::HoleExtension).is_err());

    let complete = mt(
        c("tag"),
        vec![arm("Active", 0, c("True")), otherwise(c("False"))],
    );
    assert!(check_admissibility(&complete).is_ok());
    assert!(check_admissibility_mode(&complete, AdmissibilityMode::HoleExtension).is_ok());
}
#[test]
fn structural_some_and_cons_bind_their_real_payload_types_in_order() {
    let some = Term::match_expr(
        app(c("Some"), c("input")),
        c("IncorporationContext"),
        vec![arm("Some", 1, v(0))],
    );
    let cons = app(app(c("Cons"), c("input")), c("Nil"));
    let head = Term::match_expr(
        cons.clone(),
        c("IncorporationContext"),
        vec![arm("Cons", 2, v(1))],
    );
    let tail = Term::match_expr(cons, c("ComplianceTag"), vec![arm("Cons", 2, v(0))]);
    assert_eq!(infer(&ctx(), &some).unwrap(), c("IncorporationContext"));
    assert_eq!(infer(&ctx(), &head).unwrap(), c("IncorporationContext"));
    assert_eq!(infer(&ctx(), &tail).unwrap(), c("ComplianceTag"));
    let wrong = Term::match_expr(
        app(c("Some"), c("input")),
        c("Bool"),
        vec![arm("Some", 1, v(0))],
    );
    assert!(infer(&ctx(), &wrong).is_err());
}
#[test]
fn structural_nullary_values_are_registered() {
    for name in ["None", "Nil"] {
        assert_eq!(
            PreludeRegistry::constructor_datatype(name),
            Some("ComplianceTag")
        );
        assert_eq!(
            infer(&ctx(), &mt(c(name), vec![arm(name, 0, c("True"))])).unwrap(),
            c("Bool")
        );
    }
}
#[test]
fn partial_application_is_a_function_not_a_data_scrutinee() {
    let t = mt(
        c("Some"),
        vec![arm("Some", 1, c("True")), otherwise(c("False"))],
    );
    assert!(infer(&ctx(), &t).is_err());
}
#[test]
fn pending_secondary_pattern_has_no_global_or_payload_coercion() {
    let t = mt(
        c("tag"),
        vec![arm("Pending", 0, c("True")), otherwise(c("False"))],
    );
    assert_eq!(infer(&ctx(), &t).unwrap(), c("Bool"));
    assert!(check(&ctx(), &c("Pending"), &c("ComplianceTag")).is_err());
    let context = ctx().with_named_constant("Pending", pi(c("Bool"), c("ComplianceVerdict")));
    let payload = mt(
        c("tag"),
        vec![arm("Pending", 1, c("True")), otherwise(c("False"))],
    );
    assert!(infer(&context, &payload).is_err());
}
#[test]
fn dependent_telescope_preserves_explicit_type_and_value_arguments() {
    let context = ctx()
        .with_named_constant("Zero", pi(Term::type_sort(0), pi(v(0), c("Nat"))))
        .with_named_constant("use", pi(Term::type_sort(0), pi(v(0), c("Bool"))));
    let t = mt(
        c("nat"),
        vec![
            arm("Zero", 2, app(app(c("use"), v(1)), v(0))),
            otherwise(c("False")),
        ],
    );
    assert_eq!(infer(&context, &t).unwrap(), c("Bool"));
}
#[test]
fn unknown_boolean_still_requires_both_constructors() {
    assert!(infer(&ctx(), &mt(c("boolean"), vec![arm("True", 0, c("True"))])).is_err());
    let t = mt(
        c("boolean"),
        vec![arm("True", 0, c("False")), arm("False", 0, c("True"))],
    );
    assert_eq!(infer(&ctx(), &t).unwrap(), c("Bool"));
}
#[test]
fn specialized_coverage_observes_let_annotation_beta_and_nested_match() {
    let beta = app(
        Term::annot(Term::lam("x", c("Bool"), v(0)), pi(c("Bool"), c("Bool"))),
        c("True"),
    );
    let terms = [
        c("True"),
        Term::let_in("x", c("Bool"), c("True"), v(0)),
        Term::annot(c("True"), c("Bool")),
        beta,
        mt(c("False"), vec![arm("False", 0, c("True"))]),
    ];
    for scrutinee in terms {
        let t = mt(scrutinee, vec![arm("True", 0, c("True"))]);
        assert_eq!(infer(&ctx(), &t).unwrap(), c("Bool"));
        // Syntax-only entrypoints do not interpret unresolved variable indices.
        // Typed inference checks original terms before reducing their coverage.
    }
}
#[test]
fn specialized_coverage_does_not_skip_malformed_scrutinee_types() {
    let t = mt(
        Term::annot(c("True"), c("Nat")),
        vec![arm("True", 0, c("True"))],
    );
    assert!(infer(&ctx(), &t).is_err());
}
#[test]
fn nullary_pattern_dependencies_are_checked_before_global_types() {
    let motive = Term::match_expr(
        c("True"),
        Term::type_sort(1),
        vec![
            arm("True", 0, Term::prop()),
            arm("False", 0, Term::type_sort(0)),
        ],
    );
    let context = ctx().with_named_constant("A", motive);
    assert!(check(&context, &c("A"), &Term::prop()).is_ok());
}
#[test]
fn numeric_patterns_accept_only_canonical_positive_u64() {
    for name in [
        "__NonZeroNat:0",
        "__NonZeroNat:03",
        "__NonZeroNat:+3",
        "__NonZeroNat:18446744073709551616",
    ] {
        let t = mt(
            c("nat"),
            vec![arm(name, 0, c("True")), otherwise(c("False"))],
        );
        assert!(infer(&ctx(), &t).is_err(), "invalid marker {name}");
    }
    for name in ["__NonZeroNat:3", "__NonZeroNat:18446744073709551615"] {
        let t = mt(
            c("nat"),
            vec![arm(name, 0, c("True")), otherwise(c("False"))],
        );
        assert_eq!(infer(&ctx(), &t).unwrap(), c("Bool"));
    }
}
#[test]
fn numeric_declaration_order_cannot_create_a_payload_bearing_value() {
    let marker = "__NonZeroNat:3";
    let motive = Term::match_expr(
        c("nat"),
        Term::type_sort(1),
        vec![arm(marker, 0, Term::prop()), otherwise(Term::type_sort(0))],
    );
    for name in ["A", "zz"] {
        let context = ctx()
            .with_named_constant(marker, pi(c("Bool"), c("Nat")))
            .with_named_constant(name, motive.clone());
        assert!(validate_context(&context).is_err(), "declaration {name}");
    }
    assert!(validate_context(&ctx().with_named_constant(marker, c("Nat"))).is_ok());
}
#[test]
fn wildcard_only_match_retains_non_datatype_use() {
    assert_eq!(
        infer(&ctx(), &mt(Term::type_sort(0), vec![otherwise(c("True"))])).unwrap(),
        c("Bool")
    );
}

#[test]
fn raw_named_coverage_stays_conservative_until_elaboration() {
    use lex_core::{elaborate, lexer, parser};
    for source in [
        "match (let x : Bool := True in x) return Bool with | True => True end",
        "match ((lambda (x : Bool). lambda (y : Bool). x) True False) return Bool with | True => True end",
    ] {
        let surface = parser::parse(&lexer::lex(source).unwrap()).unwrap();
        assert!(check_admissibility(&surface).is_err());
        let core = elaborate::elaborate(&surface, &ctx()).unwrap();
        // The lambda source has no explicit type annotation, so check it below
        // through a Let whose value is checked against its complete Pi type.
        if source.contains("let x") {
            assert_eq!(infer(&ctx(), &core).unwrap(), c("Bool"));
        }
    }
    let source = "match (let f : Bool -> Bool -> Bool := lambda (x : Bool). lambda (y : Bool). x in f True False) return Bool with | True => True end";
    let surface = parser::parse(&lexer::lex(source).unwrap()).unwrap();
    assert!(check_admissibility(&surface).is_err());
    let core = elaborate::elaborate(&surface, &ctx()).unwrap();
    assert_eq!(infer(&ctx(), &core).unwrap(), c("Bool"));
}

#[test]
fn nested_open_constructor_reduction_preserves_all_branch_checks() {
    let inner = Term::match_expr(
        c("True"),
        c("ComplianceTag"),
        vec![arm("True", 0, app(c("Some"), c("input")))],
    );
    let t = Term::match_expr(
        inner.clone(),
        c("IncorporationContext"),
        vec![arm("Some", 1, v(0))],
    );
    assert_eq!(infer(&ctx(), &t).unwrap(), c("IncorporationContext"));
    let bad = Term::match_expr(
        inner,
        c("IncorporationContext"),
        vec![arm("Some", 1, v(0)), arm("None", 0, c("True"))],
    );
    assert!(infer(&ctx(), &bad).is_err());
}

#[test]
fn dependent_payloads_preserve_an_existing_local_context_and_motive() {
    let context = ctx()
        .with_named_constant("Zero", pi(Term::type_sort(0), pi(v(0), c("Nat"))))
        .with_named_constant("use", pi(Term::type_sort(0), pi(v(0), c("Bool"))))
        .extend(Term::type_sort(0))
        .extend(v(0));
    // The outer value has type A. Each arm must retain that type after its
    // explicit constructor type and value binders extend the local context.
    let t = Term::match_expr(c("nat"), v(1), vec![arm("Zero", 2, v(2)), otherwise(v(0))]);
    assert_eq!(infer(&context, &t).unwrap(), v(1));
}

#[test]
fn enumerating_named_tags_does_not_close_the_open_family() {
    let context =
        lex_core::prelude::compliance_prelude().with_named_constant("tag", c("ComplianceTag"));
    let branches = PreludeRegistry::lookup_variant_constructors("ComplianceTag")
        .unwrap()
        .into_iter()
        .map(|name| {
            arm(
                name,
                match name {
                    "Some" => 1,
                    "Cons" => 2,
                    _ => 0,
                },
                c("True"),
            )
        })
        .collect();
    assert!(infer(&context, &mt(c("tag"), branches)).is_err());
}
