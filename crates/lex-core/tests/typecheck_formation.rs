use lex_core::ast::{Ident, Sort, Term};
use lex_core::typecheck::{check, check_admissible, infer, Context};

fn bad() -> Term {
    Term::annot(Term::type_sort(1), Term::IntLit(0))
}
fn v(i: u32) -> Term {
    Term::var("v", i)
}
fn pi(a: Term, b: Term) -> Term {
    Term::pi("x", a, b)
}
fn lam(a: Term, b: Term) -> Term {
    Term::lam("x", a, b)
}

#[test]
fn direct_malformed_target_rejected_by_both_public_checkers() {
    let c = Context::empty();
    assert!(check(&c, &Term::prop(), &bad()).is_err());
    assert!(check_admissible(&c, &Term::prop(), &bad()).is_err());
}

#[test]
fn outer_annotation_does_not_hide_bad_inner_kind() {
    let expected = Term::annot(bad(), Term::type_sort(2));
    assert!(check(&Context::empty(), &Term::prop(), &expected).is_err());
}

#[test]
fn public_local_context_cannot_supply_malformed_source_type() {
    let c = Context::empty().extend(bad());
    let got = check(&c, &v(0), &Term::type_sort(1));
    assert!(
        got.is_err(),
        "malformed local declaration accepted: {got:?}"
    );
}

#[test]
fn public_global_signature_cannot_supply_malformed_source_type() {
    let c = Context::empty().with_named_constant("x", bad());
    let got = check_admissible(&c, &Term::constant("x"), &Term::type_sort(1));
    assert!(
        got.is_err(),
        "malformed global declaration accepted: {got:?}"
    );
}

#[test]
fn public_global_signature_cannot_make_malformed_kind_look_formed() {
    let c = Context::empty()
        .with_named_constant("A", bad())
        .with_named_constant("a", Term::constant("A"));
    let got = check(&c, &Term::constant("a"), &Term::constant("A"));
    assert!(
        got.is_err(),
        "malformed expected-type declaration accepted: {got:?}"
    );
}

#[test]
fn public_infer_cannot_return_an_unformed_type_from_local_context() {
    let got = infer(&Context::empty().extend(bad()), &v(0));
    assert!(
        got.is_err(),
        "public inference returned malformed type: {got:?}"
    );
}

#[test]
fn dependent_two_type_application_preserves_outer_binder() {
    // forall A B : Type_0, A -> B -> A.
    let body = lam(
        Term::type_sort(0),
        lam(Term::type_sort(0), lam(v(1), lam(v(1), v(1)))),
    );
    let ty = pi(
        Term::type_sort(0),
        pi(Term::type_sort(0), pi(v(1), pi(v(1), v(3)))),
    );
    let a = Term::Sort(Sort::Time0);
    let b = Term::Sort(Sort::Time1);
    let applied = Term::app(Term::app(Term::annot(body, ty), a.clone()), b.clone());
    check(&Context::empty(), &applied, &pi(a.clone(), pi(b, a))).unwrap();
}

#[test]
fn dependent_let_under_an_existing_binder_preserves_outer_variable() {
    // A : Type_0; let B : Type_0 = A in (lambda x:B. x).
    let c = Context::empty().extend(Term::type_sort(0));
    let t = Term::Let {
        binder: Ident::new("B"),
        ty: Box::new(Term::type_sort(0)),
        val: Box::new(v(0)),
        body: Box::new(Term::annot(lam(v(0), v(0)), pi(v(0), v(1)))),
    };
    check(&c, &t, &pi(v(0), v(1))).unwrap();
}

#[test]
fn production_signature_and_pack_local_accessor_support_exact_count_patterns() {
    use lex_core::{elaborate, lexer, parser, prelude};

    let ctx = prelude::production_prelude().with_named_constant(
        "director_count",
        pi(
            Term::constant("IncorporationContext"),
            Term::constant("Nat"),
        ),
    );
    let tokens = lexer::lex(
        "lambda (ctx : IncorporationContext).
         match director_count ctx return ComplianceVerdict with
         | 0 => NonCompliant
         | 1 => NonCompliant
         | 2 => NonCompliant
         | _ => Compliant end",
    )
    .unwrap();
    let surface = parser::parse(&tokens).unwrap();
    let core = elaborate::elaborate(&surface, &ctx).unwrap();
    let expected = pi(
        Term::constant("IncorporationContext"),
        Term::constant("ComplianceVerdict"),
    );
    // Positive-count patterns have no global declaration. They must remain usable.
    assert!(!ctx.contains_named_constant("__NonZeroNat:2"));
    check(&ctx, &core, &expected).unwrap();
    assert_eq!(
        infer(&ctx, &Term::annot(core, expected.clone())),
        Ok(expected)
    );
}

#[test]
fn existing_fixture_signature_remains_formed() {
    let ctx = lex_core::prelude::legacy_fixture_prelude();
    lex_core::typecheck::validate_context(&ctx).unwrap();
    check(
        &ctx,
        &Term::constant("Compliant"),
        &Term::constant("ComplianceVerdict"),
    )
    .unwrap();
}

#[test]
fn nullary_count_pattern_in_a_global_type_needs_no_signature_entry() {
    use lex_core::ast::{Branch, Constructor, Pattern, QualIdent};

    let expected = Term::match_expr(
        Term::constant("n"),
        Term::type_sort(1),
        vec![
            Branch {
                pattern: Pattern::Constructor {
                    constructor: Constructor::new(QualIdent::simple("__NonZeroNat:1")),
                    binders: Vec::new(),
                },
                body: Term::prop(),
            },
            Branch {
                pattern: Pattern::Wildcard,
                body: Term::type_sort(0),
            },
        ],
    );
    let ctx = lex_core::prelude::production_prelude()
        .with_named_constant("n", Term::constant("Nat"))
        .with_named_constant("T", expected.clone());
    assert!(!ctx.contains_named_constant("__NonZeroNat:1"));
    check(&ctx, &Term::constant("T"), &expected).unwrap();
    assert_eq!(infer(&ctx, &Term::constant("T")), Ok(expected));
}

#[test]
fn invalid_unused_declarations_cannot_bypass_public_entrypoints() {
    use lex_core::typecheck::infer_admissible;

    for ctx in [
        Context::empty().extend(bad()),
        Context::empty().with_named_constant("unused", bad()),
    ] {
        assert!(infer(&ctx, &Term::prop()).is_err());
        assert!(infer_admissible(&ctx, &Term::prop()).is_err());
        assert!(check(&ctx, &Term::prop(), &Term::type_sort(1)).is_err());
        assert!(check_admissible(&ctx, &Term::prop(), &Term::type_sort(1)).is_err());
    }
}

#[test]
fn signature_dependency_limit_returns_an_error_on_a_bounded_stack() {
    use lex_core::typecheck::TypeError;

    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            for length in [24, 256] {
                let mut ctx = Context::empty();
                for index in 0..length {
                    let ty = Term::Let {
                        binder: Ident::new("x"),
                        ty: Box::new(Term::type_sort(0)),
                        val: Box::new(Term::constant(&format!("A{:03}", index + 1))),
                        body: Box::new(Term::type_sort(0)),
                    };
                    ctx = ctx.with_named_constant(&format!("A{index:03}"), ty);
                }
                ctx = ctx.with_named_constant(&format!("A{length:03}"), Term::type_sort(0));
                let expected = if length == 24 {
                    Ok(Term::type_sort(1))
                } else {
                    Err(TypeError::RecursionLimitExceeded)
                };
                assert_eq!(
                    infer(&ctx, &Term::prop()),
                    expected,
                    "dependency chain of length {length}",
                );
            }
        })
        .unwrap()
        .join()
        .expect("signature validation must preserve the caller stack");
}
