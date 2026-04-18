//! Property-based tests for the Lex type checker.
//!
//! Uses proptest to generate random terms and verify key soundness properties
//! of the bidirectional type checker and the effect row algebra.

use proptest::prelude::*;
use proptest::test_runner::Config as ProptestConfig;

use lex_core::ast::{Ident, Level, Sort, Term};
use lex_core::effects::{effect_subsumes, Effect, EffectRow};
use lex_core::typecheck::{check, check_admissibility, infer, Context};

// ---------------------------------------------------------------------------
// Proptest strategies
// ---------------------------------------------------------------------------

/// Strategy for random `Sort` values.
fn arb_sort() -> impl Strategy<Value = Sort> {
    prop_oneof![
        (0u64..5).prop_map(|n| Sort::Type(Level::Nat(n))),
        Just(Sort::Prop),
    ]
}

/// Strategy for random `Term` values limited to the admissible fragment.
///
/// `depth` controls maximum nesting; once depth reaches 0 only leaf terms
/// (Var, Sort) are generated. This prevents stack overflow and keeps terms
/// manageable.
fn arb_term(depth: u32) -> impl Strategy<Value = Term> {
    if depth == 0 {
        // Leaf terms only
        prop_oneof![
            (0u32..10).prop_map(|i| Term::Var {
                name: Ident::new(&format!("x{}", i)),
                index: i,
            }),
            arb_sort().prop_map(Term::Sort),
        ]
        .boxed()
    } else {
        let leaf = prop_oneof![
            (0u32..10).prop_map(|i| Term::Var {
                name: Ident::new(&format!("x{}", i)),
                index: i,
            }),
            arb_sort().prop_map(Term::Sort),
        ];

        prop_oneof![
            // Weight leaves more heavily to keep terms small
            3 => leaf,
            // Lambda
            1 => (arb_term(depth - 1), arb_term(depth - 1)).prop_map(|(domain, body)| {
                Term::Lambda {
                    binder: Ident::new("x"),
                    domain: Box::new(domain),
                    body: Box::new(body),
                }
            }),
            // Pi (pure)
            1 => (arb_term(depth - 1), arb_term(depth - 1)).prop_map(|(domain, codomain)| {
                Term::Pi {
                    binder: Ident::new("_"),
                    domain: Box::new(domain),
                    effect_row: None,
                    codomain: Box::new(codomain),
                }
            }),
            // App
            1 => (arb_term(depth - 1), arb_term(depth - 1)).prop_map(|(func, arg)| {
                Term::App {
                    func: Box::new(func),
                    arg: Box::new(arg),
                }
            }),
            // Annot
            1 => (arb_term(depth - 1), arb_term(depth - 1)).prop_map(|(t, ty)| {
                Term::Annot {
                    term: Box::new(t),
                    ty: Box::new(ty),
                }
            }),
            // Let
            1 => (arb_term(depth - 1), arb_term(depth - 1), arb_term(depth - 1))
                .prop_map(|(ty, val, body)| {
                    Term::Let {
                        binder: Ident::new("y"),
                        ty: Box::new(ty),
                        val: Box::new(val),
                        body: Box::new(body),
                    }
                }),
        ]
        .boxed()
    }
}

/// Strategy for random `Effect` values.
fn arb_effect() -> impl Strategy<Value = Effect> {
    prop_oneof![
        Just(Effect::Read),
        "[a-z]{1,8}".prop_map(|s| Effect::Write(s)),
        "[a-z]{1,8}".prop_map(|s| Effect::Attest(s)),
        "[a-z]{1,8}".prop_map(|s| Effect::Authority(s)),
        "[a-z]{1,8}".prop_map(|s| Effect::Oracle(s)),
        (0u32..5, 1u64..1000).prop_map(|(l, a)| Effect::Fuel(l, a)),
        Just(Effect::SanctionsQuery),
        "[a-z]{1,8}".prop_map(|s| Effect::Discretion(s)),
    ]
}

/// Strategy for random `EffectRow` values.
fn arb_effect_row() -> impl Strategy<Value = EffectRow> {
    prop_oneof![
        Just(EffectRow::empty()),
        prop::collection::vec(arb_effect(), 0..6).prop_map(|effs| {
            EffectRow::from_effects(effs)
        }),
        prop::collection::vec(arb_effect(), 0..6).prop_map(|effs| {
            EffectRow::branch_sensitive(effs)
        }),
    ]
}

/// Build a context with `n` bindings, each typed at `Type_0`.
fn ctx_with_bindings(n: u32) -> Context {
    let mut ctx = Context::empty();
    for _ in 0..n {
        ctx = ctx.extend(Term::Sort(Sort::Type(Level::Nat(0))));
    }
    ctx
}

fn proptest_config(default_cases: u32) -> ProptestConfig {
    let cases = std::env::var("PROPTEST_CASES")
        .ok()
        .and_then(|raw| raw.parse::<u32>().ok())
        .filter(|cases| *cases > 0)
        .unwrap_or(default_cases);

    ProptestConfig {
        cases,
        failure_persistence: None,
        ..ProptestConfig::default()
    }
}

// ---------------------------------------------------------------------------
// Property (a): Preservation
//
// If `infer(ctx, t) = Ok(ty)`, then `check(ctx, t, ty) = Ok(())`.
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(proptest_config(20))]

    #[test]
    fn preservation(term in arb_term(4)) {
        // Use a context with 10 bindings so Var indices 0..9 are in scope.
        let ctx = ctx_with_bindings(10);
        if let Ok(ty) = infer(&ctx, &term) {
            // Preservation: if we can infer a type, checking against that type must succeed.
            check(&ctx, &term, &ty)
                .expect("preservation violated: infer succeeded but check against inferred type failed");
        }
    }
}

// ---------------------------------------------------------------------------
// Property (b): Determinism
//
// `infer(ctx, t)` called twice gives the same result.
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(proptest_config(20))]

    #[test]
    fn determinism(term in arb_term(4)) {
        let ctx = ctx_with_bindings(10);
        let r1 = infer(&ctx, &term);
        let r2 = infer(&ctx, &term);
        match (&r1, &r2) {
            (Ok(ty1), Ok(ty2)) => prop_assert_eq!(ty1, ty2, "infer returned different types for the same term"),
            (Err(_), Err(_)) => { /* both errored -- deterministic */ }
            _ => panic!("determinism violated: infer returned Ok on one call and Err on the other"),
        }
    }
}

// ---------------------------------------------------------------------------
// Property (c): Depth safety
//
// Random terms of moderate depth never panic -- they always return Ok or Err.
// Keep one deterministic smoke test in the default suite, and leave the
// recursive randomized search as an explicit stress target.
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(proptest_config(3))]

    #[test]
    #[ignore = "stress property; run explicitly with PROPTEST_CASES=N cargo test -- --ignored depth_safety"]
    fn depth_safety(term in arb_term(6)) {
        let ctx = ctx_with_bindings(10);
        // Must not panic. Ok or Err are both fine.
        let _ = infer(&ctx, &term);
    }
}

fn deep_pi_chain(depth: usize) -> Term {
    let mut term = Term::Sort(Sort::Type(Level::Nat(0)));
    for _ in 0..depth {
        term = Term::Pi {
            binder: Ident::new("x"),
            domain: Box::new(Term::Sort(Sort::Type(Level::Nat(0)))),
            effect_row: None,
            codomain: Box::new(term),
        };
    }
    term
}

#[test]
fn depth_safety_smoke() {
    let ctx = Context::empty();
    let term = deep_pi_chain(48);
    let _ = infer(&ctx, &term);
}

// ---------------------------------------------------------------------------
// Property (d): Admissibility monotonic
//
// If `check_admissibility(t)` returns Ok, then `check_admissibility` on any
// immediate sub-term also returns Ok.
// ---------------------------------------------------------------------------

/// Extract immediate sub-terms from an admissible term.
fn immediate_subterms(term: &Term) -> Vec<&Term> {
    match term {
        Term::Var { .. } | Term::Sort(_) => vec![],
        Term::Lambda { domain, body, .. } => vec![domain.as_ref(), body.as_ref()],
        Term::Pi {
            domain, codomain, ..
        } => vec![domain.as_ref(), codomain.as_ref()],
        Term::App { func, arg } => vec![func.as_ref(), arg.as_ref()],
        Term::Annot { term: t, ty } => vec![t.as_ref(), ty.as_ref()],
        Term::Let {
            ty, val, body, ..
        } => vec![ty.as_ref(), val.as_ref(), body.as_ref()],
        _ => vec![],
    }
}

proptest! {
    #![proptest_config(proptest_config(20))]

    #[test]
    fn admissibility_monotonic(term in arb_term(6)) {
        if check_admissibility(&term).is_ok() {
            for sub in immediate_subterms(&term) {
                check_admissibility(sub)
                    .expect("admissibility monotonicity violated: parent is admissible but sub-term is not");
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Property (e): Effect subsumption reflexive
//
// For any EffectRow e, `effect_subsumes(&e, &e)` is true.
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(proptest_config(20))]

    #[test]
    fn effect_subsumption_reflexive(row in arb_effect_row()) {
        prop_assert!(
            effect_subsumes(&row, &row),
            "effect subsumption reflexivity violated for row: {:?}",
            row
        );
    }
}

// ---------------------------------------------------------------------------
// Bonus properties for effect algebra soundness
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(proptest_config(10))]

    /// Empty row is subsumed by any row.
    #[test]
    fn empty_subsumed_by_any(row in arb_effect_row()) {
        let empty = EffectRow::empty();
        prop_assert!(
            effect_subsumes(&empty, &row),
            "empty row should be subsumed by any row, but failed for: {:?}",
            row
        );
    }

    /// Join is an upper bound: both operands are subsumed by the join.
    #[test]
    fn join_is_upper_bound(
        a in arb_effect_row().prop_filter("non-branch-sensitive", |r| !r.is_branch_sensitive()),
        b in arb_effect_row().prop_filter("non-branch-sensitive", |r| !r.is_branch_sensitive()),
    ) {
        let joined = lex_core::effects::effect_join(&a, &b);
        prop_assert!(
            effect_subsumes(&a, &joined),
            "join upper bound violated: a={:?} not subsumed by join={:?}",
            a, joined
        );
        prop_assert!(
            effect_subsumes(&b, &joined),
            "join upper bound violated: b={:?} not subsumed by join={:?}",
            b, joined
        );
    }

    /// Join is idempotent: join(a, a) == a.
    #[test]
    fn join_idempotent(row in arb_effect_row()) {
        let joined = lex_core::effects::effect_join(&row, &row);
        prop_assert_eq!(&joined, &row, "join idempotency violated");
    }

    /// Join is commutative: join(a, b) == join(b, a).
    #[test]
    fn join_commutative(a in arb_effect_row(), b in arb_effect_row()) {
        let ab = lex_core::effects::effect_join(&a, &b);
        let ba = lex_core::effects::effect_join(&b, &a);
        prop_assert_eq!(ab, ba, "join commutativity violated");
    }

    /// Meet is commutative: meet(a, b) == meet(b, a).
    #[test]
    fn meet_commutative(a in arb_effect_row(), b in arb_effect_row()) {
        let ab = lex_core::effects::effect_meet(&a, &b);
        let ba = lex_core::effects::effect_meet(&b, &a);
        prop_assert_eq!(ab, ba, "meet commutativity violated");
    }
}
