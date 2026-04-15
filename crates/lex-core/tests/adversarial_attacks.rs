//! Adversarial attacks on the mez-lex type system.
//!
//! Each test attempts to break a different invariant of the type system.
//! Tests that SHOULD fail (system is sound) assert on the error.
//! Tests that expose vulnerabilities are documented.

use mez_lex::ast::*;
use mez_lex::typecheck::{check, check_admissibility, infer, Context, TypeError, AdmissibilityViolation};
use mez_lex::debruijn::{assign_indices, shift, substitute, DebruijnError};

// ============================================================
// Helpers
// ============================================================

fn type0() -> Term { Term::Sort(Sort::Type(Level::Nat(0))) }
fn type1() -> Term { Term::Sort(Sort::Type(Level::Nat(1))) }
fn prop() -> Term { Term::Sort(Sort::Prop) }

fn var(i: u32) -> Term {
    Term::Var { name: Ident::new(&format!("v{}", i)), index: i }
}

fn named_var(name: &str) -> Term {
    Term::Var { name: Ident::new(name), index: 0 }
}

fn lam(param_type: Term, body: Term) -> Term {
    Term::Lambda {
        binder: Ident::new("x"),
        domain: Box::new(param_type),
        body: Box::new(body),
    }
}

fn pi(domain: Term, codomain: Term) -> Term {
    Term::Pi {
        binder: Ident::new("_"),
        domain: Box::new(domain),
        effect_row: None,
        codomain: Box::new(codomain),
    }
}

fn app(func: Term, arg: Term) -> Term {
    Term::App { func: Box::new(func), arg: Box::new(arg) }
}

fn annot(term: Term, ty: Term) -> Term {
    Term::Annot { term: Box::new(term), ty: Box::new(ty) }
}

fn let_(def_type: Term, def_val: Term, body: Term) -> Term {
    Term::Let {
        binder: Ident::new("x"),
        ty: Box::new(def_type),
        val: Box::new(def_val),
        body: Box::new(body),
    }
}

// ============================================================
// ATTACK 1: Semantic type confusion — well-typed but wrong
// ============================================================

/// Attack: Apply a non-function. The type checker should reject App(Type_0, Type_0).
#[test]
fn attack1_apply_non_function() {
    let ctx = Context::empty();
    // Type_0 has type Type_1. Type_0 is not a Pi type.
    // Applying Type_0 to Type_0 should fail with NotAFunction.
    let term = app(type0(), type0());
    let result = infer(&ctx, &term);
    assert!(result.is_err(), "VULNERABILITY: applying non-function succeeded!");
    match result.unwrap_err() {
        TypeError::NotAFunction { .. } => { /* sound */ }
        other => panic!("Wrong error kind: {:?}", other),
    }
}

/// Attack: Construct a term that type-checks as Type_0 -> Type_0, but the
/// body actually returns something of a different type. Specifically, try
/// to check `λ(x : Type_0). Type_1` against `Type_0 -> Type_0`.
/// Type_1 : Type_2, not Type_0. But the codomain says Type_0.
#[test]
fn attack1_lambda_body_type_mismatch() {
    let ctx = Context::empty();
    // expected type: Π(_ : Type_0). Type_0
    // term: λ(x : Type_0). Type_1
    // Type_1 : Type_2 ≠ Type_0, so check should fail
    let expected = pi(type0(), type0());
    let term = lam(type0(), type1());
    let result = check(&ctx, &term, &expected);
    assert!(result.is_err(), "VULNERABILITY: body type mismatch passed check!");
}

/// Attack: Use universe polymorphism-like trick — check if Type_0 can be
/// treated as if it were Prop. Type_0 : Type_1, Prop : Type_1. But
/// Type_0 ≠ Prop.
#[test]
fn attack1_type0_is_not_prop() {
    let ctx = Context::empty();
    // Prop -> Prop
    let expected = pi(prop(), prop());
    // λ(x : Type_0). x  -- this has type Type_0 -> Type_0, not Prop -> Prop
    let term = lam(type0(), var(0));
    let result = check(&ctx, &term, &expected);
    assert!(result.is_err(), "VULNERABILITY: Type_0 confused with Prop!");
}

// ============================================================
// ATTACK 2: Admissibility boundary bypass
// ============================================================

/// Attack: Nest a non-admissible term (Rec) inside an admissible
/// wrapper (Annot) to see if the recursive check catches it.
#[test]
fn attack2_rec_inside_annot() {
    let ctx = Context::empty();
    let rec = Term::Rec {
        binder: Ident::new("f"),
        ty: Box::new(type0()),
        body: Box::new(var(0)),
    };
    let sneaky = annot(rec, type0());
    let result = infer(&ctx, &sneaky);
    assert!(result.is_err(), "VULNERABILITY: Rec sneaked past admissibility via Annot!");
    match result.unwrap_err() {
        TypeError::Admissibility { violation: AdmissibilityViolation::RecNotSupported, .. } => {
            /* sound */
        }
        other => panic!("Wrong error: {:?}", other),
    }
}

/// Attack: Nest a Hole inside a Let binding.
#[test]
fn attack2_hole_inside_let() {
    let ctx = Context::empty();
    let hole = Term::Hole(Hole {
        name: Some(Ident::new("sneaky")),
        ty: Box::new(type0()),
        authority: AuthorityRef::Named(QualIdent::simple("attacker")),
        scope: None,
    });
    let term = let_(type0(), type0(), hole);
    let result = infer(&ctx, &term);
    assert!(result.is_err(), "VULNERABILITY: Hole sneaked through via Let body!");
}

/// Attack: Nest Sigma inside Lambda body (deeply nested non-admissible).
#[test]
fn attack2_sigma_inside_lambda() {
    let ctx = Context::empty();
    let sigma = Term::Sigma {
        binder: Ident::new("x"),
        fst_ty: Box::new(type0()),
        snd_ty: Box::new(type0()),
    };
    // λ(y : Type_0). Σ(x : Type_0). Type_0
    let sneaky_lam = lam(type0(), sigma);
    let expected = pi(type0(), type0()); // wrong type but we want admissibility check first
    let result = check(&ctx, &sneaky_lam, &expected);
    assert!(result.is_err(), "VULNERABILITY: Sigma sneaked past admissibility in Lambda body!");
}

/// Attack: EffectRow::Empty in Pi should pass, but EffectRow::Var(0) should fail.
/// Try to construct an effectful Pi and wrap it to bypass.
#[test]
fn attack2_effectful_pi_as_domain_of_another_pi() {
    let ctx = Context::empty();
    // Construct: Π(_ : (Π(x : Type_0) [read]. Type_0)). Type_0
    // The inner Pi has a non-empty effect row.
    let inner_pi = Term::Pi {
        binder: Ident::new("x"),
        domain: Box::new(type0()),
        effect_row: Some(EffectRow::Effects(vec![Effect::Read])),
        codomain: Box::new(type0()),
    };
    let outer_pi = pi(inner_pi, type0());
    let result = infer(&ctx, &outer_pi);
    assert!(result.is_err(), "VULNERABILITY: effectful Pi sneaked past as domain!");
}

/// Attack: Pi with EffectRow::Empty (which is Some(Empty), not None)
/// should still be admissible.
#[test]
fn attack2_pi_with_explicit_empty_effect_row() {
    let ctx = Context::empty();
    let term = Term::Pi {
        binder: Ident::new("x"),
        domain: Box::new(type0()),
        effect_row: Some(EffectRow::Empty),
        codomain: Box::new(type0()),
    };
    let result = infer(&ctx, &term);
    // EffectRow::Empty is explicitly accepted by the admissibility checker
    assert!(result.is_ok(), "EffectRow::Empty Pi rejected incorrectly: {:?}", result.unwrap_err());
}

/// Attack: Constant without signature entry — admissibility says OK,
/// but infer should fail because no type is registered.
#[test]
fn attack2_constant_without_signature() {
    let ctx = Context::empty();
    let term = Term::Constant(QualIdent::simple("FakeType"));
    // check_admissibility says Constant is OK
    assert!(check_admissibility(&term).is_ok());
    // But infer should fail because no signature entry
    let result = infer(&ctx, &term);
    assert!(result.is_err(), "VULNERABILITY: Constant without signature was accepted!");
    match result.unwrap_err() {
        TypeError::Admissibility { violation: AdmissibilityViolation::ConstantNotSupported, .. } => {
            /* sound: the constant is not in the global signature */
        }
        other => panic!("Wrong error: {:?}", other),
    }
}

// ============================================================
// ATTACK 3: Stack overflow via deep nesting (depth limits)
// ============================================================

/// Build a term nested 300 levels deep (above MAX_DEPTH=256 in debruijn.rs).
/// De Bruijn shift should hit the recursion limit.
/// Runs on a thread with extra stack to avoid Drop overflow.
#[test]
fn attack3_deep_shift_overflow() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let mut term = var(0);
            for _ in 0..300 {
                term = Term::Lambda {
                    binder: Ident::new("x"),
                    domain: Box::new(prop()),
                    body: Box::new(term),
                };
            }
            let result = shift(&term, 0, 1);
            assert!(result.is_err(), "VULNERABILITY: shift did not hit depth limit at 300 levels!");
            match result.unwrap_err() {
                DebruijnError::RecursionLimit { .. } => { /* sound */ }
                other => panic!("Wrong error: {:?}", other),
            }
        })
        .expect("thread spawn")
        .join()
        .expect("thread join");
}

/// Build a deeply nested term and try assign_indices.
/// Runs on a thread with extra stack to avoid Drop overflow.
#[test]
fn attack3_deep_assign_indices_overflow() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let mut term = named_var("x");
            for _ in 0..300 {
                term = Term::Lambda {
                    binder: Ident::new("x"),
                    domain: Box::new(prop()),
                    body: Box::new(term),
                };
            }
            let result = assign_indices(&term);
            assert!(result.is_err(), "VULNERABILITY: assign_indices did not hit depth limit!");
            match result.unwrap_err() {
                DebruijnError::RecursionLimit { .. } => { /* sound */ }
                other => panic!("Wrong error: {:?}", other),
            }
        })
        .expect("thread spawn")
        .join()
        .expect("thread join");
}

/// Build a deeply nested term and try substitute.
/// Runs on a thread with extra stack to avoid Drop overflow.
#[test]
fn attack3_deep_substitute_overflow() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let mut term = var(0);
            for _ in 0..300 {
                term = Term::Lambda {
                    binder: Ident::new("x"),
                    domain: Box::new(prop()),
                    body: Box::new(term),
                };
            }
            let result = substitute(&term, 0, &prop());
            assert!(result.is_err(), "VULNERABILITY: substitute did not hit depth limit!");
            match result.unwrap_err() {
                DebruijnError::RecursionLimit { .. } => { /* sound */ }
                other => panic!("Wrong error: {:?}", other),
            }
        })
        .expect("thread spawn")
        .join()
        .expect("thread join");
}

/// The type checker now has depth limits (MAX_DEPTH=192). A 300-deep Pi chain
/// triggers RecursionLimitExceeded in check_admissibility.
/// Runs on a thread with extra stack to avoid Drop overflow.
#[test]
fn attack3_deep_pi_typecheck_overflow() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let ctx = Context::empty();
            let mut term = type0();
            for _ in 0..300 {
                term = pi(type0(), term);
            }
            let result = infer(&ctx, &term);
            assert!(result.is_err());
            match result.unwrap_err() {
                TypeError::RecursionLimitExceeded => { /* sound: depth guard caught it */ }
                other => panic!("expected RecursionLimitExceeded, got: {:?}", other),
            }
        })
        .expect("thread spawn")
        .join()
        .expect("thread join");
}

/// Deep nesting in WHNF: build a 200-deep application chain.
/// With depth guards, check_admissibility catches this before reduction.
/// Runs on a thread with extra stack to avoid Drop overflow.
#[test]
fn attack3_deep_whnf_reduction() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let ctx = Context::empty();
            let mut term = type0();
            for _ in 0..200 {
                let id = lam(type1(), var(0));
                let id_annot = annot(id, pi(type1(), type1()));
                term = app(id_annot, term);
            }
            let result = infer(&ctx, &term);
            // With depth guards, this returns RecursionLimitExceeded.
            assert!(result.is_err());
            match result.unwrap_err() {
                TypeError::RecursionLimitExceeded => { /* sound: depth guard caught it */ }
                other => panic!("expected RecursionLimitExceeded, got: {:?}", other),
            }
        })
        .expect("thread spawn")
        .join()
        .expect("thread join");
}

// ============================================================
// ATTACK 4: Type-in-Type via universe level manipulation
// ============================================================

/// Attack: Can we get Type_n : Type_n? (Girard's paradox entry point)
/// The rule is Type_n : Type_{n+1}. Can we confuse the level arithmetic?
#[test]
fn attack4_type_in_type_direct() {
    let ctx = Context::empty();
    // Type_0 : Type_1, never Type_0 : Type_0
    let result = check(&ctx, &type0(), &type0());
    assert!(result.is_err(), "VULNERABILITY: Type_0 : Type_0 accepted! Type-in-Type!");
}

/// Attack: Use Level::Max to try to fool level computation.
/// max(0, 0) = 0. Type_{max(0,0)} : Type_1, not Type_0.
#[test]
fn attack4_max_level_trick() {
    let ctx = Context::empty();
    let tricky_sort = Term::Sort(Sort::Type(Level::Max(
        Box::new(Level::Nat(0)),
        Box::new(Level::Nat(0)),
    )));
    let ty = infer(&ctx, &tricky_sort).unwrap();
    // Should be Type_1
    let expected = type1();
    assert!(
        ty == expected,
        "VULNERABILITY: Type_{{max(0,0)}} has wrong type: {:?}",
        ty
    );
}

/// Attack: Level::Succ arithmetic. Type_{0+0} = Type_0 : Type_1
/// But can we get Type_{n+k} to evaluate wrong?
#[test]
fn attack4_succ_level_overflow() {
    let ctx = Context::empty();
    // Type_{0 + u64::MAX} — this is a huge level
    let huge_sort = Term::Sort(Sort::Type(Level::Succ(Box::new(Level::Nat(0)), u64::MAX)));
    let result = infer(&ctx, &huge_sort);
    // eval_level does 0 + u64::MAX = u64::MAX
    // Then sort rule does u64::MAX + 1 which overflows!
    match result {
        Ok(ty) => {
            // Check if the type is correct (Type_{u64::MAX + 1})
            // If u64::MAX + 1 overflowed to 0, that's Type_0 — WRONG
            match &ty {
                Term::Sort(Sort::Type(Level::Nat(n))) => {
                    if *n == 0 {
                        panic!("VULNERABILITY: Level overflow! Type_{{u64::MAX}} : Type_0 (wrapped around!)");
                    }
                    // If n == 0, that's the overflow bug. If panic doesn't trigger, it's ok.
                }
                _ => {}
            }
        }
        Err(_) => { /* error is fine */ }
    }
}

/// Attack: Succ with large offset. Type_{5 + (u64::MAX - 3)}
/// = Type_{u64::MAX + 2}  which would overflow
#[test]
fn attack4_succ_deliberate_wrap() {
    let ctx = Context::empty();
    let sort = Term::Sort(Sort::Type(Level::Succ(Box::new(Level::Nat(5)), u64::MAX - 3)));
    let result = infer(&ctx, &sort);
    // eval_level: 5 + (u64::MAX - 3) = u64::MAX + 2 => overflow
    // With checked/wrapping arithmetic, this either panics or wraps
    match result {
        Ok(ty) => {
            match &ty {
                Term::Sort(Sort::Type(Level::Nat(n))) => {
                    // If this wrapped around to a small number, it's a vulnerability
                    if *n < 100 {
                        panic!("VULNERABILITY: Level arithmetic overflow, got Type_{}", n);
                    }
                }
                _ => {}
            }
        }
        Err(_) => { /* fine */ }
    }
}

// ============================================================
// ATTACK 5: Capture avoidance in substitution
// ============================================================

/// Classic capture-avoidance test: substitute a free variable into a
/// context where the same index would be captured by a binder.
///
/// Term: λ(y : Prop). x@1   (x is free at index 1)
/// Substitute [0 := z@0]:
///   Under binder, target=1, replacement shifted to z@1.
///   x@1 == target 1 → z@1. Correct.
///
/// If capture avoidance is broken, we'd get z@0 (captured by y).
#[test]
fn attack5_basic_capture_avoidance() {
    // λ(y : Prop). x@1 — x is free
    let term = Term::Lambda {
        binder: Ident::new("y"),
        domain: Box::new(prop()),
        body: Box::new(var(1)),
    };
    let replacement = var(0); // z@0
    let result = substitute(&term, 0, &replacement).unwrap();
    match &result {
        Term::Lambda { body, .. } => {
            match body.as_ref() {
                Term::Var { index, .. } => {
                    assert_eq!(*index, 1, "VULNERABILITY: capture occurred! Got index {} instead of 1", index);
                }
                other => panic!("Expected Var, got {:?}", other),
            }
        }
        _ => panic!("Expected Lambda"),
    }
}

/// Double-binder capture test:
/// Term: λ(a : Prop). λ(b : Prop). x@2  (x is free at index 2)
/// Substitute [0 := y@0]:
///   Under first binder: target=1, replacement=y@1
///   Under second binder: target=2, replacement=y@2
///   x@2 == target 2 → y@2. Correct.
#[test]
fn attack5_double_binder_capture() {
    let term = Term::Lambda {
        binder: Ident::new("a"),
        domain: Box::new(prop()),
        body: Box::new(Term::Lambda {
            binder: Ident::new("b"),
            domain: Box::new(prop()),
            body: Box::new(var(2)),
        }),
    };
    let replacement = var(0);
    let result = substitute(&term, 0, &replacement).unwrap();
    match &result {
        Term::Lambda { body: outer, .. } => match outer.as_ref() {
            Term::Lambda { body: inner, .. } => match inner.as_ref() {
                Term::Var { index, .. } => {
                    assert_eq!(*index, 2, "VULNERABILITY: double-binder capture! index={}", index);
                }
                other => panic!("Expected Var, got {:?}", other),
            },
            _ => panic!("Expected inner Lambda"),
        },
        _ => panic!("Expected outer Lambda"),
    }
}

/// Substitution in Pi codomain: Π(y : Type_0). x@1
/// Substitute [0 := z@0]:
///   Same as Lambda — codomain is under a binder, so replacement shifts.
#[test]
fn attack5_pi_codomain_capture() {
    let term = Term::Pi {
        binder: Ident::new("y"),
        domain: Box::new(type0()),
        effect_row: None,
        codomain: Box::new(var(1)),
    };
    let replacement = var(0);
    let result = substitute(&term, 0, &replacement).unwrap();
    match &result {
        Term::Pi { codomain, .. } => match codomain.as_ref() {
            Term::Var { index, .. } => {
                assert_eq!(*index, 1, "VULNERABILITY: Pi codomain capture! index={}", index);
            }
            other => panic!("Expected Var in codomain, got {:?}", other),
        },
        _ => panic!("Expected Pi"),
    }
}

/// Substitution in Let body:
/// let x : Type_0 := Type_0 in y@1
/// Substitute [0 := z@0]:
///   Under binder: target=1, replacement=z@1
///   y@1 == target 1 → z@1
#[test]
fn attack5_let_body_capture() {
    let term = Term::Let {
        binder: Ident::new("x"),
        ty: Box::new(type0()),
        val: Box::new(type0()),
        body: Box::new(var(1)),
    };
    let replacement = var(0);
    let result = substitute(&term, 0, &replacement).unwrap();
    match &result {
        Term::Let { body, .. } => match body.as_ref() {
            Term::Var { index, .. } => {
                assert_eq!(*index, 1, "VULNERABILITY: Let body capture! index={}", index);
            }
            other => panic!("Expected Var, got {:?}", other),
        },
        _ => panic!("Expected Let"),
    }
}

// ============================================================
// ATTACK 6: Effect row comparison gap in Pi conv_eq
// ============================================================

/// The conv_eq function compares effect rows with `e1 == e2` (PartialEq
/// on ast::EffectRow). Two Pi types with different effect rows should NOT
/// be considered equal. Try to construct two Pi types that differ only
/// in effect rows and see if conv_eq treats them as equal.
#[test]
fn attack6_pi_different_effect_rows_not_equal() {
    let ctx = Context::empty();
    // Pi without effects
    let pure_pi = Term::Pi {
        binder: Ident::new("x"),
        domain: Box::new(type0()),
        effect_row: None,
        codomain: Box::new(type0()),
    };
    // Pi with empty effect row (Some(Empty) vs None)
    let empty_effect_pi = Term::Pi {
        binder: Ident::new("x"),
        domain: Box::new(type0()),
        effect_row: Some(EffectRow::Empty),
        codomain: Box::new(type0()),
    };
    // These should be semantically equivalent (None and Empty both mean pure)
    // But PartialEq will say None != Some(Empty)!
    // This means conv_eq will consider them NOT equal.
    // Check: can we have a lambda checked against one but not the other?
    
    let body = lam(type0(), var(0));

    // Check against pure pi (None)
    let _result_pure = check(&ctx, &body, &pure_pi);
    // Check against empty-effect pi (Some(Empty))
    let _result_empty = check(&ctx, &body, &empty_effect_pi);
    
    // Both should succeed (both are pure Pi types)
    // But if admissibility rejects Some(Empty), the empty_effect_pi check never runs
    // Let's see...
    
    // Actually, admissibility DOES accept EffectRow::Empty explicitly.
    // So both should pass admissibility. The question is whether
    // ensure_pi works for both.
    
    // Actually, for check mode with Lambda, ensure_pi is called on the EXPECTED type.
    // ensure_pi reduces to WHNF and matches Pi. Both are already Pi.
    // ensure_pi returns (domain, codomain) — it does not check effect_row.
    // So Lambda check doesn't care about effect_row at all!
    
    // The real gap: if we try to use conv_eq between the two Pi types,
    // e.g., by inferring one and checking against the other:
    let annot_pure = annot(body.clone(), pure_pi.clone());
    let result_check = check(&ctx, &annot_pure, &empty_effect_pi);
    
    // infer(annot(body, pure_pi)) => pure_pi
    // then conv_eq(pure_pi, empty_effect_pi)
    // pure_pi has effect_row: None, empty_effect_pi has effect_row: Some(Empty)
    // conv_eq compares e1 == e2 => None != Some(Empty) => MISMATCH!
    
    match result_check {
        Ok(()) => {
            // If this succeeds, the system correctly identifies them as equivalent
        }
        Err(TypeError::Mismatch { .. }) => {
            // VULNERABILITY: None and Some(EffectRow::Empty) are semantically
            // identical (both mean pure), but conv_eq rejects them.
            // This is a FALSE NEGATIVE — a valid term is rejected.
            // Document as vulnerability.
            eprintln!("CONFIRMED VULNERABILITY: Pi(None) vs Pi(Some(Empty)) mismatch in conv_eq");
        }
        Err(other) => {
            panic!("Unexpected error: {:?}", other);
        }
    }
}

/// Attack: Two effectful Pi types with structurally different but semantically
/// equivalent effect rows. EffectRow::Join(Empty, Effects([Read])) vs Effects([Read]).
/// The conv_eq uses `e1 == e2` which is structural PartialEq on the AST enum.
#[test]
fn attack6_effect_row_join_not_normalized() {
    // This tests the AST-level EffectRow comparison.
    // EffectRow::Join(Empty, Effects([Read])) should equal Effects([Read])
    // semantically, but PartialEq will say they're different.
    let row_simple = EffectRow::Effects(vec![Effect::Read]);
    let row_join = EffectRow::Join(
        Box::new(EffectRow::Empty),
        Box::new(EffectRow::Effects(vec![Effect::Read])),
    );
    
    // These should be semantically equivalent but structurally different
    let are_equal = row_simple == row_join;
    if are_equal {
        // System normalizes — no vulnerability
    } else {
        eprintln!("CONFIRMED VULNERABILITY: EffectRow Join not normalized before comparison");
        // This means conv_eq on Pi types with these effect rows would report mismatch
    }
}

// ============================================================
// ATTACK 7: Ill-typed terms via the type checker entry points
// ============================================================

/// Attack: Forge a De Bruijn index that points to the wrong binder.
/// λ(x : Prop). λ(y : Type_0). x@0
/// Here x@0 actually refers to y (index 0 = innermost binder).
/// The name says "x" but the index says "y".
/// The type checker uses the INDEX, not the name.
/// So this term has type Prop -> Type_0 -> Type_0 (not Prop -> Type_0 -> Prop).
#[test]
fn attack7_forged_debruijn_index() {
    let ctx = Context::empty();
    // λ(x : Prop). λ(y : Type_0). v0@0
    // v0@0 refers to y (innermost binder), which has type Type_0
    let term = lam(prop(), lam(type0(), var(0)));
    let claimed_type = pi(prop(), pi(type0(), prop())); // claims to return Prop
    let real_type = pi(prop(), pi(type0(), type0())); // actually returns Type_0

    // Should fail against claimed type
    let result_wrong = check(&ctx, &term, &claimed_type);
    assert!(result_wrong.is_err(), "VULNERABILITY: forged index accepted with wrong type!");

    // Should succeed against real type
    let result_right = check(&ctx, &term, &real_type);
    assert!(result_right.is_ok(), "Correct type rejected: {:?}", result_right.unwrap_err());
}

/// Attack: Construct a term that is checked in an inconsistent context.
/// Put the SAME variable type at two different indices and see if
/// confusion arises.
#[test]
fn attack7_context_consistency() {
    // ctx = [Type_0, Type_0] — two entries both of type Type_0
    let ctx = Context::empty().extend(type0()).extend(type0());
    // v0 and v1 both have type Type_0
    let v0_ty = infer(&ctx, &var(0)).unwrap();
    let v1_ty = infer(&ctx, &var(1)).unwrap();
    assert_eq!(v0_ty, type0());
    assert_eq!(v1_ty, type0());
    // Correct — no confusion
}

/// Attack: Does the checker correctly reject `(Type_0 : Prop)`?
/// Type_0 : Type_1, not Prop.
#[test]
fn attack7_wrong_annotation() {
    let ctx = Context::empty();
    let term = annot(type0(), prop());
    let result = infer(&ctx, &term);
    // infer(annot(Type_0, Prop)):
    //   infer_sort(Prop) => Prop : Type_1 => level 1, ok
    //   check(Type_0, Prop):
    //     infer(Type_0) => Type_1
    //     conv_eq(Type_1, Prop) => false
    //     => Mismatch
    assert!(result.is_err(), "VULNERABILITY: (Type_0 : Prop) accepted!");
}

/// Attack: try to use a Constant that is registered in the signature
/// with the wrong type, then exploit the wrong type.
#[test]
fn attack7_constant_with_wrong_type() {
    // Register "Nat" as Prop (wrong — should be Type_0 or similar)
    let ctx = Context::empty().with_named_constant("Nat", prop());
    // Now infer(Nat) => Prop
    let nat_ty = infer(&ctx, &Term::Constant(QualIdent::simple("Nat"))).unwrap();
    assert_eq!(nat_ty, prop());
    // This is technically correct behavior — the signature is trusted.
    // If someone registers a wrong type in the signature, the checker trusts it.
    // This is a trust boundary, not a vulnerability — the signature is the TCB.
}

// ============================================================
// ATTACK 8: typecheck.rs shift/subst depth limits
// ============================================================

/// The typecheck.rs module now has depth limits (MAX_DEPTH=192) on all
/// recursive functions. A 500-deep App chain triggers RecursionLimitExceeded
/// in check_admissibility before any inference starts.
/// Runs on a thread with extra stack to avoid Drop overflow.
#[test]
fn attack8_typecheck_shift_depth_limit() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let mut term = type0();
            for _ in 0..500 {
                term = app(term.clone(), type0());
            }
            let ctx = Context::empty();
            let result = infer(&ctx, &term);
            assert!(result.is_err());
            match result.unwrap_err() {
                TypeError::RecursionLimitExceeded => { /* sound: depth guard caught it */ }
                // Also acceptable: NotAFunction if the shallow check fires first
                TypeError::NotAFunction { .. } => { /* sound */ }
                other => panic!("unexpected error: {:?}", other),
            }
        })
        .expect("thread spawn")
        .join()
        .expect("thread join");
}

/// Deeply nested Pi types: 256 levels exceeds MAX_DEPTH=192, so
/// check_admissibility now rejects this with RecursionLimitExceeded.
/// A 180-deep Pi chain (within MAX_DEPTH) should still succeed.
/// Runs on a thread with extra stack to avoid Drop overflow.
#[test]
fn attack8_deep_pi_recursion() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let ctx = Context::empty();
            // 256 deep exceeds MAX_DEPTH=192
            let mut deep = type0();
            for _ in 0..256 {
                deep = pi(type0(), deep);
            }
            let result = infer(&ctx, &deep);
            assert!(result.is_err());
            match result.unwrap_err() {
                TypeError::RecursionLimitExceeded => { /* sound: depth guard caught it */ }
                other => panic!("expected RecursionLimitExceeded, got: {:?}", other),
            }

            // 180 deep is within MAX_DEPTH and should succeed
            let mut shallow = type0();
            for _ in 0..180 {
                shallow = pi(type0(), shallow);
            }
            let result2 = infer(&ctx, &shallow);
            assert!(result2.is_ok(), "180-deep Pi chain failed: {:?}", result2.unwrap_err());
        })
        .expect("thread spawn")
        .join()
        .expect("thread join");
}

// ============================================================
// ATTACK 9: whnf non-termination via Ω combinator
// ============================================================

/// The omega combinator (λx. x x)(λx. x x) would cause infinite
/// beta-reduction. But it can't type-check because self-application
/// (x x) requires x to have type (A -> B) where A = A -> B, which
/// is not expressible without recursive types.
/// Let's try to construct it anyway with raw De Bruijn terms.
#[test]
fn attack9_omega_combinator_rejected() {
    let ctx = Context::empty();
    // λ(x : ?). x x — we need a type for x such that x : A -> B and A = A -> B
    // With a forged annotation, try: (λ(x : Type_0). x x : ?) 
    // But x : Type_0 means x is a type, and applying a type to itself is ill-typed.
    let self_app = app(var(0), var(0)); // x x
    let omega_half = lam(type0(), self_app);
    // Try to check this as (Type_0 -> Type_0)
    let result = check(&ctx, &omega_half, &pi(type0(), type0()));
    // x : Type_0, so x x means applying Type_0 to Type_0
    // infer(x) => Type_0 (lookup index 0)
    // ensure_pi(Type_0) => fails (Type_0 is not a Pi)
    assert!(result.is_err(), "VULNERABILITY: omega combinator body accepted!");
}

