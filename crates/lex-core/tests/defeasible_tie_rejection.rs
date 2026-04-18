//! Defeasible tie rejection — admissibility requires a total order.
//!
//! The defeasible rule form `base unless e₁ | e₂ | …` depends on a total
//! order over the exception set. The decision procedure walks exceptions
//! in priority order and picks the highest-priority exception whose guard
//! holds. Two exceptions at the SAME priority leave the resolution
//! ambiguous — the winner would depend on the container's iteration
//! order, which is not part of the surface semantics.
//!
//! The admissibility gate rejects such ambiguous rules at check time so
//! the compilation function stays a function. This test covers the
//! negative case the op-lex-compiler's §6.2 cycle-3 tightening fixed:
//! two exceptions sharing `(priority)` — in the op-lex-compiler's LexTerm
//! vendoring, the key pair `(priority, source_position)` — must surface
//! as `DefeasibleOrderNotTotal`. The positive case (unique priorities)
//! already has coverage in `adgm_rules.rs` and `seychelles_ibc_rules.rs`.
//!
//! Matching the paper's convention, `source_position` plays the role of
//! a tie-breaker when two exceptions carry the same priority. Lex-core's
//! `Exception` does not carry a `source_position` field — it carries
//! only `priority: Option<u32>`. The admissibility check therefore keys
//! on `priority` alone: two exceptions with equal explicit priorities
//! leave the order non-total regardless of position, and the check
//! rejects them.

use lex_core::ast::{
    AuthorityRef, DefeasibleRule, Exception, Ident, QualIdent, Term,
};
use lex_core::typecheck::{check_admissibility, AdmissibilityViolation, TypeError};

fn lam(binder: &str, domain: Term, body: Term) -> Term {
    Term::Lambda {
        binder: Ident::new(binder),
        domain: Box::new(domain),
        body: Box::new(body),
    }
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

fn var(name: &str, index: u32) -> Term {
    Term::Var {
        name: Ident::new(name),
        index,
    }
}

/// Construct a defeasible rule with the given exception list. The base
/// body is a trivial identity so the test focuses on the priority
/// admissibility check rather than on scrutinee shape.
fn defeasible_with_exceptions(exceptions: Vec<Exception>) -> Term {
    Term::Defeasible(DefeasibleRule {
        name: Ident::new("test_rule"),
        base_ty: Box::new(constant("ComplianceVerdict")),
        base_body: Box::new(lam(
            "ctx",
            constant("IncorporationContext"),
            constant("Compliant"),
        )),
        exceptions,
        lattice: None,
    })
}

/// Minimal exception carrying a given priority. Guard and body are
/// trivial identity-shape terms so the priority is the load-bearing
/// piece of the test.
fn exception_at(priority: u32) -> Exception {
    Exception {
        guard: Box::new(lam(
            "ctx",
            constant("IncorporationContext"),
            app(constant("trivial_guard"), var("ctx", 0)),
        )),
        body: Box::new(lam(
            "ctx",
            constant("IncorporationContext"),
            constant("NonCompliant"),
        )),
        priority: Some(priority),
        authority: Some(AuthorityRef::Named(QualIdent::simple("test.authority"))),
    }
}

/// Exception with no explicit priority — ignored by the total-order
/// check. Lex's tie-breaking for unprioritized exceptions is delegated
/// to the decision procedure's default strategy, not to admissibility.
fn exception_unpriorized() -> Exception {
    Exception {
        guard: Box::new(lam(
            "ctx",
            constant("IncorporationContext"),
            app(constant("trivial_guard"), var("ctx", 0)),
        )),
        body: Box::new(lam(
            "ctx",
            constant("IncorporationContext"),
            constant("NonCompliant"),
        )),
        priority: None,
        authority: None,
    }
}

#[test]
fn two_exceptions_at_same_priority_rejected_as_defeasible_order_not_total() {
    // Both exceptions carry priority 10; the order is non-total.
    // Matching the op-lex-compiler cycle-3 fix (same `(priority,
    // source_position)` rejected), lex-core rejects on `priority`
    // alone since `source_position` is not part of the AST here.
    let rule = defeasible_with_exceptions(vec![exception_at(10), exception_at(10)]);

    let err = check_admissibility(&rule).expect_err("duplicate priority should be rejected");

    match err {
        TypeError::Admissibility { violation, .. } => {
            assert_eq!(
                violation,
                AdmissibilityViolation::DefeasibleOrderNotTotal { priority: 10 },
                "wrong admissibility violation variant"
            );
        }
        other => panic!("expected Admissibility violation, got {other:?}"),
    }
}

#[test]
fn two_exceptions_at_same_non_trivial_priority_both_rejected() {
    // The scenario the task names literally: priority=10 and (conceptual)
    // source_position=5 shared across two exceptions. Since lex-core's
    // `Exception` has no `source_position` field, the shared value is
    // priority alone — this is the most restrictive form of the check
    // the ast supports. Use priority=10 twice in a rule with five
    // exceptions; the admissibility check must still fire.
    let rule = defeasible_with_exceptions(vec![
        exception_at(10), // first at 10 (represents source_position i)
        exception_at(5),
        exception_at(15),
        exception_at(10), // second at 10 (represents source_position j ≠ i)
        exception_at(20),
    ]);

    let err = check_admissibility(&rule).expect_err("duplicate priority must be rejected");
    match err {
        TypeError::Admissibility {
            violation: AdmissibilityViolation::DefeasibleOrderNotTotal { priority },
            ..
        } => {
            assert_eq!(priority, 10, "wrong priority surfaced: {priority}");
        }
        other => panic!("expected DefeasibleOrderNotTotal, got {other:?}"),
    }
}

#[test]
fn error_display_mentions_non_total_and_priority_value() {
    // The error message must be actionable — at minimum, it names the
    // conflicting priority value so an engineer can locate the tie.
    let rule = defeasible_with_exceptions(vec![exception_at(10), exception_at(10)]);
    let err = check_admissibility(&rule).expect_err("duplicate priority should be rejected");
    let msg = format!("{err}");
    assert!(
        msg.to_lowercase().contains("not total") || msg.to_lowercase().contains("order"),
        "display message should mention order/total-order violation: {msg}"
    );
    assert!(msg.contains("10"), "display message should cite the conflicting priority: {msg}");
}

#[test]
fn unique_priorities_still_admissible() {
    // Regression guard: the check must not over-fire. Two exceptions at
    // distinct priorities remain admissible — the order is total.
    // Existing tests (adgm_rules, seychelles_ibc_rules) exercise the
    // one-exception success path; this is the two-exception success
    // path, with a concrete test of the new admissibility branch.
    let rule = defeasible_with_exceptions(vec![exception_at(1), exception_at(2)]);
    assert!(
        check_admissibility(&rule).is_ok(),
        "distinct priorities must be admissible"
    );
}

#[test]
fn unpriorized_exceptions_are_not_checked_by_the_tie_gate() {
    // Lex's `Exception::priority` is `Option<u32>`. Exceptions without
    // an explicit priority are OUTSIDE the total-order check — their
    // tie-breaking rides elsewhere. Two unpriorized exceptions must
    // not trip the admissibility gate.
    let rule = defeasible_with_exceptions(vec![exception_unpriorized(), exception_unpriorized()]);
    assert!(
        check_admissibility(&rule).is_ok(),
        "exceptions without priority must not trigger DefeasibleOrderNotTotal"
    );

    // Mixed case: one unpriorized, one priority=3. Order is total on the
    // prioritized subset; admissibility must pass.
    let mixed = defeasible_with_exceptions(vec![exception_unpriorized(), exception_at(3)]);
    assert!(
        check_admissibility(&mixed).is_ok(),
        "mixed prioritized/unprioritized with no collision must be admissible"
    );
}

#[test]
fn three_exceptions_with_first_pair_collision_reports_the_shared_priority() {
    // A larger mix: three exceptions, the first two share priority 7,
    // the third sits at 9. The admissibility check must surface 7 —
    // the earliest collision under the sorted-priority scan.
    let rule = defeasible_with_exceptions(vec![exception_at(7), exception_at(7), exception_at(9)]);
    let err = check_admissibility(&rule).expect_err("first-pair collision should reject");
    match err {
        TypeError::Admissibility {
            violation: AdmissibilityViolation::DefeasibleOrderNotTotal { priority },
            ..
        } => {
            assert_eq!(priority, 7);
        }
        other => panic!("expected DefeasibleOrderNotTotal {{ priority: 7 }}, got {other:?}"),
    }
}

#[test]
fn single_exception_is_admissible_regardless_of_priority() {
    // A single exception carries no total-order question. Any priority
    // value is admissible; the check must not over-fire on a singleton.
    for p in [0, 1, 10, 100, u32::MAX] {
        let rule = defeasible_with_exceptions(vec![exception_at(p)]);
        assert!(
            check_admissibility(&rule).is_ok(),
            "single exception at priority {p} must be admissible"
        );
    }
}
