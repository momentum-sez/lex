//! Integration tests: exact-count Nat-literal match patterns (`| 0 =>`,
//! `| 1 =>`, `| 2 =>`, `| _ =>`) through the full Lex pipeline.
//!
//! These rules express EXACT-COUNT director/shareholder thresholds — the shape
//! deployed `.lex` compliance rules need but that the elaborator previously
//! could not express (`Nat` had only the `Zero` constructor; positive-count
//! literal patterns failed at elaboration as "unknown constructor").
//!
//! A Nat-literal pattern lowers to the SAME constructor name the evaluator
//! produces for a `Nat` scrutinee — `Zero` for 0, the value-carrying
//! `__NonZeroNat:<n>` marker for a positive count — so it matches the evaluated
//! scrutinee by exact constructor-name equality with no change to the AST, the
//! core calculus, the evaluator's match logic, or the formal proofs.
//!
//! Each test drives a rule through:
//!   1. `lexer::lex`            — surface text → tokens
//!   2. `parser::parse`         — tokens → surface AST (lowers `| <n> =>`)
//!   3. `elaborate::elaborate`  — name resolution + de Bruijn indexing
//!   4. `typecheck::check_admissibility` — admissible-fragment gate
//!   5. `evaluate::evaluate`    — runtime verdict for a concrete count
//!
//! and asserts the resulting `ComplianceVerdict` for counts {0, 1, 2, 3}.

use lex_core::certificate::ComplianceVerdict;
use lex_core::evaluate::{evaluate, RuntimeContext, RuntimeValue};
use lex_core::typecheck::{
    check_admissibility, check_admissibility_mode, AdmissibilityMode, AdmissibilityViolation,
    TypeError,
};
use lex_core::{elaborate, lexer, parser, prelude};

/// Lex → parse → elaborate → admissibility-check. Returns the elaborated,
/// de-Bruijn-indexed core term, having proved it passes the admissible-fragment
/// gate. Panics with a descriptive message on any stage failure.
fn admissible_core(src: &str) -> lex_core::ast::Term {
    let tokens = lexer::lex(src).unwrap_or_else(|e| panic!("lex error: {e:?}"));
    let surface = parser::parse(&tokens).unwrap_or_else(|e| panic!("parse error: {e:?}"));
    // The fixture prelude registers the count accessors these rules read
    // (`director_count`, `shareholder_count`, …) — the same prelude `lex-cli`'s
    // `elaborate`/`check` commands use, so this mirrors the CLI path exactly.
    let ctx = prelude::compliance_prelude();
    let core =
        elaborate::elaborate(&surface, &ctx).unwrap_or_else(|e| panic!("elaboration error: {e}"));
    check_admissibility(&core).unwrap_or_else(|e| panic!("admissibility error: {e}"));
    core
}

/// Evaluate a rule of one `Nat` accessor against a concrete count.
fn verdict_for_count(rule: &lex_core::ast::Term, accessor: &str, count: u64) -> ComplianceVerdict {
    let mut ctx = RuntimeContext::new();
    ctx.insert(accessor, RuntimeValue::Nat(count));
    evaluate(rule, &ctx).unwrap_or_else(|e| panic!("evaluation error at count {count}: {e:?}"))
}

// ---------------------------------------------------------------------------
// `director_count >= 3`
//
//   match director_count ctx return ComplianceVerdict with
//   | 0 => NonCompliant
//   | 1 => NonCompliant
//   | 2 => NonCompliant
//   | _ => Compliant
//
// counts 0/1/2 → NonCompliant; count 3 (and above) → Compliant.
// ---------------------------------------------------------------------------

const DIRECTORS_MIN_THREE: &str = "\
λ(ctx : IncorporationContext).
  match director_count ctx return ComplianceVerdict with
  | 0 => NonCompliant
  | 1 => NonCompliant
  | 2 => NonCompliant
  | _ => Compliant";

#[test]
fn directors_min_three_elaborates_and_is_admissible() {
    // The full surface → core → admissibility path must succeed: this is the
    // shape that previously failed at elaboration ("unknown constructor").
    let _ = admissible_core(DIRECTORS_MIN_THREE);
}

#[test]
fn directors_min_three_evaluates_correctly_for_counts_0_through_3() {
    let rule = admissible_core(DIRECTORS_MIN_THREE);

    // Below the threshold: 0, 1, 2 directors are all NonCompliant.
    assert_eq!(
        verdict_for_count(&rule, "director_count", 0),
        ComplianceVerdict::NonCompliant,
        "0 directors must be NonCompliant under `>= 3`",
    );
    assert_eq!(
        verdict_for_count(&rule, "director_count", 1),
        ComplianceVerdict::NonCompliant,
        "1 director must be NonCompliant under `>= 3`",
    );
    assert_eq!(
        verdict_for_count(&rule, "director_count", 2),
        ComplianceVerdict::NonCompliant,
        "2 directors must be NonCompliant under `>= 3`",
    );

    // At the threshold: 3 directors is Compliant (hits the wildcard arm).
    assert_eq!(
        verdict_for_count(&rule, "director_count", 3),
        ComplianceVerdict::Compliant,
        "3 directors must be Compliant under `>= 3`",
    );
    // And comfortably above the threshold too.
    assert_eq!(
        verdict_for_count(&rule, "director_count", 7),
        ComplianceVerdict::Compliant,
        "7 directors must be Compliant under `>= 3`",
    );
}

// ---------------------------------------------------------------------------
// `shareholder_count >= 2`
//
//   match shareholder_count ctx return ComplianceVerdict with
//   | 0 => NonCompliant
//   | 1 => NonCompliant
//   | _ => Compliant
//
// counts 0/1 → NonCompliant; count 2 (and above) → Compliant.
// ---------------------------------------------------------------------------

const SHAREHOLDERS_MIN_TWO: &str = "\
λ(ctx : IncorporationContext).
  match shareholder_count ctx return ComplianceVerdict with
  | 0 => NonCompliant
  | 1 => NonCompliant
  | _ => Compliant";

#[test]
fn shareholders_min_two_elaborates_and_is_admissible() {
    let _ = admissible_core(SHAREHOLDERS_MIN_TWO);
}

#[test]
fn shareholders_min_two_evaluates_correctly_for_counts_0_through_3() {
    let rule = admissible_core(SHAREHOLDERS_MIN_TWO);

    // Below the threshold: 0, 1 shareholders are NonCompliant.
    assert_eq!(
        verdict_for_count(&rule, "shareholder_count", 0),
        ComplianceVerdict::NonCompliant,
        "0 shareholders must be NonCompliant under `>= 2`",
    );
    assert_eq!(
        verdict_for_count(&rule, "shareholder_count", 1),
        ComplianceVerdict::NonCompliant,
        "1 shareholder must be NonCompliant under `>= 2`",
    );

    // At / above the threshold: 2 and 3 shareholders are Compliant.
    assert_eq!(
        verdict_for_count(&rule, "shareholder_count", 2),
        ComplianceVerdict::Compliant,
        "2 shareholders must be Compliant under `>= 2`",
    );
    assert_eq!(
        verdict_for_count(&rule, "shareholder_count", 3),
        ComplianceVerdict::Compliant,
        "3 shareholders must be Compliant under `>= 2`",
    );
}

// ---------------------------------------------------------------------------
// Discrimination check: the value-carrying marker distinguishes counts.
//
// A regression guard for the LEX-1 value-preservation fix this feature builds
// on: `| 2 =>` must match exactly 2 and nothing else, so a `== 2` rule
// (`| 2 => Compliant | _ => NonCompliant`) is Compliant ONLY at count 2.
// ---------------------------------------------------------------------------

const EXACTLY_TWO: &str = "\
λ(ctx : IncorporationContext).
  match director_count ctx return ComplianceVerdict with
  | 2 => Compliant
  | _ => NonCompliant";

#[test]
fn exact_count_two_matches_only_two() {
    let rule = admissible_core(EXACTLY_TWO);

    assert_eq!(
        verdict_for_count(&rule, "director_count", 0),
        ComplianceVerdict::NonCompliant,
    );
    assert_eq!(
        verdict_for_count(&rule, "director_count", 1),
        ComplianceVerdict::NonCompliant,
    );
    assert_eq!(
        verdict_for_count(&rule, "director_count", 2),
        ComplianceVerdict::Compliant,
        "count 2 must match the `| 2 =>` arm exactly",
    );
    assert_eq!(
        verdict_for_count(&rule, "director_count", 3),
        ComplianceVerdict::NonCompliant,
        "count 3 must NOT match `| 2 =>` — distinct positive naturals do not collapse",
    );
}

// ===========================================================================
// Nested-match arm delimitation (regression for the kernel-observed
// "match on 'ComplianceTag' is not exhaustive" rejection of the Seychelles
// Companies Act 2003 public-company `>= N` rules).
//
// Root cause was NOT the exhaustiveness wildcard-credit (that short-circuit
// was always intact) — it was that the parser's match branch loop was
// GREEDY: a nested `match` in a non-final branch body swallowed the enclosing
// match's trailing `| _ =>` arm, leaving the OUTER match (scrutinising the
// open `ComplianceTag`-typed `company_class`) with no wildcard, which then
// failed admissibility as non-exhaustive over the entire ComplianceTag enum.
//
// The kernel admits deployed rule bodies via
// `check_admissibility_mode(parsed_term, HoleExtension)` on the *parsed*
// (un-elaborated) term, so these fixtures assert that exact path in addition
// to the strict elaborate-then-check path.
// ===========================================================================

/// Parse only (no elaboration) — the shape the kernel's
/// `lex_admission_residuals_for` feeds to `check_admissibility_mode`.
fn parse_only(src: &str) -> lex_core::ast::Term {
    let tokens = lexer::lex(src).unwrap_or_else(|e| panic!("lex error: {e:?}"));
    parser::parse(&tokens).unwrap_or_else(|e| panic!("parse error: {e:?}"))
}

/// Assert a source admits on BOTH the strict (elaborated) gate and the
/// `HoleExtension` gate on the parsed term (the kernel's actual admission
/// path). Returns the elaborated core for evaluation.
fn admissible_core_both_modes(src: &str) -> lex_core::ast::Term {
    let parsed = parse_only(src);
    check_admissibility_mode(&parsed, AdmissibilityMode::HoleExtension).unwrap_or_else(|e| {
        panic!("HoleExtension admissibility (kernel path, parsed term) failed: {e}")
    });
    admissible_core(src)
}

/// Evaluate a rule of (ComplianceTag-classifier, Nat-count) against concrete
/// values for `company_class` + `shareholder_count`.
fn verdict_for_class_and_count(
    rule: &lex_core::ast::Term,
    class: &str,
    count: u64,
) -> ComplianceVerdict {
    let mut ctx = RuntimeContext::new();
    ctx.insert("company_class", RuntimeValue::Tag(class.to_string()));
    ctx.insert("shareholder_count", RuntimeValue::Nat(count));
    evaluate(rule, &ctx).unwrap_or_else(|e| panic!("evaluation error {class}/{count}: {e:?}"))
}

// (a) A match on a ComplianceTag-typed accessor carrying a named-constructor
//     arm, a `__NonZeroNat:N` value-member arm (lowered from `| 1 =>`), and a
//     wildcard MUST admit — the wildcard satisfies exhaustiveness regardless of
//     the value-member pattern, and the value-member arm passes the membership
//     check. (Mixed Nat/Tag arms cannot co-occur in one well-formed match, so
//     this exercises the value-member-plus-wildcard credit on the Nat scrutinee
//     resolved from the count accessor.)
const VALUE_MEMBER_PLUS_WILDCARD: &str = "\
λ(ctx : IncorporationContext).
  match shareholder_count ctx return ComplianceVerdict with
  | 0 => NonCompliant
  | 1 => NonCompliant
  | _ => Compliant";

#[test]
fn value_member_pattern_with_wildcard_admits_on_both_gates() {
    let rule = admissible_core_both_modes(VALUE_MEMBER_PLUS_WILDCARD);
    assert_eq!(
        verdict_for_count(&rule, "shareholder_count", 1),
        ComplianceVerdict::NonCompliant,
    );
    assert_eq!(
        verdict_for_count(&rule, "shareholder_count", 2),
        ComplianceVerdict::Compliant,
    );
}

// (b) The exact nested kernel shape: outer matches `company_class`
//     (ComplianceTag) on `PublicCompany`, inner matches `shareholder_count`
//     (Nat) with `| 0 | 1 | _` (public ≥ 2); the outer `| _ =>` arm holds a
//     second inner match `| 0 | _` (private ≥ 1). This is
//     `modules/lex/seychelles/companies_act_2003.lex` Rule 1, verbatim shape.
//     It MUST admit and evaluate correctly: the parser must not let the inner
//     `PublicCompany`-branch match swallow the outer `| _ =>` arm.
const SC_COMPANIES_ACT_MIN_SHAREHOLDERS: &str = "\
λ(ctx : IncorporationContext).
  match company_class ctx return ComplianceVerdict with
  | PublicCompany => match shareholder_count ctx return ComplianceVerdict with
    | 0 => NonCompliant
    | 1 => NonCompliant
    | _ => Compliant
  | _ => match shareholder_count ctx return ComplianceVerdict with
    | 0 => NonCompliant
    | _ => Compliant";

#[test]
fn nested_company_class_count_rule_admits_on_both_gates() {
    // Regression: pre-fix this REJECTED with
    // "match on 'ComplianceTag' is not exhaustive; missing constructors: [...]".
    let _ = admissible_core_both_modes(SC_COMPANIES_ACT_MIN_SHAREHOLDERS);
}

#[test]
fn nested_company_class_count_rule_evaluates_correctly() {
    let rule = admissible_core_both_modes(SC_COMPANIES_ACT_MIN_SHAREHOLDERS);

    // Public company: below the `>= 2` threshold is NonCompliant.
    assert_eq!(
        verdict_for_class_and_count(&rule, "PublicCompany", 0),
        ComplianceVerdict::NonCompliant,
        "public company, 0 shareholders → NonCompliant",
    );
    assert_eq!(
        verdict_for_class_and_count(&rule, "PublicCompany", 1),
        ComplianceVerdict::NonCompliant,
        "public company, 1 shareholder → NonCompliant (the `>= 2` NonCompliant arm)",
    );
    // At / above the threshold the wildcard (≥ 2) arm fires.
    assert_eq!(
        verdict_for_class_and_count(&rule, "PublicCompany", 2),
        ComplianceVerdict::Compliant,
        "public company, 2 shareholders → Compliant",
    );
    assert_eq!(
        verdict_for_class_and_count(&rule, "PublicCompany", 7),
        ComplianceVerdict::Compliant,
    );

    // Non-public (the outer `| _ =>` arm): a `>= 1` rule.
    assert_eq!(
        verdict_for_class_and_count(&rule, "PrivateCompany", 0),
        ComplianceVerdict::NonCompliant,
        "private company, 0 shareholders → NonCompliant (outer wildcard branch)",
    );
    assert_eq!(
        verdict_for_class_and_count(&rule, "PrivateCompany", 1),
        ComplianceVerdict::Compliant,
        "private company, 1 shareholder → Compliant (outer wildcard branch)",
    );
}

// (c) NEGATIVE guard: a match on a CLOSED finite datatype (`Bool`) that omits a
//     constructor AND has no wildcard MUST still fail admissibility. The
//     nested-arm fix must not over-loosen exhaustiveness for genuinely-closed
//     types. `Bool` has exactly {True, False}; covering only `True` with no
//     wildcard is non-exhaustive.
const BOOL_MISSING_FALSE_NO_WILDCARD: &str = "\
λ(ctx : IncorporationContext).
  match local_resident_director ctx return ComplianceVerdict with
  | True => Compliant";

#[test]
fn closed_datatype_missing_constructor_without_wildcard_still_fails() {
    let parsed = parse_only(BOOL_MISSING_FALSE_NO_WILDCARD);
    let err = check_admissibility_mode(&parsed, AdmissibilityMode::HoleExtension)
        .expect_err("a Bool match missing `False` with no wildcard must be rejected");
    match err {
        TypeError::Admissibility {
            violation:
                AdmissibilityViolation::MatchNonExhaustive {
                    ref missing_constructors,
                    ..
                },
            ..
        } => {
            assert!(
                missing_constructors.iter().any(|c| c == "False"),
                "the missing constructor must be reported as `False`, got {missing_constructors:?}",
            );
        }
        other => panic!("expected MatchNonExhaustive, got {other:?}"),
    }

    // Same posture on the strict elaborate-then-check gate.
    let ctx = prelude::compliance_prelude();
    let core = elaborate::elaborate(&parsed, &ctx).expect("Bool match elaborates");
    check_admissibility(&core)
        .expect_err("strict gate must also reject the non-exhaustive Bool match");
}
