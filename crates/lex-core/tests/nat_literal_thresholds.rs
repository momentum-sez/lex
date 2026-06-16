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
use lex_core::typecheck::check_admissibility;
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
    let core = elaborate::elaborate(&surface, &ctx)
        .unwrap_or_else(|e| panic!("elaboration error: {e}"));
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
