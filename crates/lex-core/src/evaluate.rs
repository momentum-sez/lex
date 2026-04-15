//! Runtime evaluator for Lex compliance rules.
//!
//! The type checker (`typecheck.rs`) verifies that rules are well-typed but
//! cannot evaluate them against live entity data. This module bridges that gap:
//! given a Lex `Term` (typically a `lambda (ctx : IncorporationContext). body`
//! rule) and a [`RuntimeContext`] mapping accessor names to concrete values, it
//! reduces the term to a [`ComplianceVerdict`].
//!
//! # Design
//!
//! Each compliance rule is `λ(ctx : IncorporationContext). body` where `body`
//! is typically `match (accessor ctx) return T with | Ctor => Verdict | ...`.
//! At runtime we:
//!
//! 1. Strip the outer Lambda, entering its body.
//! 2. Reduce `App(Constant("accessor"), Var(0))` by looking up `accessor` in
//!    the [`RuntimeContext`] and returning the corresponding constant term.
//! 3. Reduce `Match` by evaluating the scrutinee, finding the first matching
//!    branch (constructor or wildcard), and evaluating the branch body.
//! 4. Reduce `Defeasible` by evaluating the base body, then each exception
//!    guard in priority order; the highest-priority satisfied exception wins.
//! 5. Recognize verdict constants (`Compliant`, `NonCompliant`, `Pending`)
//!    and return the corresponding [`ComplianceVerdict`].

use std::collections::BTreeMap;

use crate::ast::{Pattern, QualIdent, Term};
use crate::certificate::ComplianceVerdict;

// ---------------------------------------------------------------------------
// RuntimeValue — concrete values supplied by the caller
// ---------------------------------------------------------------------------

/// A concrete runtime value for an accessor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeValue {
    /// A natural number (e.g., `director_count` = 3).
    Nat(u64),
    /// A boolean (e.g., `all_identified` = true).
    Bool(bool),
    /// A tag constructor name (e.g., `audit_status` = "AuditComplete").
    Tag(String),
    /// A sanctions result constructor name (e.g., `sanctions_check` = "Clear").
    SanctionsResult(String),
}

// ---------------------------------------------------------------------------
// RuntimeContext — maps accessor names to runtime values
// ---------------------------------------------------------------------------

/// Runtime context mapping accessor names to concrete [`RuntimeValue`]s.
///
/// Populated from live entity data before evaluating a rule. Every accessor
/// referenced by the rule must be present, or evaluation will fail with
/// [`EvalError::UnknownAccessor`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeContext {
    /// Accessor name -> concrete value.
    pub values: BTreeMap<String, RuntimeValue>,
}

impl RuntimeContext {
    /// Create an empty runtime context.
    pub fn new() -> Self {
        Self {
            values: BTreeMap::new(),
        }
    }

    /// Insert an accessor value.
    pub fn insert(&mut self, name: impl Into<String>, value: RuntimeValue) -> &mut Self {
        self.values.insert(name.into(), value);
        self
    }

    /// Look up an accessor's value.
    pub fn get(&self, name: &str) -> Option<&RuntimeValue> {
        self.values.get(name)
    }
}

impl Default for RuntimeContext {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// EvalError — evaluation failures
// ---------------------------------------------------------------------------

/// Errors produced during runtime evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvalError {
    /// An accessor referenced by the rule is not present in the RuntimeContext.
    UnknownAccessor { name: String },

    /// The term reduced to a form that is not a recognized verdict constant.
    NotAVerdict { term: Term },

    /// Match expression had no matching branch for the scrutinee value.
    NoMatchingBranch { scrutinee: Term },

    /// The rule is not a lambda abstraction at the top level.
    NotALambda { term: Term },

    /// Evaluation recursion depth exceeded.
    RecursionLimitExceeded,

    /// Evaluation fuel (reduction steps) exhausted.
    ReductionLimitExceeded,
}

impl std::error::Error for EvalError {}

impl std::fmt::Display for EvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownAccessor { name } => {
                write!(f, "accessor '{}' not found in runtime context", name)
            }
            Self::NotAVerdict { .. } => {
                write!(f, "term did not reduce to a compliance verdict")
            }
            Self::NoMatchingBranch { .. } => {
                write!(f, "no matching branch in match expression")
            }
            Self::NotALambda { .. } => {
                write!(f, "rule is not a lambda abstraction")
            }
            Self::RecursionLimitExceeded => {
                write!(f, "evaluation recursion limit exceeded")
            }
            Self::ReductionLimitExceeded => {
                write!(f, "evaluation reduction limit exceeded")
            }
        }
    }
}

/// Maximum recursion depth for evaluation.
const MAX_EVAL_DEPTH: usize = 192;

/// Maximum number of reduction steps.
const MAX_EVAL_FUEL: usize = 4096;

// ---------------------------------------------------------------------------
// Core evaluator
// ---------------------------------------------------------------------------

/// Evaluate a Lex compliance rule against a [`RuntimeContext`].
///
/// The `term` should be a rule of the form:
/// ```text
/// λ(ctx : IncorporationContext). body
/// ```
/// or a `Defeasible` rule wrapping such a lambda. The evaluator substitutes
/// accessor lookups with values from `ctx` and reduces the term to a
/// [`ComplianceVerdict`].
pub fn evaluate(term: &Term, ctx: &RuntimeContext) -> Result<ComplianceVerdict, EvalError> {
    let mut fuel = MAX_EVAL_FUEL;
    eval_term(term, ctx, 0, &mut fuel)
}

/// Inner recursive evaluator.
fn eval_term(
    term: &Term,
    ctx: &RuntimeContext,
    depth: usize,
    fuel: &mut usize,
) -> Result<ComplianceVerdict, EvalError> {
    if depth > MAX_EVAL_DEPTH {
        return Err(EvalError::RecursionLimitExceeded);
    }
    *fuel = fuel
        .checked_sub(1)
        .ok_or(EvalError::ReductionLimitExceeded)?;

    match term {
        // ── Verdict constants ──────────────────────────────────────────
        Term::Constant(name) => {
            let n = qual_ident_name(name);
            match n {
                "Compliant" => Ok(ComplianceVerdict::Compliant),
                "NonCompliant" => Ok(ComplianceVerdict::NonCompliant),
                "Pending" => Ok(ComplianceVerdict::Pending),
                _ => Err(EvalError::NotAVerdict { term: term.clone() }),
            }
        }

        // ── Lambda: enter the body with runtime context ────────────────
        // The lambda binds the IncorporationContext. We don't literally
        // substitute — instead we pass the RuntimeContext through and
        // resolve accessor applications when we encounter them.
        Term::Lambda { body, .. } => eval_term(body, ctx, depth + 1, fuel),

        // ── Application: resolve accessor lookups ──────────────────────
        // App(Constant("accessor_name"), Var(0)) => look up in ctx
        Term::App { func, arg } => eval_app(func, arg, ctx, depth, fuel),

        // ── Match: evaluate scrutinee, find matching branch ────────────
        Term::Match {
            scrutinee,
            branches,
            ..
        } => {
            let scrutinee_val = eval_to_constant(scrutinee, ctx, depth + 1, fuel)?;
            // Find matching branch
            for branch in branches {
                match &branch.pattern {
                    Pattern::Constructor {
                        constructor,
                        binders: _,
                    } => {
                        let ctor_name = qual_ident_name(&constructor.name);
                        if ctor_name == scrutinee_val {
                            return eval_term(&branch.body, ctx, depth + 1, fuel);
                        }
                    }
                    Pattern::Wildcard => {
                        return eval_term(&branch.body, ctx, depth + 1, fuel);
                    }
                }
            }
            Err(EvalError::NoMatchingBranch {
                scrutinee: scrutinee.as_ref().clone(),
            })
        }

        // ── Let: evaluate the bound value, then the body ───────────────
        // Evaluate the bound value to a RuntimeValue and insert it into
        // the context under the binder name for the body evaluation. If
        // the value cannot be resolved to a RuntimeValue, fall through to
        // structural evaluation of the body with the unchanged context.
        Term::Let {
            binder, val, body, ..
        } => {
            let resolved = eval_to_constant(val, ctx, depth + 1, fuel)
                .ok()
                .and_then(|name| constant_name_to_runtime_value(&name));
            match resolved {
                Some(rv) => {
                    let mut extended_ctx = ctx.clone();
                    extended_ctx.insert(binder.name.as_str(), rv);
                    eval_term(body, &extended_ctx, depth + 1, fuel)
                }
                None => eval_term(body, ctx, depth + 1, fuel),
            }
        }

        // ── Annotation: strip and evaluate inner term ──────────────────
        Term::Annot { term: inner, .. } => eval_term(inner, ctx, depth + 1, fuel),

        // ── Defeasible rule: evaluate base, then exceptions ────────────
        Term::Defeasible(rule) => {
            // Evaluate base body
            let base_verdict = eval_term(&rule.base_body, ctx, depth + 1, fuel)?;

            // Collect exceptions that are satisfied (guard evaluates to Compliant/True)
            // and pick the highest-priority one.
            let mut best_exception: Option<(u32, ComplianceVerdict)> = None;

            for exception in &rule.exceptions {
                let guard_result = eval_guard(&exception.guard, ctx, depth + 1, fuel);
                let guard_satisfied = match guard_result {
                    Ok(true) => true,
                    Ok(false) => false,
                    // If the guard can't be evaluated, treat it as unsatisfied
                    Err(_) => false,
                };

                if guard_satisfied {
                    let exception_verdict =
                        eval_term(&exception.body, ctx, depth + 1, fuel)?;
                    let priority = exception.priority.unwrap_or(0);

                    match &best_exception {
                        None => {
                            best_exception = Some((priority, exception_verdict));
                        }
                        Some((best_priority, _)) if priority > *best_priority => {
                            best_exception = Some((priority, exception_verdict));
                        }
                        _ => {}
                    }
                }
            }

            // If any exception was satisfied, its verdict overrides the base
            match best_exception {
                Some((_, verdict)) => Ok(verdict),
                None => Ok(base_verdict),
            }
        }

        // ── Var(0) at the top level means the context itself ───────────
        // This shouldn't normally appear as a final result, but if a rule
        // is just `λctx. ctx` it would reduce here.
        Term::Var { .. } => Err(EvalError::NotAVerdict { term: term.clone() }),

        // ── Everything else is not evaluable ───────────────────────────
        _ => Err(EvalError::NotAVerdict { term: term.clone() }),
    }
}

// ---------------------------------------------------------------------------
// Application resolution
// ---------------------------------------------------------------------------

/// Evaluate a function application. The key case is:
/// `App(Constant("accessor_name"), _)` — look up accessor in the RuntimeContext
/// and return the corresponding constant.
fn eval_app(
    func: &Term,
    arg: &Term,
    ctx: &RuntimeContext,
    depth: usize,
    fuel: &mut usize,
) -> Result<ComplianceVerdict, EvalError> {
    // Case 1: Direct accessor application — App(Constant("accessor"), _)
    if let Term::Constant(name) = func {
        let accessor_name = qual_ident_name(name);
        if let Some(val) = ctx.get(accessor_name) {
            let resolved = runtime_value_to_term(val);
            return eval_term(&resolved, ctx, depth + 1, fuel);
        }
        // Not an accessor — might be a constructor application or something else
        return Err(EvalError::UnknownAccessor {
            name: accessor_name.to_string(),
        });
    }

    // Case 2: Beta-reduction — App(Lambda { binder, body, .. }, arg)
    // Evaluate the argument to a RuntimeValue, extend the context with the
    // binder name mapped to that value, and evaluate the body. If the
    // argument cannot be resolved, fall through to structural evaluation.
    if let Term::Lambda {
        binder, body, ..
    } = func
    {
        let resolved = eval_to_constant(arg, ctx, depth + 1, fuel)
            .ok()
            .and_then(|name| constant_name_to_runtime_value(&name));
        match resolved {
            Some(rv) => {
                let mut extended_ctx = ctx.clone();
                extended_ctx.insert(binder.name.as_str(), rv);
                return eval_term(body, &extended_ctx, depth + 1, fuel);
            }
            None => {
                return eval_term(body, ctx, depth + 1, fuel);
            }
        }
    }

    Err(EvalError::NotAVerdict {
        term: Term::App {
            func: Box::new(func.clone()),
            arg: Box::new(arg.clone()),
        },
    })
}

/// Evaluate an accessor application, returning the resolved constant as a Term
/// rather than a ComplianceVerdict. This is used for Match scrutinee evaluation.
fn eval_to_constant(
    term: &Term,
    ctx: &RuntimeContext,
    depth: usize,
    fuel: &mut usize,
) -> Result<String, EvalError> {
    if depth > MAX_EVAL_DEPTH {
        return Err(EvalError::RecursionLimitExceeded);
    }
    *fuel = fuel
        .checked_sub(1)
        .ok_or(EvalError::ReductionLimitExceeded)?;

    match term {
        // A constant like "Compliant", "True", "Active", "Zero", etc.
        Term::Constant(name) => Ok(qual_ident_name(name).to_string()),

        // Application: resolve accessor
        Term::App { func, .. } => {
            if let Term::Constant(name) = func.as_ref() {
                let accessor_name = qual_ident_name(name);
                if let Some(val) = ctx.get(accessor_name) {
                    return Ok(runtime_value_to_constant_name(val));
                }
                return Err(EvalError::UnknownAccessor {
                    name: accessor_name.to_string(),
                });
            }
            Err(EvalError::NotAVerdict { term: term.clone() })
        }

        // Annotation: strip
        Term::Annot { term: inner, .. } => eval_to_constant(inner, ctx, depth + 1, fuel),

        // Var(0) in a lambda body — this IS the context, can't resolve to a constant
        _ => Err(EvalError::NotAVerdict { term: term.clone() }),
    }
}

/// Evaluate a defeasible exception guard.
///
/// Guards are propositions. In the admissible fragment, guards are typically
/// boolean-valued or constructor-match expressions. We evaluate them and
/// interpret the result:
/// - `Compliant` / `True` / `Clear` => satisfied (true)
/// - `NonCompliant` / `False` / anything else => not satisfied (false)
fn eval_guard(
    guard: &Term,
    ctx: &RuntimeContext,
    depth: usize,
    fuel: &mut usize,
) -> Result<bool, EvalError> {
    // Try to evaluate the guard as a verdict
    match eval_term(guard, ctx, depth, fuel) {
        Ok(ComplianceVerdict::Compliant) => Ok(true),
        Ok(ComplianceVerdict::NonCompliant) => Ok(false),
        Ok(ComplianceVerdict::Pending) => Ok(false),
        Err(_) => {
            // Guard might evaluate to a Bool constant instead of a verdict
            // Try to evaluate to a constant name — share the same fuel budget
            // to prevent unbounded evaluation across guards.
            match eval_to_constant(guard, ctx, depth, fuel) {
                Ok(name) => match name.as_str() {
                    "True" | "Clear" | "Compliant" => Ok(true),
                    _ => Ok(false),
                },
                Err(_) => Ok(false),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Extract the simple name from a QualIdent.
fn qual_ident_name(qi: &QualIdent) -> &str {
    qi.segments
        .last()
        .map(|s| s.as_str())
        .unwrap_or("")
}

/// Convert a RuntimeValue to a Lex Term constant.
fn runtime_value_to_term(val: &RuntimeValue) -> Term {
    match val {
        RuntimeValue::Nat(0) => Term::Constant(QualIdent::simple("Zero")),
        // Non-zero Nat: there's no prelude constructor for non-zero naturals.
        // We use a wildcard-matching strategy: non-zero naturals will NOT match
        // the "Zero" constructor, so they'll fall through to wildcard branches.
        // Encode as a special non-zero marker that won't match "Zero".
        RuntimeValue::Nat(_) => Term::Constant(QualIdent::simple("__NonZeroNat")),
        RuntimeValue::Bool(true) => Term::Constant(QualIdent::simple("True")),
        RuntimeValue::Bool(false) => Term::Constant(QualIdent::simple("False")),
        RuntimeValue::Tag(name) => Term::Constant(QualIdent::simple(name)),
        RuntimeValue::SanctionsResult(name) => Term::Constant(QualIdent::simple(name)),
    }
}

/// Convert a RuntimeValue to a constructor name string for pattern matching.
fn runtime_value_to_constant_name(val: &RuntimeValue) -> String {
    match val {
        RuntimeValue::Nat(0) => "Zero".to_string(),
        RuntimeValue::Nat(_) => "__NonZeroNat".to_string(),
        RuntimeValue::Bool(true) => "True".to_string(),
        RuntimeValue::Bool(false) => "False".to_string(),
        RuntimeValue::Tag(name) => name.clone(),
        RuntimeValue::SanctionsResult(name) => name.clone(),
    }
}

/// Convert a constant name (from `eval_to_constant`) back to a [`RuntimeValue`].
///
/// Recognizes the well-known constructor names produced by [`runtime_value_to_constant_name`].
/// Returns `None` for unrecognized names, allowing the caller to fall through
/// to structural evaluation.
fn constant_name_to_runtime_value(name: &str) -> Option<RuntimeValue> {
    match name {
        "Zero" => Some(RuntimeValue::Nat(0)),
        "__NonZeroNat" => Some(RuntimeValue::Nat(1)),
        "True" => Some(RuntimeValue::Bool(true)),
        "False" => Some(RuntimeValue::Bool(false)),
        "Clear" | "Hit" | "Pending" | "Compliant" | "NonCompliant" => {
            Some(RuntimeValue::Tag(name.to_string()))
        }
        _ => Some(RuntimeValue::Tag(name.to_string())),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Branch, Constructor, DefeasibleRule, Exception, Ident, Pattern, QualIdent};

    // ── Helpers ────────────────────────────────────────────────────────

    fn constant(name: &str) -> Term {
        Term::Constant(QualIdent::simple(name))
    }

    fn var(name: &str, index: u32) -> Term {
        Term::Var {
            name: Ident::new(name),
            index,
        }
    }

    fn lam(binder: &str, domain: Term, body: Term) -> Term {
        Term::lam(binder, domain, body)
    }

    fn app(func: Term, arg: Term) -> Term {
        Term::app(func, arg)
    }

    fn match_expr(scrutinee: Term, return_ty: Term, branches: Vec<Branch>) -> Term {
        Term::match_expr(scrutinee, return_ty, branches)
    }

    fn ctor_branch(ctor_name: &str, body: Term) -> Branch {
        Branch {
            pattern: Pattern::Constructor {
                constructor: Constructor::new(QualIdent::simple(ctor_name)),
                binders: vec![],
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

    /// Build the canonical minimum-directors rule:
    /// ```text
    /// defeasible min_directors
    ///   : IncorporationContext → ComplianceVerdict
    ///   := λ(ctx : IncorporationContext).
    ///        match director_count ctx return ComplianceVerdict with
    ///        | Zero => NonCompliant
    ///        | _    => Compliant
    /// ```
    fn min_directors_rule() -> Term {
        Term::Defeasible(DefeasibleRule {
            name: Ident::new("min_directors"),
            base_ty: Box::new(Term::pi(
                "ctx",
                constant("IncorporationContext"),
                constant("ComplianceVerdict"),
            )),
            base_body: Box::new(lam(
                "ctx",
                constant("IncorporationContext"),
                match_expr(
                    app(constant("director_count"), var("ctx", 0)),
                    constant("ComplianceVerdict"),
                    vec![
                        ctor_branch("Zero", constant("NonCompliant")),
                        wildcard_branch(constant("Compliant")),
                    ],
                ),
            )),
            exceptions: vec![],
            lattice: None,
        })
    }

    /// Build a rule that checks audit_status:
    /// ```text
    /// λ(ctx : IncorporationContext).
    ///   match audit_status ctx return ComplianceVerdict with
    ///   | AuditComplete => Compliant
    ///   | AuditDue      => Pending
    ///   | _             => NonCompliant
    /// ```
    fn audit_status_rule() -> Term {
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("audit_status"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    ctor_branch("AuditComplete", constant("Compliant")),
                    ctor_branch("AuditDue", constant("Pending")),
                    wildcard_branch(constant("NonCompliant")),
                ],
            ),
        )
    }

    /// Build a rule that checks a boolean accessor:
    /// ```text
    /// λ(ctx : IncorporationContext).
    ///   match all_identified ctx return ComplianceVerdict with
    ///   | True  => Compliant
    ///   | False => NonCompliant
    /// ```
    fn bool_accessor_rule() -> Term {
        lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("all_identified"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    ctor_branch("True", constant("Compliant")),
                    ctor_branch("False", constant("NonCompliant")),
                ],
            ),
        )
    }

    // ── Basic verdict evaluation ───────────────────────────────────────

    #[test]
    fn evaluate_bare_compliant() {
        let ctx = RuntimeContext::new();
        let result = evaluate(&constant("Compliant"), &ctx);
        assert_eq!(result.unwrap(), ComplianceVerdict::Compliant);
    }

    #[test]
    fn evaluate_bare_non_compliant() {
        let ctx = RuntimeContext::new();
        let result = evaluate(&constant("NonCompliant"), &ctx);
        assert_eq!(result.unwrap(), ComplianceVerdict::NonCompliant);
    }

    #[test]
    fn evaluate_bare_pending() {
        let ctx = RuntimeContext::new();
        let result = evaluate(&constant("Pending"), &ctx);
        assert_eq!(result.unwrap(), ComplianceVerdict::Pending);
    }

    // ── Minimum directors rule ─────────────────────────────────────────

    #[test]
    fn evaluate_min_directors_zero_is_non_compliant() {
        let rule = min_directors_rule();
        let mut ctx = RuntimeContext::new();
        ctx.insert("director_count", RuntimeValue::Nat(0));

        let result = evaluate(&rule, &ctx).unwrap();
        assert_eq!(result, ComplianceVerdict::NonCompliant);
    }

    #[test]
    fn evaluate_min_directors_one_is_compliant() {
        let rule = min_directors_rule();
        let mut ctx = RuntimeContext::new();
        ctx.insert("director_count", RuntimeValue::Nat(1));

        let result = evaluate(&rule, &ctx).unwrap();
        assert_eq!(result, ComplianceVerdict::Compliant);
    }

    #[test]
    fn evaluate_min_directors_many_is_compliant() {
        let rule = min_directors_rule();
        let mut ctx = RuntimeContext::new();
        ctx.insert("director_count", RuntimeValue::Nat(5));

        let result = evaluate(&rule, &ctx).unwrap();
        assert_eq!(result, ComplianceVerdict::Compliant);
    }

    // ── Tag accessor rule ──────────────────────────────────────────────

    #[test]
    fn evaluate_audit_complete_is_compliant() {
        let rule = audit_status_rule();
        let mut ctx = RuntimeContext::new();
        ctx.insert("audit_status", RuntimeValue::Tag("AuditComplete".into()));

        let result = evaluate(&rule, &ctx).unwrap();
        assert_eq!(result, ComplianceVerdict::Compliant);
    }

    #[test]
    fn evaluate_audit_due_is_pending() {
        let rule = audit_status_rule();
        let mut ctx = RuntimeContext::new();
        ctx.insert("audit_status", RuntimeValue::Tag("AuditDue".into()));

        let result = evaluate(&rule, &ctx).unwrap();
        assert_eq!(result, ComplianceVerdict::Pending);
    }

    #[test]
    fn evaluate_audit_overdue_is_non_compliant() {
        let rule = audit_status_rule();
        let mut ctx = RuntimeContext::new();
        ctx.insert("audit_status", RuntimeValue::Tag("AuditOverdue".into()));

        let result = evaluate(&rule, &ctx).unwrap();
        assert_eq!(result, ComplianceVerdict::NonCompliant);
    }

    // ── Boolean accessor rule ──────────────────────────────────────────

    #[test]
    fn evaluate_bool_true_is_compliant() {
        let rule = bool_accessor_rule();
        let mut ctx = RuntimeContext::new();
        ctx.insert("all_identified", RuntimeValue::Bool(true));

        let result = evaluate(&rule, &ctx).unwrap();
        assert_eq!(result, ComplianceVerdict::Compliant);
    }

    #[test]
    fn evaluate_bool_false_is_non_compliant() {
        let rule = bool_accessor_rule();
        let mut ctx = RuntimeContext::new();
        ctx.insert("all_identified", RuntimeValue::Bool(false));

        let result = evaluate(&rule, &ctx).unwrap();
        assert_eq!(result, ComplianceVerdict::NonCompliant);
    }

    // ── Defeasible rule with exceptions ────────────────────────────────

    #[test]
    fn evaluate_defeasible_base_when_no_exceptions_triggered() {
        // Base: NonCompliant (director_count = 0)
        // Exception (priority 10): if all_identified => Pending
        // With all_identified = false, exception is NOT triggered
        let rule = Term::Defeasible(DefeasibleRule {
            name: Ident::new("directors_with_exception"),
            base_ty: Box::new(Term::pi(
                "ctx",
                constant("IncorporationContext"),
                constant("ComplianceVerdict"),
            )),
            base_body: Box::new(lam(
                "ctx",
                constant("IncorporationContext"),
                match_expr(
                    app(constant("director_count"), var("ctx", 0)),
                    constant("ComplianceVerdict"),
                    vec![
                        ctor_branch("Zero", constant("NonCompliant")),
                        wildcard_branch(constant("Compliant")),
                    ],
                ),
            )),
            exceptions: vec![Exception {
                guard: Box::new(lam(
                    "ctx",
                    constant("IncorporationContext"),
                    match_expr(
                        app(constant("all_identified"), var("ctx", 0)),
                        constant("Bool"),
                        vec![
                            ctor_branch("True", constant("Compliant")),
                            ctor_branch("False", constant("NonCompliant")),
                        ],
                    ),
                )),
                body: Box::new(constant("Pending")),
                priority: Some(10),
                authority: None,
            }],
            lattice: None,
        });

        let mut ctx = RuntimeContext::new();
        ctx.insert("director_count", RuntimeValue::Nat(0));
        ctx.insert("all_identified", RuntimeValue::Bool(false));

        let result = evaluate(&rule, &ctx).unwrap();
        // Exception guard is NOT satisfied (all_identified = false => NonCompliant => false)
        // So base verdict wins: NonCompliant (0 directors)
        assert_eq!(result, ComplianceVerdict::NonCompliant);
    }

    #[test]
    fn evaluate_defeasible_exception_overrides_base() {
        // Base: NonCompliant (director_count = 0)
        // Exception (priority 10): if all_identified => Pending
        // With all_identified = true, exception IS triggered
        let rule = Term::Defeasible(DefeasibleRule {
            name: Ident::new("directors_with_exception"),
            base_ty: Box::new(Term::pi(
                "ctx",
                constant("IncorporationContext"),
                constant("ComplianceVerdict"),
            )),
            base_body: Box::new(lam(
                "ctx",
                constant("IncorporationContext"),
                match_expr(
                    app(constant("director_count"), var("ctx", 0)),
                    constant("ComplianceVerdict"),
                    vec![
                        ctor_branch("Zero", constant("NonCompliant")),
                        wildcard_branch(constant("Compliant")),
                    ],
                ),
            )),
            exceptions: vec![Exception {
                guard: Box::new(lam(
                    "ctx",
                    constant("IncorporationContext"),
                    match_expr(
                        app(constant("all_identified"), var("ctx", 0)),
                        constant("Bool"),
                        vec![
                            ctor_branch("True", constant("Compliant")),
                            ctor_branch("False", constant("NonCompliant")),
                        ],
                    ),
                )),
                body: Box::new(constant("Pending")),
                priority: Some(10),
                authority: None,
            }],
            lattice: None,
        });

        let mut ctx = RuntimeContext::new();
        ctx.insert("director_count", RuntimeValue::Nat(0));
        ctx.insert("all_identified", RuntimeValue::Bool(true));

        let result = evaluate(&rule, &ctx).unwrap();
        // Exception guard IS satisfied (all_identified = true => Compliant => true)
        // So exception verdict wins: Pending
        assert_eq!(result, ComplianceVerdict::Pending);
    }

    #[test]
    fn evaluate_defeasible_highest_priority_exception_wins() {
        // Base: NonCompliant
        // Exception 1 (priority 5): body = Pending
        // Exception 2 (priority 15): body = Compliant
        // Both guards are constant "Compliant" (always true)
        // Highest priority (15) wins => Compliant
        let rule = Term::Defeasible(DefeasibleRule {
            name: Ident::new("priority_test"),
            base_ty: Box::new(constant("ComplianceVerdict")),
            base_body: Box::new(constant("NonCompliant")),
            exceptions: vec![
                Exception {
                    guard: Box::new(constant("Compliant")),
                    body: Box::new(constant("Pending")),
                    priority: Some(5),
                    authority: None,
                },
                Exception {
                    guard: Box::new(constant("Compliant")),
                    body: Box::new(constant("Compliant")),
                    priority: Some(15),
                    authority: None,
                },
            ],
            lattice: None,
        });

        let ctx = RuntimeContext::new();
        let result = evaluate(&rule, &ctx).unwrap();
        assert_eq!(result, ComplianceVerdict::Compliant);
    }

    // ── Error cases ────────────────────────────────────────────────────

    #[test]
    fn evaluate_unknown_accessor_is_error() {
        let rule = lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("nonexistent_accessor"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![wildcard_branch(constant("Compliant"))],
            ),
        );
        let ctx = RuntimeContext::new();
        let result = evaluate(&rule, &ctx);
        assert!(result.is_err());
        match result.unwrap_err() {
            EvalError::UnknownAccessor { name } => {
                assert_eq!(name, "nonexistent_accessor");
            }
            other => panic!("expected UnknownAccessor, got: {:?}", other),
        }
    }

    #[test]
    fn evaluate_non_verdict_constant_is_error() {
        let ctx = RuntimeContext::new();
        let result = evaluate(&constant("SomeRandomConstant"), &ctx);
        assert!(result.is_err());
        match result.unwrap_err() {
            EvalError::NotAVerdict { .. } => {}
            other => panic!("expected NotAVerdict, got: {:?}", other),
        }
    }

    // ── Sanctions accessor ─────────────────────────────────────────────

    #[test]
    fn evaluate_sanctions_clear_is_compliant() {
        let rule = lam(
            "ctx",
            constant("IncorporationContext"),
            match_expr(
                app(constant("sanctions_check"), var("ctx", 0)),
                constant("ComplianceVerdict"),
                vec![
                    ctor_branch("Clear", constant("Compliant")),
                    wildcard_branch(constant("NonCompliant")),
                ],
            ),
        );

        let mut ctx = RuntimeContext::new();
        ctx.insert(
            "sanctions_check",
            RuntimeValue::SanctionsResult("Clear".into()),
        );

        let result = evaluate(&rule, &ctx).unwrap();
        assert_eq!(result, ComplianceVerdict::Compliant);
    }

    // ── Annotation stripping ───────────────────────────────────────────

    #[test]
    fn evaluate_strips_annotation() {
        let annotated = Term::annot(constant("Compliant"), constant("ComplianceVerdict"));
        let ctx = RuntimeContext::new();
        let result = evaluate(&annotated, &ctx).unwrap();
        assert_eq!(result, ComplianceVerdict::Compliant);
    }

    // ── RuntimeContext builder ──────────────────────────────────────────

    #[test]
    fn runtime_context_insert_and_get() {
        let mut ctx = RuntimeContext::new();
        ctx.insert("director_count", RuntimeValue::Nat(3));
        ctx.insert("audit_status", RuntimeValue::Tag("AuditComplete".into()));
        ctx.insert("all_identified", RuntimeValue::Bool(true));
        ctx.insert(
            "sanctions_check",
            RuntimeValue::SanctionsResult("Clear".into()),
        );

        assert_eq!(ctx.get("director_count"), Some(&RuntimeValue::Nat(3)));
        assert_eq!(
            ctx.get("audit_status"),
            Some(&RuntimeValue::Tag("AuditComplete".into()))
        );
        assert_eq!(
            ctx.get("all_identified"),
            Some(&RuntimeValue::Bool(true))
        );
        assert_eq!(ctx.get("nonexistent"), None);
    }
}
