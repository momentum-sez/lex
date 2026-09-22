//! Reference (term-reduction) evaluator for Lex compliance rules.
//!
//! **Status — reference/experimental, NOT the production verdict path.** This
//! module is a small term-reducer over the `Term` AST: given a Lex `Term`
//! (typically a `lambda (ctx : IncorporationContext). body` rule) and a
//! [`RuntimeContext`] mapping accessor names to concrete values, it reduces the
//! term to a [`ComplianceVerdict`]. It exists as a readable reference for how a
//! rule body reduces, and is referenced by the prelude/parser docs for that
//! purpose. It has no callers in the shipped pipeline.
//!
//! The production caveat/predicate evaluation path is
//! [`crate::predicate_runtime::evaluate`] (re-exported as
//! [`crate::evaluate_predicate`]), which evaluates a structured
//! `LexProposition` against a typed [`crate::predicate_runtime::EvalContext`]
//! and is the surface the runtime narrowing/caveat machinery consumes. Do not
//! route a production verdict through this module; route it through
//! `predicate_runtime`.
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
//!    branch, substituting its complete constructor payload, and evaluating the body.
//! 4. Reduce `Defeasible` by evaluating the base body, then each exception
//!    guard in priority order; the highest-priority satisfied exception wins.
//! 5. Recognize verdict constants (`Compliant`, `NonCompliant`, `Pending`)
//!    and return the corresponding [`ComplianceVerdict`].

use std::collections::BTreeMap;

use crate::ast::{Pattern, QualIdent, Term};
use crate::certificate::ComplianceVerdict;
use crate::typecheck::{instantiate_constructor_args, validate_evaluation_shape, TypeError};

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
///
/// Term payloads are owned `Box<Term>` values. Dereference a payload to recover
/// its complete term. Boxing keeps error returns small without discarding evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvalError {
    /// An accessor referenced by the rule is not present in the RuntimeContext.
    UnknownAccessor { name: String },

    /// The term reduced to a form that is not a recognized verdict constant.
    NotAVerdict { term: Box<Term> },

    /// Match expression had no matching branch for the scrutinee value.
    NoMatchingBranch { scrutinee: Box<Term> },

    /// The rule is not a lambda abstraction at the top level.
    NotALambda { term: Box<Term> },

    /// Substitution rejected a term outside its checked structural limits.
    Substitution { error: Box<TypeError> },

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
            Self::Substitution { error } => write!(f, "evaluation substitution failed: {error}"),
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
///
/// Constructor arities come from the fixture prelude. This entrypoint does not
/// accept custom constructor signatures or establish typing or certificate validity.
pub fn evaluate(term: &Term, ctx: &RuntimeContext) -> Result<ComplianceVerdict, EvalError> {
    validate_evaluation_shape(term).map_err(substitution_error)?;
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
    consume_step(depth, fuel)?;

    match term {
        // The outer rule lambda supplies the runtime context implicitly.
        Term::Lambda { body, .. } => eval_term(body, ctx, depth + 1, fuel),

        // ── Defeasible rule: evaluate base, then exceptions ────────────
        Term::Defeasible(rule) => {
            // Evaluate base body
            let base_verdict = eval_term(&rule.base_body, ctx, depth + 1, fuel)?;

            // Collect exceptions that are satisfied (guard evaluates to Compliant/True)
            // and pick the highest-priority one.
            let mut best_exception: Option<(u32, ComplianceVerdict)> = None;

            for exception in &rule.exceptions {
                // Propagate an unevaluable guard rather than silently treating
                // it as unsatisfied: a guard that cannot be evaluated is a fault
                // in the rule/context, not evidence that the exception does not
                // apply. Swallowing it would drop a legal defeasible exception.
                let guard_satisfied = eval_guard(&exception.guard, ctx, depth + 1, fuel)?;

                if guard_satisfied {
                    let exception_verdict = eval_term(&exception.body, ctx, depth + 1, fuel)?;
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

        _ => {
            let value = reduce_value(term, ctx, depth + 1, fuel)?.term;
            if let Term::Lambda { body, .. } = &value {
                return eval_term(body, ctx, depth + 1, fuel);
            }
            if let Term::Constant(name) = &value {
                if name.segments.len() == 1 {
                    match qual_ident_name(name) {
                        "Compliant" => return Ok(ComplianceVerdict::Compliant),
                        "NonCompliant" => return Ok(ComplianceVerdict::NonCompliant),
                        "Pending" => return Ok(ComplianceVerdict::Pending),
                        _ => {}
                    }
                }
            }
            Err(EvalError::NotAVerdict {
                term: Box::new(value),
            })
        }
    }
}

fn consume_step(depth: usize, fuel: &mut usize) -> Result<(), EvalError> {
    if depth > MAX_EVAL_DEPTH {
        return Err(EvalError::RecursionLimitExceeded);
    }
    *fuel = fuel
        .checked_sub(1)
        .ok_or(EvalError::ReductionLimitExceeded)?;
    Ok(())
}

/// Instantiate the complete source-order payload with the checker's bounded substitution.
fn instantiate(args: &[Term], body: &Term) -> Result<Term, EvalError> {
    instantiate_constructor_args(args, body).map_err(substitution_error)
}

fn substitution_error(error: Box<TypeError>) -> EvalError {
    match *error {
        TypeError::RecursionLimitExceeded => EvalError::RecursionLimitExceeded,
        TypeError::ReductionLimitExceeded | TypeError::SubstitutionBlowup { .. } => {
            EvalError::ReductionLimitExceeded
        }
        _ => EvalError::Substitution { error },
    }
}

/// Read payload arity from the same declarations used by the fixture checker.
fn constructor_arity(name: &QualIdent) -> Option<usize> {
    if !crate::prelude::is_prelude_constructor(&name.to_dotted()) {
        return None;
    }
    if crate::prelude::is_nat_constructor(&name.to_dotted()) {
        return Some(0);
    }
    static SIGNATURE: std::sync::LazyLock<crate::typecheck::Context> =
        std::sync::LazyLock::new(crate::prelude::legacy_fixture_prelude);
    let mut ty = SIGNATURE.lookup_constant(name)?;
    let mut arity = 0;
    while let Term::Pi { codomain, .. } = ty {
        arity += 1;
        ty = codomain;
    }
    Some(arity)
}

/// A runtime accessor supplies a concrete value even for an open tag family.
struct ReducedValue {
    term: Term,
    remaining_arguments: Option<usize>,
}

/// Reduce to a value without dropping constructor arguments or entering lambdas.
fn reduce_value(
    term: &Term,
    ctx: &RuntimeContext,
    depth: usize,
    fuel: &mut usize,
) -> Result<ReducedValue, EvalError> {
    consume_step(depth, fuel)?;
    match term {
        Term::App { func, arg } => {
            let func = reduce_value(func, ctx, depth + 1, fuel)?;
            if let Term::Lambda { body, .. } = &func.term {
                let body = instantiate(std::slice::from_ref(arg.as_ref()), body)?;
                return reduce_value(&body, ctx, depth + 1, fuel);
            }
            if func.remaining_arguments == Some(0) {
                return Err(EvalError::NotAVerdict {
                    term: Box::new(Term::app(func.term, arg.as_ref().clone())),
                });
            }
            if let Term::Constant(name) = &func.term {
                // Constructor syntax has priority over a colliding accessor name.
                if !crate::prelude::is_prelude_constructor(&name.to_dotted()) {
                    let value =
                        ctx.get(&name.to_dotted())
                            .ok_or_else(|| EvalError::UnknownAccessor {
                                name: name.to_dotted(),
                            })?;
                    let term = runtime_value_to_term(value);
                    if matches!(&term, Term::Constant(name) if matches!(constructor_arity(name), Some(1..)))
                    {
                        return Err(EvalError::NotAVerdict {
                            term: Box::new(term),
                        });
                    }
                    return Ok(ReducedValue {
                        term,
                        remaining_arguments: Some(0),
                    });
                }
            }
            let remaining_arguments = func.remaining_arguments.map(|arity| arity - 1);
            Ok(ReducedValue {
                term: Term::app(func.term, arg.as_ref().clone()),
                remaining_arguments,
            })
        }
        Term::Let { val, body, .. } => {
            let body = instantiate(std::slice::from_ref(val.as_ref()), body)?;
            reduce_value(&body, ctx, depth + 1, fuel)
        }
        Term::Annot { term, .. } => reduce_value(term, ctx, depth + 1, fuel),
        Term::Match {
            scrutinee,
            branches,
            ..
        } => {
            // Resolve accessor errors before selecting even a wildcard branch.
            let value = reduce_value(scrutinee, ctx, depth + 1, fuel)?;
            if matches!(value.remaining_arguments, Some(1..)) {
                return Err(EvalError::NotAVerdict {
                    term: Box::new(value.term),
                });
            }
            let mut head = &value.term;
            let mut args = Vec::new();
            while let Term::App { func, arg } = head {
                consume_step(depth, fuel)?;
                args.push(arg.as_ref().clone());
                head = func;
            }
            args.reverse();
            for branch in branches {
                match &branch.pattern {
                    Pattern::Wildcard => return reduce_value(&branch.body, ctx, depth + 1, fuel),
                    Pattern::Constructor {
                        constructor,
                        binders,
                    } => {
                        if value.remaining_arguments != Some(0) {
                            return Err(EvalError::NotAVerdict {
                                term: Box::new(value.term),
                            });
                        }
                        let Term::Constant(name) = head else {
                            // An unresolved earlier arm prevents a later wildcard decision.
                            return Err(EvalError::NotAVerdict {
                                term: Box::new(value.term),
                            });
                        };
                        if constructor.name == *name {
                            if binders.len() != args.len() {
                                return Err(EvalError::NoMatchingBranch {
                                    scrutinee: scrutinee.clone(),
                                });
                            }
                            let body = instantiate(&args, &branch.body)?;
                            return reduce_value(&body, ctx, depth + 1, fuel);
                        }
                    }
                }
            }
            Err(EvalError::NoMatchingBranch {
                scrutinee: scrutinee.clone(),
            })
        }
        Term::Defeasible(_) => {
            let name = match eval_term(term, ctx, depth + 1, fuel)? {
                ComplianceVerdict::Compliant => "Compliant",
                ComplianceVerdict::NonCompliant => "NonCompliant",
                ComplianceVerdict::Pending => "Pending",
            };
            Ok(ReducedValue {
                term: Term::Constant(QualIdent::simple(name)),
                remaining_arguments: Some(0),
            })
        }
        Term::Constant(_)
        | Term::Var { .. }
        | Term::Sort(_)
        | Term::Lambda { .. }
        | Term::Pi { .. } => Ok(ReducedValue {
            remaining_arguments: match term {
                Term::Constant(name) => constructor_arity(name),
                _ => None,
            },
            term: term.clone(),
        }),
        _ => Err(EvalError::NotAVerdict {
            term: Box::new(term.clone()),
        }),
    }
}

fn eval_to_constant(
    term: &Term,
    ctx: &RuntimeContext,
    depth: usize,
    fuel: &mut usize,
) -> Result<String, EvalError> {
    let value = reduce_value(term, ctx, depth, fuel)?;
    match value.term {
        Term::Constant(name)
            if value.remaining_arguments == Some(0) && name.segments.len() == 1 =>
        {
            Ok(qual_ident_name(&name).to_string())
        }
        term => Err(EvalError::NotAVerdict {
            term: Box::new(term),
        }),
    }
}

/// Evaluate a defeasible exception guard.
///
/// Guards are propositions. In the admissible fragment, guards are typically
/// boolean-valued or constructor-match expressions. We evaluate them and
/// interpret the result:
/// - `Compliant` / `True` / `Clear` => satisfied (true)
/// - `NonCompliant` / `False` => not satisfied (false)
///
/// A guard that reduces to a recognized form (verdict or known constant) yields
/// a definite `Ok(true)`/`Ok(false)`. A guard that cannot be evaluated under
/// **either** interpretation is a real error and is **propagated**, not
/// silently read as "exception not satisfied": silently swallowing a guard
/// failure would turn a malformed defeasible exception into one that never
/// fires, dropping a legal exception without trace.
fn eval_guard(
    guard: &Term,
    ctx: &RuntimeContext,
    depth: usize,
    fuel: &mut usize,
) -> Result<bool, EvalError> {
    // First interpretation: the guard reduces to a verdict.
    match eval_term(guard, ctx, depth, fuel) {
        Ok(ComplianceVerdict::Compliant) => Ok(true),
        Ok(ComplianceVerdict::NonCompliant) => Ok(false),
        Ok(ComplianceVerdict::Pending) => Ok(false),
        Err(verdict_err) => {
            // Second interpretation: the guard reduces to a Bool/constant name
            // (e.g. a guard written `all_identified ctx` returning `True`).
            // Share the fuel budget to bound total work across guards. Only if
            // BOTH interpretations fail do we surface an error — the verdict
            // interpretation's error is the more specific one to report.
            match eval_to_constant(guard, ctx, depth, fuel) {
                Ok(name) => match name.as_str() {
                    "True" | "Clear" | "Compliant" => Ok(true),
                    // A recognized-but-false constant (`False`, `NonCompliant`,
                    // a non-satisfying status tag) is a definite not-satisfied.
                    _ => Ok(false),
                },
                Err(_) => Err(verdict_err),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Extract the simple name from a QualIdent.
fn qual_ident_name(qi: &QualIdent) -> &str {
    qi.segments.last().map(|s| s.as_str()).unwrap_or("")
}

/// Prefix for the non-zero-natural marker constructor name.
///
/// There is no prelude constructor for non-zero naturals, so a positive `Nat`
/// is encoded as `"<prefix><value>"` (e.g. `__NonZeroNat:5`). Encoding the
/// concrete value — rather than collapsing every positive natural onto a single
/// sentinel — keeps the value recoverable, so a downstream comparison can tell
/// `1` from `5`. The reserved prefix cannot collide with an authored
/// constructor (it is not lexable as a single identifier) and never matches the
/// `Zero` constructor, so a positive natural still falls through to wildcard
/// branches the same way the old single sentinel did.
///
/// This is the SAME marker the parser's Nat-literal pattern lowering produces
/// (`crate::prelude::encode_non_zero_nat_marker`) and the admissibility checker
/// classifies as a `Nat` value-member, so a `| <n> =>` pattern matches the
/// evaluated scrutinee by exact constructor-name equality. The constant is
/// re-exported from `crate::prelude` to keep one source of truth for the shape.
const NON_ZERO_NAT_PREFIX: &str = crate::prelude::NON_ZERO_NAT_PREFIX;

/// Encode a non-zero natural as its value-preserving marker constructor name.
fn encode_non_zero_nat(n: u64) -> String {
    format!("{NON_ZERO_NAT_PREFIX}{n}")
}

/// Decode a value-preserving non-zero-natural marker name back to its value.
/// Returns `None` if `name` is not a non-zero-natural marker.
#[cfg(test)]
fn decode_non_zero_nat(name: &str) -> Option<u64> {
    name.strip_prefix(NON_ZERO_NAT_PREFIX)
        .and_then(|rest| rest.parse::<u64>().ok())
}

/// Convert a RuntimeValue to a Lex Term constant.
fn runtime_value_to_term(val: &RuntimeValue) -> Term {
    match val {
        RuntimeValue::Nat(0) => Term::Constant(QualIdent::simple("Zero")),
        // Non-zero Nat: encode the concrete value into the marker name so it
        // survives the round-trip (see `NON_ZERO_NAT_PREFIX`). It still does
        // not match the `Zero` constructor, so it falls through to wildcards.
        RuntimeValue::Nat(n) => Term::Constant(QualIdent::simple(&encode_non_zero_nat(*n))),
        RuntimeValue::Bool(true) => Term::Constant(QualIdent::simple("True")),
        RuntimeValue::Bool(false) => Term::Constant(QualIdent::simple("False")),
        RuntimeValue::Tag(name) => Term::Constant(QualIdent::simple(name)),
        RuntimeValue::SanctionsResult(name) => Term::Constant(QualIdent::simple(name)),
    }
}

/// Convert a RuntimeValue to a constructor name string for pattern matching.
#[cfg(test)]
fn runtime_value_to_constant_name(val: &RuntimeValue) -> String {
    match val {
        RuntimeValue::Nat(0) => "Zero".to_string(),
        RuntimeValue::Nat(n) => encode_non_zero_nat(*n),
        RuntimeValue::Bool(true) => "True".to_string(),
        RuntimeValue::Bool(false) => "False".to_string(),
        RuntimeValue::Tag(name) => name.clone(),
        RuntimeValue::SanctionsResult(name) => name.clone(),
    }
}

/// Convert a constant name (from `eval_to_constant`) back to a [`RuntimeValue`].
///
/// Recognizes the well-known constructor names produced by
/// [`runtime_value_to_constant_name`]. The non-zero-natural marker round-trips
/// its concrete value. Returns `None` for any other name; the caller treats a
/// `None` as "not a recognized runtime value" and does NOT mint a `Tag` from
/// it (an unknown token is not silently coerced into a valid value).
#[cfg(test)]
fn constant_name_to_runtime_value(name: &str) -> Option<RuntimeValue> {
    match name {
        "Zero" => Some(RuntimeValue::Nat(0)),
        "True" => Some(RuntimeValue::Bool(true)),
        "False" => Some(RuntimeValue::Bool(false)),
        "Clear" | "Hit" | "Pending" | "Compliant" | "NonCompliant" => {
            Some(RuntimeValue::Tag(name.to_string()))
        }
        _ => decode_non_zero_nat(name).map(RuntimeValue::Nat),
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
            applies_to: None,
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
            applies_to: None,
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
            applies_to: None,
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
            applies_to: None,
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
        let input = constant("SomeRandomConstant");
        let error = evaluate(&input, &ctx).unwrap_err();
        assert_eq!(
            error.to_string(),
            "term did not reduce to a compliance verdict"
        );
        match error {
            EvalError::NotAVerdict { term } => assert_eq!(*term, input),
            other => panic!("expected NotAVerdict, got: {:?}", other),
        }
    }

    #[test]
    fn missing_branch_preserves_original_scrutinee() {
        let scrutinee = app(constant("audit_status"), var("ctx", 0));
        let rule = match_expr(scrutinee.clone(), constant("ComplianceVerdict"), vec![]);
        let mut ctx = RuntimeContext::new();
        ctx.insert("audit_status", RuntimeValue::Tag("AuditComplete".into()));
        let error = evaluate(&rule, &ctx).unwrap_err();
        assert_eq!(error.to_string(), "no matching branch in match expression");
        match error {
            EvalError::NoMatchingBranch { scrutinee: actual } => {
                assert_eq!(*actual, scrutinee);
            }
            other => panic!("expected NoMatchingBranch, got: {:?}", other),
        }
    }

    #[test]
    fn term_errors_preserve_owned_payloads_and_clone_equality() {
        let input = constant("RetainedEvidence");
        let errors = [
            EvalError::NotAVerdict {
                term: Box::new(input.clone()),
            },
            EvalError::NoMatchingBranch {
                scrutinee: Box::new(input.clone()),
            },
            EvalError::NotALambda {
                term: Box::new(input.clone()),
            },
        ];
        let messages = [
            "term did not reduce to a compliance verdict",
            "no matching branch in match expression",
            "rule is not a lambda abstraction",
        ];
        for (error, message) in errors.into_iter().zip(messages) {
            let cloned = error.clone();
            assert_eq!(error, cloned);
            assert_eq!(error.to_string(), message);
            drop(error);
            match cloned {
                EvalError::NotAVerdict { term } | EvalError::NotALambda { term } => {
                    assert_eq!(*term, input);
                }
                EvalError::NoMatchingBranch { scrutinee } => assert_eq!(*scrutinee, input),
                other => panic!("unexpected error: {:?}", other),
            }
        }
        assert!(std::mem::size_of::<EvalError>() <= 64);
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
        assert_eq!(ctx.get("all_identified"), Some(&RuntimeValue::Bool(true)));
        assert_eq!(ctx.get("nonexistent"), None);
    }

    // ── Non-zero Nat value preservation (LEX-1 fix i) ──────────────────
    // WHY: the old encoding collapsed every positive natural onto one sentinel
    // ("__NonZeroNat"), so a comparison could not tell 1 from 5 — a `>= 2`
    // threshold would treat them identically. The marker now carries the value.

    #[test]
    fn non_zero_nat_marker_round_trips_distinct_values() {
        // Distinct positive naturals encode to distinct marker names...
        let one = runtime_value_to_constant_name(&RuntimeValue::Nat(1));
        let five = runtime_value_to_constant_name(&RuntimeValue::Nat(5));
        assert_ne!(one, five, "1 and 5 must not collapse to the same marker");

        // ...and decode back to the original value (not a fixed sentinel).
        assert_eq!(
            constant_name_to_runtime_value(&one),
            Some(RuntimeValue::Nat(1))
        );
        assert_eq!(
            constant_name_to_runtime_value(&five),
            Some(RuntimeValue::Nat(5))
        );
    }

    #[test]
    fn non_zero_nat_marker_never_matches_zero() {
        // The value-carrying marker must still NOT equal the `Zero`
        // constructor, so positive naturals fall through to wildcard branches.
        assert_ne!(
            runtime_value_to_constant_name(&RuntimeValue::Nat(7)),
            "Zero"
        );
    }

    #[test]
    fn positive_nat_falls_through_zero_branch_to_wildcard() {
        // End-to-end through the accessor path (`match director_count ctx`):
        // a positive natural (3) must NOT match the `Zero` constructor and so
        // hits the wildcard => Compliant; Nat(0) hits `Zero` => NonCompliant.
        // The value-carrying marker preserves this fall-through behavior.
        let rule = lam(
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
        );

        let mut ctx_three = RuntimeContext::new();
        ctx_three.insert("director_count", RuntimeValue::Nat(3));
        assert_eq!(
            evaluate(&rule, &ctx_three).unwrap(),
            ComplianceVerdict::Compliant,
        );

        let mut ctx_zero = RuntimeContext::new();
        ctx_zero.insert("director_count", RuntimeValue::Nat(0));
        assert_eq!(
            evaluate(&rule, &ctx_zero).unwrap(),
            ComplianceVerdict::NonCompliant,
        );
    }

    // ── Constant catch-all is not Tag-minting (LEX-1 fix iii) ──────────
    // WHY: the old catch-all turned ANY unknown token into a valid Tag, so a
    // typo or stray constant silently became a legitimate runtime value.

    #[test]
    fn unknown_constant_name_resolves_to_none_not_tag() {
        // A name that is neither a known constant nor a non-zero-nat marker is
        // unrecognized; it must NOT be minted into a Tag.
        assert_eq!(constant_name_to_runtime_value("TotallyUnknownToken"), None);
        // Known constants still resolve.
        assert_eq!(
            constant_name_to_runtime_value("True"),
            Some(RuntimeValue::Bool(true))
        );
        assert_eq!(
            constant_name_to_runtime_value("Zero"),
            Some(RuntimeValue::Nat(0))
        );
    }

    // ── Guard error propagation (LEX-1 fix ii) ─────────────────────────
    // WHY: the old eval_guard mapped every guard failure to Ok(false), silently
    // turning a malformed defeasible exception into one that never fires —
    // dropping a legal exception with no trace. An unevaluable guard must error.

    #[test]
    fn defeasible_guard_unknown_accessor_propagates_error() {
        // Base: Compliant. Exception guard references an accessor that is not in
        // the context AND cannot be read as a constant — it must surface as an
        // error, not silently leave the exception un-triggered.
        let rule = Term::Defeasible(DefeasibleRule {
            name: Ident::new("guard_failure"),
            base_ty: Box::new(constant("ComplianceVerdict")),
            base_body: Box::new(constant("Compliant")),
            exceptions: vec![Exception {
                guard: Box::new(lam(
                    "ctx",
                    constant("IncorporationContext"),
                    app(constant("missing_accessor"), var("ctx", 0)),
                )),
                body: Box::new(constant("NonCompliant")),
                priority: Some(10),
                authority: None,
            }],
            lattice: None,
            applies_to: None,
        });

        let ctx = RuntimeContext::new();
        let result = evaluate(&rule, &ctx);
        assert!(
            result.is_err(),
            "an unevaluable guard must propagate, not be swallowed as not-satisfied",
        );
        match result.unwrap_err() {
            EvalError::UnknownAccessor { name } => assert_eq!(name, "missing_accessor"),
            other => panic!("expected UnknownAccessor, got: {:?}", other),
        }
    }

    #[test]
    fn defeasible_guard_recognized_false_constant_stays_unsatisfied() {
        // Counterpart to the propagation test: a guard that DOES evaluate to a
        // recognized not-satisfied form (NonCompliant) is a definite false and
        // must NOT error — the base verdict stands.
        let rule = Term::Defeasible(DefeasibleRule {
            name: Ident::new("guard_false"),
            base_ty: Box::new(constant("ComplianceVerdict")),
            base_body: Box::new(constant("Compliant")),
            exceptions: vec![Exception {
                guard: Box::new(constant("NonCompliant")),
                body: Box::new(constant("Pending")),
                priority: Some(10),
                authority: None,
            }],
            lattice: None,
            applies_to: None,
        });

        let ctx = RuntimeContext::new();
        assert_eq!(evaluate(&rule, &ctx).unwrap(), ComplianceVerdict::Compliant,);
    }
}
