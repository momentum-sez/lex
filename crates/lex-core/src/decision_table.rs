//! Decision table compiler for Lex AST.
//!
//! Provides a tabular authoring surface for compliance rules that compiles
//! to the canonical Lex `Term` AST. The T1 agent observed that ~90% of rules
//! in production are decision tables expressed as `defeasible lambda match`
//! — this module lets authors write those rules as structured data (YAML/JSON)
//! instead of lambda calculus syntax.
//!
//! **This is a compilation layer, not a replacement.** The Lex AST remains
//! canonical. Decision tables compile *to* it; they do not extend or modify it.

use crate::ast::{Branch, Constructor, DefeasibleRule, Exception, Ident, Pattern, QualIdent, Term};
use serde::{Deserialize, Serialize};

// ═══════════════════════════════════════════════════════════════════════
// Decision table types
// ═══════════════════════════════════════════════════════════════════════

/// A decision table: a set of rules that map conditions on a context type
/// to compliance verdicts. Compiles to a defeasible Lex `Term`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecisionTable {
    /// Human-readable rule name (becomes the DefeasibleRule name).
    pub name: String,
    /// Jurisdiction code (e.g., "sc" for Seychelles).
    pub jurisdiction: String,
    /// Legal citation (e.g., "IBC Act 2016 s.66").
    pub legal_basis: String,
    /// The context type the lambda binds (e.g., "IncorporationContext").
    pub context_type: String,
    /// Ordered rules. First matching rule wins at each priority level;
    /// higher priority rules override lower ones (defeasibility).
    pub rules: Vec<DecisionRule>,
}

/// A single row in the decision table.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecisionRule {
    /// The condition that must hold for this rule to fire.
    pub condition: Condition,
    /// The compliance verdict: "Compliant", "NonCompliant", or "Pending".
    pub verdict: String,
    /// Priority for defeasibility ordering. Higher priority rules can
    /// override lower priority rules (the `unless` mechanism in Lex).
    pub priority: u32,
}

/// A condition in a decision rule. Conditions are compiled to Lex `Match`
/// branches with constructor patterns.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Condition {
    /// Field equals a constructor/literal value.
    /// Compiles to: `match ctx.field with | value => ...`
    Equals {
        /// Dot-separated accessor on the context (e.g., "director_count").
        accessor: String,
        /// The value to match (constructor name or integer literal).
        value: String,
    },
    /// Field is greater than a numeric threshold.
    /// For integer fields, compiles to a match with the threshold as a
    /// literal arm returning NonCompliant and wildcard returning Compliant.
    GreaterThan {
        /// Dot-separated accessor.
        accessor: String,
        /// The threshold value.
        threshold: i64,
    },
    /// Field is less than a numeric threshold.
    LessThan {
        /// Dot-separated accessor.
        accessor: String,
        /// The threshold value.
        threshold: i64,
    },
    /// Field accessor is the boolean True constructor.
    IsTrue {
        /// Dot-separated accessor.
        accessor: String,
    },
    /// Field accessor is the boolean False constructor.
    IsFalse {
        /// Dot-separated accessor.
        accessor: String,
    },
    /// All sub-conditions must hold.
    And(Vec<Condition>),
    /// At least one sub-condition must hold.
    Or(Vec<Condition>),
    /// Negation of a condition.
    Not(Box<Condition>),
    /// Always matches (wildcard / default row).
    Always,
}

// ═══════════════════════════════════════════════════════════════════════
// Compilation errors
// ═══════════════════════════════════════════════════════════════════════

/// Maximum threshold value for `GreaterThan`/`LessThan` conditions.
/// Prevents resource exhaustion from unbounded branch enumeration.
pub const MAX_THRESHOLD: i64 = 10_000;

/// Errors that can occur during decision table compilation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompileError {
    /// No rules in the table.
    EmptyTable,
    /// Invalid verdict string (must be Compliant/NonCompliant/Pending).
    InvalidVerdict(String),
    /// An accessor path is empty.
    EmptyAccessor,
    /// A threshold exceeds `MAX_THRESHOLD`, which would cause resource exhaustion.
    ThresholdTooLarge(i64),
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileError::EmptyTable => write!(f, "decision table has no rules"),
            CompileError::InvalidVerdict(v) => {
                write!(f, "invalid verdict '{v}': expected Compliant, NonCompliant, or Pending")
            }
            CompileError::EmptyAccessor => write!(f, "accessor path is empty"),
            CompileError::ThresholdTooLarge(t) => {
                write!(f, "threshold {t} exceeds maximum allowed value of {MAX_THRESHOLD}")
            }
        }
    }
}

impl std::error::Error for CompileError {}

// ═══════════════════════════════════════════════════════════════════════
// Compilation: DecisionTable → Term
// ═══════════════════════════════════════════════════════════════════════

/// Compile a decision table to a Lex AST `Term`.
///
/// The compilation strategy:
///
/// 1. Group rules by priority level.
/// 2. The lowest-priority group becomes the base rule body: a `Lambda`
///    wrapping a `Match` expression over the context accessor.
/// 3. Higher-priority groups become `Exception`s on the `DefeasibleRule`,
///    implementing Lex defeasibility (the `unless` mechanism).
///
/// For a single-priority table (the common case), this produces:
/// ```text
/// defeasible <name>
///   lambda (ctx : <context_type>).
///     match ctx.<accessor> return ComplianceVerdict with
///     | <value1> => <verdict1>
///     | <value2> => <verdict2>
///     | ...
///   priority <p>
/// end
/// ```
pub fn compile_table(table: &DecisionTable) -> Result<Term, CompileError> {
    if table.rules.is_empty() {
        return Err(CompileError::EmptyTable);
    }

    // Validate all verdicts up front.
    for rule in &table.rules {
        validate_verdict(&rule.verdict)?;
        validate_condition(&rule.condition)?;
    }

    // Partition rules by priority. Lower priority = base rule, higher = exceptions.
    let min_priority = table.rules.iter().map(|r| r.priority).min().unwrap_or(0);

    let base_rules: Vec<&DecisionRule> = table
        .rules
        .iter()
        .filter(|r| r.priority == min_priority)
        .collect();
    let exception_rules: Vec<&DecisionRule> = table
        .rules
        .iter()
        .filter(|r| r.priority > min_priority)
        .collect();

    // Build the base body: lambda (ctx : ContextType). match ...
    let base_body = compile_rules_to_lambda(&table.context_type, &base_rules);

    // Build exceptions from higher-priority rules.
    let exceptions = compile_exceptions(&table.context_type, &exception_rules);

    Ok(Term::Defeasible(DefeasibleRule {
        name: Ident::new(&table.name),
        base_ty: Box::new(Term::Constant(QualIdent::simple("ComplianceVerdict"))),
        base_body: Box::new(base_body),
        exceptions,
        lattice: None,
    }))
}

// ═══════════════════════════════════════════════════════════════════════
// Internal helpers
// ═══════════════════════════════════════════════════════════════════════

fn validate_verdict(verdict: &str) -> Result<(), CompileError> {
    match verdict {
        "Compliant" | "NonCompliant" | "Pending" => Ok(()),
        _ => Err(CompileError::InvalidVerdict(verdict.to_string())),
    }
}

fn validate_condition(condition: &Condition) -> Result<(), CompileError> {
    match condition {
        Condition::Equals { accessor, .. }
        | Condition::IsTrue { accessor }
        | Condition::IsFalse { accessor } => {
            if accessor.is_empty() {
                return Err(CompileError::EmptyAccessor);
            }
            Ok(())
        }
        Condition::GreaterThan { accessor, threshold } => {
            if accessor.is_empty() {
                return Err(CompileError::EmptyAccessor);
            }
            if *threshold > MAX_THRESHOLD {
                return Err(CompileError::ThresholdTooLarge(*threshold));
            }
            Ok(())
        }
        Condition::LessThan { accessor, threshold } => {
            if accessor.is_empty() {
                return Err(CompileError::EmptyAccessor);
            }
            if *threshold > MAX_THRESHOLD {
                return Err(CompileError::ThresholdTooLarge(*threshold));
            }
            Ok(())
        }
        Condition::And(subs) | Condition::Or(subs) => {
            for sub in subs {
                validate_condition(sub)?;
            }
            Ok(())
        }
        Condition::Not(inner) => validate_condition(inner),
        Condition::Always => Ok(()),
    }
}

/// Build the accessor term: `ctx.field` as an `App(Constant("field"), Var("ctx"))`.
///
/// For a dot-path like "registered_agent.csp_license_status", this nests:
/// `App(Constant("csp_license_status"), App(Constant("registered_agent"), Var("ctx")))`.
fn build_accessor(binder_name: &str, accessor: &str) -> Term {
    let parts: Vec<&str> = accessor.split('.').collect();
    let mut term = Term::var(binder_name, 0);
    for part in &parts {
        term = Term::app(Term::constant(part), term);
    }
    term
}

/// Build a verdict term: `Constant("Compliant")` etc.
fn verdict_term(verdict: &str) -> Term {
    Term::Constant(QualIdent::simple(verdict))
}

/// Compile a condition into match branches for a single-accessor match.
/// Returns `(scrutinee, branches)`.
fn compile_condition_to_branches(
    binder_name: &str,
    condition: &Condition,
    verdict: &str,
) -> (Term, Vec<Branch>) {
    match condition {
        Condition::Equals { accessor, value } => {
            let scrutinee = build_accessor(binder_name, accessor);
            // Try parsing value as integer for IntLit patterns.
            let pattern = if let Ok(n) = value.parse::<i64>() {
                // Integer literal pattern: | 0 => ...
                Pattern::Constructor {
                    constructor: Constructor::new(QualIdent::simple(&n.to_string())),
                    binders: vec![],
                }
            } else {
                // Constructor pattern: | SomeValue => ...
                Pattern::Constructor {
                    constructor: Constructor::new(QualIdent::simple(value)),
                    binders: vec![],
                }
            };

            let branches = vec![
                Branch {
                    pattern,
                    body: verdict_term(verdict),
                },
                // Wildcard fallback: opposite verdict.
                Branch {
                    pattern: Pattern::Wildcard,
                    body: verdict_term(&opposite_verdict(verdict)),
                },
            ];
            (scrutinee, branches)
        }
        Condition::GreaterThan {
            accessor,
            threshold,
        } => {
            // match ctx.field with | 0 => NonCompliant | ... | threshold => NonCompliant | _ => verdict
            // For threshold-based rules, we enumerate values up to the threshold
            // as the opposite verdict, wildcard catches the rest.
            let scrutinee = build_accessor(binder_name, accessor);
            let mut branches = Vec::new();
            for i in 0..=*threshold {
                branches.push(Branch {
                    pattern: Pattern::Constructor {
                        constructor: Constructor::new(QualIdent::simple(&i.to_string())),
                        binders: vec![],
                    },
                    body: verdict_term(&opposite_verdict(verdict)),
                });
            }
            branches.push(Branch {
                pattern: Pattern::Wildcard,
                body: verdict_term(verdict),
            });
            (scrutinee, branches)
        }
        Condition::LessThan {
            accessor,
            threshold,
        } => {
            let scrutinee = build_accessor(binder_name, accessor);
            let mut branches = Vec::new();
            // Values 0..threshold-1 match (get the verdict).
            for i in 0..*threshold {
                branches.push(Branch {
                    pattern: Pattern::Constructor {
                        constructor: Constructor::new(QualIdent::simple(&i.to_string())),
                        binders: vec![],
                    },
                    body: verdict_term(verdict),
                });
            }
            branches.push(Branch {
                pattern: Pattern::Wildcard,
                body: verdict_term(&opposite_verdict(verdict)),
            });
            (scrutinee, branches)
        }
        Condition::IsTrue { accessor } => {
            let scrutinee = build_accessor(binder_name, accessor);
            let branches = vec![
                Branch {
                    pattern: Pattern::Constructor {
                        constructor: Constructor::new(QualIdent::simple("True")),
                        binders: vec![],
                    },
                    body: verdict_term(verdict),
                },
                Branch {
                    pattern: Pattern::Wildcard,
                    body: verdict_term(&opposite_verdict(verdict)),
                },
            ];
            (scrutinee, branches)
        }
        Condition::IsFalse { accessor } => {
            let scrutinee = build_accessor(binder_name, accessor);
            let branches = vec![
                Branch {
                    pattern: Pattern::Constructor {
                        constructor: Constructor::new(QualIdent::simple("False")),
                        binders: vec![],
                    },
                    body: verdict_term(verdict),
                },
                Branch {
                    pattern: Pattern::Wildcard,
                    body: verdict_term(&opposite_verdict(verdict)),
                },
            ];
            (scrutinee, branches)
        }
        Condition::Always => {
            // Always condition: just return the verdict directly (no match needed).
            // We use a trivial match on the binder itself with a wildcard.
            let scrutinee = Term::var(binder_name, 0);
            let branches = vec![Branch {
                pattern: Pattern::Wildcard,
                body: verdict_term(verdict),
            }];
            (scrutinee, branches)
        }
        Condition::And(subs) if subs.is_empty() => {
            // Empty And = always true.
            let scrutinee = Term::var(binder_name, 0);
            let branches = vec![Branch {
                pattern: Pattern::Wildcard,
                body: verdict_term(verdict),
            }];
            (scrutinee, branches)
        }
        Condition::Or(subs) if subs.is_empty() => {
            // Empty Or = always false.
            let scrutinee = Term::var(binder_name, 0);
            let branches = vec![Branch {
                pattern: Pattern::Wildcard,
                body: verdict_term(&opposite_verdict(verdict)),
            }];
            (scrutinee, branches)
        }
        // For compound conditions (And/Or/Not), we compile to nested matches.
        Condition::And(subs) => {
            // And(A, B): compile A's match; in A's matching branch, nest B's
            // compiled match. Non-matching branches return opposite verdict.
            // Build inside-out: the innermost check is the last sub-condition.
            let opposite = opposite_verdict(verdict);
            let mut body = verdict_term(verdict);
            for sub in subs.iter().rev() {
                let (scrutinee, sub_branches) =
                    compile_condition_to_branches(binder_name, sub, verdict);
                // Replace the verdict in matching branches with the nested body,
                // and keep opposite-verdict branches as-is.
                let verdict_t = verdict_term(verdict);
                let nested_branches: Vec<Branch> = sub_branches
                    .into_iter()
                    .map(|b| {
                        if b.body == verdict_t {
                            Branch {
                                pattern: b.pattern,
                                body: body.clone(),
                            }
                        } else {
                            Branch {
                                pattern: b.pattern,
                                body: verdict_term(&opposite),
                            }
                        }
                    })
                    .collect();
                body = Term::match_expr(
                    scrutinee,
                    Term::Constant(QualIdent::simple("ComplianceVerdict")),
                    nested_branches,
                );
            }
            // Wrap in a trivial scrutinee so the return type is consistent.
            let scrutinee = Term::var(binder_name, 0);
            let branches = vec![Branch {
                pattern: Pattern::Wildcard,
                body,
            }];
            (scrutinee, branches)
        }
        Condition::Or(subs) => {
            // Or(A, B): compile A's match; in A's non-matching (wildcard)
            // branch, nest B's compiled match. Matching branches return verdict.
            // Build inside-out: the innermost check is the last sub-condition.
            let opposite = opposite_verdict(verdict);
            let mut fallback = verdict_term(&opposite);
            for sub in subs.iter().rev() {
                let (scrutinee, sub_branches) =
                    compile_condition_to_branches(binder_name, sub, verdict);
                // In non-matching branches (those returning opposite verdict),
                // substitute the nested fallback to try the next condition.
                let opposite_t = verdict_term(&opposite);
                let nested_branches: Vec<Branch> = sub_branches
                    .into_iter()
                    .map(|b| {
                        if b.body == opposite_t {
                            Branch {
                                pattern: b.pattern,
                                body: fallback.clone(),
                            }
                        } else {
                            b
                        }
                    })
                    .collect();
                fallback = Term::match_expr(
                    scrutinee,
                    Term::Constant(QualIdent::simple("ComplianceVerdict")),
                    nested_branches,
                );
            }
            let scrutinee = Term::var(binder_name, 0);
            let branches = vec![Branch {
                pattern: Pattern::Wildcard,
                body: fallback,
            }];
            (scrutinee, branches)
        }
        Condition::Not(inner) => {
            // Negate: swap verdict and opposite in the inner compilation.
            let opposite = opposite_verdict(verdict);
            compile_condition_to_branches(binder_name, inner, &opposite)
        }
    }
}

/// Compile a set of rules at the same priority into a lambda + match body.
fn compile_rules_to_lambda(context_type: &str, rules: &[&DecisionRule]) -> Term {
    let binder = "ctx";

    if rules.len() == 1 {
        // Single rule: straightforward lambda + match.
        let rule = rules[0];
        let (scrutinee, branches) =
            compile_condition_to_branches(binder, &rule.condition, &rule.verdict);
        let match_term = Term::match_expr(
            scrutinee,
            Term::Constant(QualIdent::simple("ComplianceVerdict")),
            branches,
        );
        Term::lam(binder, Term::constant(context_type), match_term)
    } else {
        // Multiple rules at same priority: compile to sequential match arms.
        // Each rule becomes a branch. Rules are evaluated in order.
        let mut all_branches = Vec::new();
        for rule in rules {
            let (_, branches) =
                compile_condition_to_branches(binder, &rule.condition, &rule.verdict);
            all_branches.extend(branches);
        }
        // Deduplicate trailing wildcards — keep only the last.
        deduplicate_wildcards(&mut all_branches);

        let scrutinee = build_first_accessor(binder, rules);
        let match_term = Term::match_expr(
            scrutinee,
            Term::Constant(QualIdent::simple("ComplianceVerdict")),
            all_branches,
        );
        Term::lam(binder, Term::constant(context_type), match_term)
    }
}

/// Compile a set of rules into a boolean-producing guard lambda.
///
/// The guard returns `True` if any rule's condition matches (the exception
/// applies) and `False` otherwise. This is distinct from the body lambda,
/// which returns the compliance verdict.
fn compile_rules_to_guard_lambda(context_type: &str, rules: &[&DecisionRule]) -> Term {
    let binder = "ctx";

    if rules.len() == 1 {
        let rule = rules[0];
        let (scrutinee, branches) =
            compile_condition_to_branches(binder, &rule.condition, &rule.verdict);
        // Rewrite branches: matching verdict => True, opposite => False.
        let verdict_t = verdict_term(&rule.verdict);
        let guard_branches: Vec<Branch> = branches
            .into_iter()
            .map(|b| Branch {
                pattern: b.pattern,
                body: if b.body == verdict_t {
                    Term::Constant(QualIdent::simple("True"))
                } else {
                    Term::Constant(QualIdent::simple("False"))
                },
            })
            .collect();
        let match_term = Term::match_expr(
            scrutinee,
            Term::Constant(QualIdent::simple("Bool")),
            guard_branches,
        );
        Term::lam(binder, Term::constant(context_type), match_term)
    } else {
        let mut all_branches = Vec::new();
        for rule in rules {
            let (_, branches) =
                compile_condition_to_branches(binder, &rule.condition, &rule.verdict);
            let verdict_t = verdict_term(&rule.verdict);
            let guard_branches: Vec<Branch> = branches
                .into_iter()
                .map(|b| Branch {
                    pattern: b.pattern,
                    body: if b.body == verdict_t {
                        Term::Constant(QualIdent::simple("True"))
                    } else {
                        Term::Constant(QualIdent::simple("False"))
                    },
                })
                .collect();
            all_branches.extend(guard_branches);
        }
        deduplicate_wildcards(&mut all_branches);

        let scrutinee = build_first_accessor(binder, rules);
        let match_term = Term::match_expr(
            scrutinee,
            Term::Constant(QualIdent::simple("Bool")),
            all_branches,
        );
        Term::lam(binder, Term::constant(context_type), match_term)
    }
}

/// For multi-rule tables, extract the scrutinee from the first rule.
fn build_first_accessor(binder: &str, rules: &[&DecisionRule]) -> Term {
    match &rules[0].condition {
        Condition::Equals { accessor, .. }
        | Condition::GreaterThan { accessor, .. }
        | Condition::LessThan { accessor, .. }
        | Condition::IsTrue { accessor }
        | Condition::IsFalse { accessor } => build_accessor(binder, accessor),
        _ => Term::var(binder, 0),
    }
}

/// Compile higher-priority rules into Lex `Exception`s.
fn compile_exceptions(context_type: &str, rules: &[&DecisionRule]) -> Vec<Exception> {
    if rules.is_empty() {
        return vec![];
    }

    // Group by priority.
    let mut priority_groups: Vec<(u32, Vec<&DecisionRule>)> = Vec::new();
    for rule in rules {
        if let Some(group) = priority_groups.iter_mut().find(|(p, _)| *p == rule.priority) {
            group.1.push(rule);
        } else {
            priority_groups.push((rule.priority, vec![rule]));
        }
    }
    priority_groups.sort_by_key(|(p, _)| *p);

    priority_groups
        .into_iter()
        .map(|(priority, group_rules)| {
            // Guard: boolean-producing lambda — does this exception apply?
            // Compiles conditions to True/False (the guard proposition).
            let guard = compile_rules_to_guard_lambda(context_type, &group_rules);
            // Body: the verdict to apply when the guard holds.
            let body = compile_rules_to_lambda(context_type, &group_rules);
            Exception {
                guard: Box::new(guard),
                body: Box::new(body),
                priority: Some(priority),
                authority: None,
            }
        })
        .collect()
}

/// Remove duplicate wildcard branches, keeping only the last.
fn deduplicate_wildcards(branches: &mut Vec<Branch>) {
    let wildcard_count = branches.iter().filter(|b| b.pattern == Pattern::Wildcard).count();
    if wildcard_count > 1 {
        // Keep the last wildcard, remove earlier ones.
        let mut seen_last = false;
        let len = branches.len();
        let mut i = len;
        while i > 0 {
            i -= 1;
            if branches[i].pattern == Pattern::Wildcard {
                if !seen_last {
                    seen_last = true;
                } else {
                    branches.remove(i);
                }
            }
        }
    }
}

fn opposite_verdict(verdict: &str) -> String {
    match verdict {
        "Compliant" => "NonCompliant".to_string(),
        "NonCompliant" => "Compliant".to_string(),
        "Pending" => "NonCompliant".to_string(),
        _ => "NonCompliant".to_string(),
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    // ── Helper ──────────────────────────────────────────────────────

    fn ibc_minimum_directors_table() -> DecisionTable {
        DecisionTable {
            name: "minimum_directors".to_string(),
            jurisdiction: "sc".to_string(),
            legal_basis: "IBC Act 2016 s.66".to_string(),
            context_type: "IncorporationContext".to_string(),
            rules: vec![
                DecisionRule {
                    condition: Condition::Equals {
                        accessor: "director_count".to_string(),
                        value: "0".to_string(),
                    },
                    verdict: "NonCompliant".to_string(),
                    priority: 0,
                },
            ],
        }
    }

    // ── Test 1: Minimum directors compiles to expected AST ─────────

    #[test]
    fn compile_minimum_directors_matches_handwritten() {
        let table = ibc_minimum_directors_table();
        let compiled = compile_table(&table).unwrap();

        // The handwritten .lex Rule 1 produces:
        //
        //   defeasible
        //     lambda (ctx : IncorporationContext).
        //       match ctx.director_count return ComplianceVerdict with
        //       | 0 => NonCompliant
        //       | _ => Compliant
        //     priority 0
        //   end
        //
        // Which is a DefeasibleRule with:
        //   - base_body = Lambda(ctx : IncorporationContext, Match(accessor, ...))
        //   - base_ty = ComplianceVerdict

        match &compiled {
            Term::Defeasible(rule) => {
                assert_eq!(rule.name.name, "minimum_directors");
                assert!(rule.exceptions.is_empty(), "no exceptions for single-priority");

                // base_ty should be ComplianceVerdict
                assert_eq!(
                    *rule.base_ty,
                    Term::Constant(QualIdent::simple("ComplianceVerdict"))
                );

                // base_body should be lambda (ctx : IncorporationContext). match ...
                match rule.base_body.as_ref() {
                    Term::Lambda { binder, domain, body } => {
                        assert_eq!(binder.name, "ctx");
                        assert_eq!(
                            **domain,
                            Term::Constant(QualIdent::simple("IncorporationContext"))
                        );

                        // body should be a Match
                        match body.as_ref() {
                            Term::Match { scrutinee, return_ty, branches } => {
                                // scrutinee = App(Constant("director_count"), Var("ctx"))
                                assert_eq!(
                                    **scrutinee,
                                    Term::app(
                                        Term::constant("director_count"),
                                        Term::var("ctx", 0)
                                    )
                                );
                                assert_eq!(
                                    **return_ty,
                                    Term::Constant(QualIdent::simple("ComplianceVerdict"))
                                );
                                assert_eq!(branches.len(), 2);

                                // Branch 1: | 0 => NonCompliant
                                assert_eq!(
                                    branches[0].pattern,
                                    Pattern::Constructor {
                                        constructor: Constructor::new(QualIdent::simple("0")),
                                        binders: vec![],
                                    }
                                );
                                assert_eq!(
                                    branches[0].body,
                                    Term::Constant(QualIdent::simple("NonCompliant"))
                                );

                                // Branch 2: | _ => Compliant
                                assert_eq!(branches[1].pattern, Pattern::Wildcard);
                                assert_eq!(
                                    branches[1].body,
                                    Term::Constant(QualIdent::simple("Compliant"))
                                );
                            }
                            other => panic!("expected Match body, got {:?}", other),
                        }
                    }
                    other => panic!("expected Lambda base_body, got {:?}", other),
                }
            }
            other => panic!("expected Defeasible, got {:?}", other),
        }
    }

    // ── Test 2: Empty table is an error ────────────────────────────

    #[test]
    fn empty_table_returns_error() {
        let table = DecisionTable {
            name: "empty".to_string(),
            jurisdiction: "sc".to_string(),
            legal_basis: "none".to_string(),
            context_type: "Ctx".to_string(),
            rules: vec![],
        };
        assert_eq!(compile_table(&table), Err(CompileError::EmptyTable));
    }

    // ── Test 3: Invalid verdict is rejected ────────────────────────

    #[test]
    fn invalid_verdict_rejected() {
        let table = DecisionTable {
            name: "bad".to_string(),
            jurisdiction: "sc".to_string(),
            legal_basis: "none".to_string(),
            context_type: "Ctx".to_string(),
            rules: vec![DecisionRule {
                condition: Condition::Always,
                verdict: "Maybe".to_string(),
                priority: 0,
            }],
        };
        assert_eq!(
            compile_table(&table),
            Err(CompileError::InvalidVerdict("Maybe".to_string()))
        );
    }

    // ── Test 4: Boolean IsTrue condition ───────────────────────────

    #[test]
    fn is_true_compiles_to_match() {
        let table = DecisionTable {
            name: "bearer_shares".to_string(),
            jurisdiction: "sc".to_string(),
            legal_basis: "IBC Act s.24".to_string(),
            context_type: "IncorporationContext".to_string(),
            rules: vec![DecisionRule {
                condition: Condition::IsTrue {
                    accessor: "conducts_business_with_seychelles_residents".to_string(),
                },
                verdict: "NonCompliant".to_string(),
                priority: 0,
            }],
        };
        let compiled = compile_table(&table).unwrap();
        match &compiled {
            Term::Defeasible(rule) => {
                match rule.base_body.as_ref() {
                    Term::Lambda { body, .. } => {
                        match body.as_ref() {
                            Term::Match { branches, .. } => {
                                assert_eq!(branches.len(), 2);
                                // True => NonCompliant
                                assert_eq!(
                                    branches[0].pattern,
                                    Pattern::Constructor {
                                        constructor: Constructor::new(QualIdent::simple("True")),
                                        binders: vec![],
                                    }
                                );
                                assert_eq!(
                                    branches[0].body,
                                    Term::Constant(QualIdent::simple("NonCompliant"))
                                );
                                // _ => Compliant
                                assert_eq!(branches[1].pattern, Pattern::Wildcard);
                                assert_eq!(
                                    branches[1].body,
                                    Term::Constant(QualIdent::simple("Compliant"))
                                );
                            }
                            other => panic!("expected Match, got {:?}", other),
                        }
                    }
                    other => panic!("expected Lambda, got {:?}", other),
                }
            }
            other => panic!("expected Defeasible, got {:?}", other),
        }
    }

    // ── Test 5: Always condition compiles to wildcard ──────────────

    #[test]
    fn always_condition_produces_wildcard() {
        let table = DecisionTable {
            name: "no_minimum_capital".to_string(),
            jurisdiction: "sc".to_string(),
            legal_basis: "IBC Act (absence of requirement)".to_string(),
            context_type: "IncorporationContext".to_string(),
            rules: vec![DecisionRule {
                condition: Condition::Always,
                verdict: "Compliant".to_string(),
                priority: 0,
            }],
        };
        let compiled = compile_table(&table).unwrap();
        match &compiled {
            Term::Defeasible(rule) => {
                match rule.base_body.as_ref() {
                    Term::Lambda { body, .. } => {
                        match body.as_ref() {
                            Term::Match { branches, .. } => {
                                assert_eq!(branches.len(), 1);
                                assert_eq!(branches[0].pattern, Pattern::Wildcard);
                                assert_eq!(
                                    branches[0].body,
                                    Term::Constant(QualIdent::simple("Compliant"))
                                );
                            }
                            other => panic!("expected Match, got {:?}", other),
                        }
                    }
                    other => panic!("expected Lambda, got {:?}", other),
                }
            }
            other => panic!("expected Defeasible, got {:?}", other),
        }
    }

    // ── Test 6: Defeasibility — higher priority creates exception ──

    #[test]
    fn defeasible_priority_creates_exception() {
        // Rule 13: Share transfers need board approval, UNLESS articles permit free transfer.
        let table = DecisionTable {
            name: "share_transfer".to_string(),
            jurisdiction: "sc".to_string(),
            legal_basis: "IBC Act s.30".to_string(),
            context_type: "IncorporationContext".to_string(),
            rules: vec![
                DecisionRule {
                    condition: Condition::IsFalse {
                        accessor: "board_approved_share_transfer".to_string(),
                    },
                    verdict: "NonCompliant".to_string(),
                    priority: 0,
                },
                DecisionRule {
                    condition: Condition::IsTrue {
                        accessor: "articles_permit_free_transfer".to_string(),
                    },
                    verdict: "Compliant".to_string(),
                    priority: 1,
                },
            ],
        };
        let compiled = compile_table(&table).unwrap();
        match &compiled {
            Term::Defeasible(rule) => {
                assert_eq!(rule.name.name, "share_transfer");
                assert_eq!(rule.exceptions.len(), 1, "one exception for priority 1");
                assert_eq!(rule.exceptions[0].priority, Some(1));
            }
            other => panic!("expected Defeasible, got {:?}", other),
        }
    }

    // ── Test 7: YAML round-trip ────────────────────────────────────

    #[test]
    fn serde_json_round_trip() {
        let table = ibc_minimum_directors_table();
        let json = serde_json::to_string_pretty(&table).unwrap();
        let recovered: DecisionTable = serde_json::from_str(&json).unwrap();
        assert_eq!(table, recovered);
    }

    // ── Test 8: Empty accessor rejected ────────────────────────────

    #[test]
    fn empty_accessor_rejected() {
        let table = DecisionTable {
            name: "bad".to_string(),
            jurisdiction: "sc".to_string(),
            legal_basis: "none".to_string(),
            context_type: "Ctx".to_string(),
            rules: vec![DecisionRule {
                condition: Condition::Equals {
                    accessor: "".to_string(),
                    value: "X".to_string(),
                },
                verdict: "Compliant".to_string(),
                priority: 0,
            }],
        };
        assert_eq!(compile_table(&table), Err(CompileError::EmptyAccessor));
    }

    // ── Test 9: Nested accessor path ───────────────────────────────

    #[test]
    fn nested_accessor_builds_chained_apps() {
        let table = DecisionTable {
            name: "registered_agent_license".to_string(),
            jurisdiction: "sc".to_string(),
            legal_basis: "IBC Act s.92".to_string(),
            context_type: "IncorporationContext".to_string(),
            rules: vec![DecisionRule {
                condition: Condition::Equals {
                    accessor: "registered_agent.csp_license_status".to_string(),
                    value: "Active".to_string(),
                },
                verdict: "Compliant".to_string(),
                priority: 0,
            }],
        };
        let compiled = compile_table(&table).unwrap();
        match &compiled {
            Term::Defeasible(rule) => {
                match rule.base_body.as_ref() {
                    Term::Lambda { body, .. } => {
                        match body.as_ref() {
                            Term::Match { scrutinee, .. } => {
                                // scrutinee should be App("csp_license_status", App("registered_agent", Var("ctx")))
                                let expected = Term::app(
                                    Term::constant("csp_license_status"),
                                    Term::app(
                                        Term::constant("registered_agent"),
                                        Term::var("ctx", 0),
                                    ),
                                );
                                assert_eq!(**scrutinee, expected);
                            }
                            other => panic!("expected Match, got {:?}", other),
                        }
                    }
                    other => panic!("expected Lambda, got {:?}", other),
                }
            }
            other => panic!("expected Defeasible, got {:?}", other),
        }
    }

    // ── Test 10: And(Equals, IsTrue) compiles to nested match ──────

    #[test]
    fn and_equals_is_true_compiles_to_nested_match() {
        // And(director_count == 1, has_registered_agent == True) => Compliant
        let table = DecisionTable {
            name: "and_combo".to_string(),
            jurisdiction: "sc".to_string(),
            legal_basis: "test".to_string(),
            context_type: "Ctx".to_string(),
            rules: vec![DecisionRule {
                condition: Condition::And(vec![
                    Condition::Equals {
                        accessor: "director_count".to_string(),
                        value: "1".to_string(),
                    },
                    Condition::IsTrue {
                        accessor: "has_registered_agent".to_string(),
                    },
                ]),
                verdict: "Compliant".to_string(),
                priority: 0,
            }],
        };
        let compiled = compile_table(&table).unwrap();
        match &compiled {
            Term::Defeasible(rule) => {
                match rule.base_body.as_ref() {
                    Term::Lambda { body, .. } => {
                        // Outermost match is on ctx (trivial wrapper from And).
                        // Inside is the nested And structure.
                        match body.as_ref() {
                            Term::Match { branches, .. } => {
                                assert_eq!(branches.len(), 1, "single wildcard wrapper");
                                assert_eq!(branches[0].pattern, Pattern::Wildcard);

                                // The body should be a nested match on director_count.
                                match &branches[0].body {
                                    Term::Match {
                                        scrutinee: outer_scrut,
                                        branches: outer_branches,
                                        ..
                                    } => {
                                        // Scrutinee: ctx.director_count
                                        assert_eq!(
                                            **outer_scrut,
                                            Term::app(
                                                Term::constant("director_count"),
                                                Term::var("ctx", 0)
                                            )
                                        );
                                        assert_eq!(outer_branches.len(), 2);

                                        // Branch | 1 => (nested match on has_registered_agent)
                                        assert_eq!(
                                            outer_branches[0].pattern,
                                            Pattern::Constructor {
                                                constructor: Constructor::new(QualIdent::simple(
                                                    "1"
                                                )),
                                                binders: vec![],
                                            }
                                        );
                                        // The matching branch body should be the inner match.
                                        match &outer_branches[0].body {
                                            Term::Match {
                                                scrutinee: inner_scrut,
                                                branches: inner_branches,
                                                ..
                                            } => {
                                                assert_eq!(
                                                    **inner_scrut,
                                                    Term::app(
                                                        Term::constant("has_registered_agent"),
                                                        Term::var("ctx", 0)
                                                    )
                                                );
                                                assert_eq!(inner_branches.len(), 2);
                                                // | True => Compliant
                                                assert_eq!(
                                                    inner_branches[0].pattern,
                                                    Pattern::Constructor {
                                                        constructor: Constructor::new(
                                                            QualIdent::simple("True")
                                                        ),
                                                        binders: vec![],
                                                    }
                                                );
                                                assert_eq!(
                                                    inner_branches[0].body,
                                                    Term::Constant(QualIdent::simple("Compliant"))
                                                );
                                                // | _ => NonCompliant
                                                assert_eq!(
                                                    inner_branches[1].pattern,
                                                    Pattern::Wildcard
                                                );
                                                assert_eq!(
                                                    inner_branches[1].body,
                                                    Term::Constant(QualIdent::simple(
                                                        "NonCompliant"
                                                    ))
                                                );
                                            }
                                            other => panic!(
                                                "expected nested Match for IsTrue, got {:?}",
                                                other
                                            ),
                                        }

                                        // Branch | _ => NonCompliant (director_count didn't match)
                                        assert_eq!(outer_branches[1].pattern, Pattern::Wildcard);
                                        assert_eq!(
                                            outer_branches[1].body,
                                            Term::Constant(QualIdent::simple("NonCompliant"))
                                        );
                                    }
                                    other => panic!(
                                        "expected nested Match for Equals, got {:?}",
                                        other
                                    ),
                                }
                            }
                            other => panic!("expected Match body, got {:?}", other),
                        }
                    }
                    other => panic!("expected Lambda, got {:?}", other),
                }
            }
            other => panic!("expected Defeasible, got {:?}", other),
        }
    }

    // ── Test 11: Or(Equals, Equals) compiles to nested match ────────

    #[test]
    fn or_equals_equals_compiles_to_nested_match() {
        // Or(status == "Active", status == "Provisional") => Compliant
        let table = DecisionTable {
            name: "or_combo".to_string(),
            jurisdiction: "sc".to_string(),
            legal_basis: "test".to_string(),
            context_type: "Ctx".to_string(),
            rules: vec![DecisionRule {
                condition: Condition::Or(vec![
                    Condition::Equals {
                        accessor: "status".to_string(),
                        value: "Active".to_string(),
                    },
                    Condition::Equals {
                        accessor: "status".to_string(),
                        value: "Provisional".to_string(),
                    },
                ]),
                verdict: "Compliant".to_string(),
                priority: 0,
            }],
        };
        let compiled = compile_table(&table).unwrap();
        match &compiled {
            Term::Defeasible(rule) => {
                match rule.base_body.as_ref() {
                    Term::Lambda { body, .. } => {
                        // Outermost is a trivial wildcard wrapper from Or.
                        match body.as_ref() {
                            Term::Match { branches, .. } => {
                                assert_eq!(branches.len(), 1, "single wildcard wrapper");

                                // The body should be a nested match on first Or branch (status == Active).
                                match &branches[0].body {
                                    Term::Match {
                                        scrutinee: first_scrut,
                                        branches: first_branches,
                                        ..
                                    } => {
                                        // Scrutinee: ctx.status
                                        assert_eq!(
                                            **first_scrut,
                                            Term::app(
                                                Term::constant("status"),
                                                Term::var("ctx", 0)
                                            )
                                        );
                                        assert_eq!(first_branches.len(), 2);

                                        // | Active => Compliant
                                        assert_eq!(
                                            first_branches[0].pattern,
                                            Pattern::Constructor {
                                                constructor: Constructor::new(QualIdent::simple(
                                                    "Active"
                                                )),
                                                binders: vec![],
                                            }
                                        );
                                        assert_eq!(
                                            first_branches[0].body,
                                            Term::Constant(QualIdent::simple("Compliant"))
                                        );

                                        // | _ => (nested match for second Or branch)
                                        assert_eq!(first_branches[1].pattern, Pattern::Wildcard);
                                        match &first_branches[1].body {
                                            Term::Match {
                                                scrutinee: second_scrut,
                                                branches: second_branches,
                                                ..
                                            } => {
                                                assert_eq!(
                                                    **second_scrut,
                                                    Term::app(
                                                        Term::constant("status"),
                                                        Term::var("ctx", 0)
                                                    )
                                                );
                                                assert_eq!(second_branches.len(), 2);
                                                // | Provisional => Compliant
                                                assert_eq!(
                                                    second_branches[0].pattern,
                                                    Pattern::Constructor {
                                                        constructor: Constructor::new(
                                                            QualIdent::simple("Provisional")
                                                        ),
                                                        binders: vec![],
                                                    }
                                                );
                                                assert_eq!(
                                                    second_branches[0].body,
                                                    Term::Constant(QualIdent::simple("Compliant"))
                                                );
                                                // | _ => NonCompliant
                                                assert_eq!(
                                                    second_branches[1].pattern,
                                                    Pattern::Wildcard
                                                );
                                                assert_eq!(
                                                    second_branches[1].body,
                                                    Term::Constant(QualIdent::simple(
                                                        "NonCompliant"
                                                    ))
                                                );
                                            }
                                            other => panic!(
                                                "expected nested Match for second Or, got {:?}",
                                                other
                                            ),
                                        }
                                    }
                                    other => panic!(
                                        "expected nested Match for first Or, got {:?}",
                                        other
                                    ),
                                }
                            }
                            other => panic!("expected Match body, got {:?}", other),
                        }
                    }
                    other => panic!("expected Lambda, got {:?}", other),
                }
            }
            other => panic!("expected Defeasible, got {:?}", other),
        }
    }

    // ── Test 12: GreaterThan threshold ────────────────────────────

    #[test]
    fn greater_than_enumerates_threshold() {
        let table = DecisionTable {
            name: "min_shareholders".to_string(),
            jurisdiction: "sc".to_string(),
            legal_basis: "IBC Act s.11".to_string(),
            context_type: "IncorporationContext".to_string(),
            rules: vec![DecisionRule {
                condition: Condition::GreaterThan {
                    accessor: "shareholder_count".to_string(),
                    threshold: 0,
                },
                verdict: "Compliant".to_string(),
                priority: 0,
            }],
        };
        let compiled = compile_table(&table).unwrap();
        match &compiled {
            Term::Defeasible(rule) => {
                match rule.base_body.as_ref() {
                    Term::Lambda { body, .. } => {
                        match body.as_ref() {
                            Term::Match { branches, .. } => {
                                // | 0 => NonCompliant (opposite of Compliant)
                                // | _ => Compliant
                                assert_eq!(branches.len(), 2);
                                assert_eq!(
                                    branches[0].body,
                                    Term::Constant(QualIdent::simple("NonCompliant"))
                                );
                                assert_eq!(branches[1].pattern, Pattern::Wildcard);
                                assert_eq!(
                                    branches[1].body,
                                    Term::Constant(QualIdent::simple("Compliant"))
                                );
                            }
                            other => panic!("expected Match, got {:?}", other),
                        }
                    }
                    other => panic!("expected Lambda, got {:?}", other),
                }
            }
            other => panic!("expected Defeasible, got {:?}", other),
        }
    }
}
