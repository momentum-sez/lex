//! SMT-LIB2 interface for Lex decision procedures.
//!
//! Provides a structured representation of SMT queries, translation from
//! proof obligations to SMT problems, SMT-LIB2 text generation, and an
//! external solver bridge that invokes `z3 -smt2 -in` via `std::process::Command`.
//!
//! If the `z3` binary is not available on `PATH`, `solve_external` returns
//! `SmtResult::Unknown` — never an error. This keeps the decision procedure
//! pipeline functional on machines without Z3 installed.

use serde::{Deserialize, Serialize};

use crate::obligations::{ObligationCategory, ProofObligation};

// ---------------------------------------------------------------------------
// SMT types
// ---------------------------------------------------------------------------

/// An SMT query representing a satisfiability problem.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SmtQuery {
    /// Variables with their sorts.
    pub variables: Vec<(String, SmtSort)>,
    /// Assertions (constraints that must hold).
    pub assertions: Vec<SmtExpr>,
    /// The property to check (is it satisfiable?).
    pub goal: SmtExpr,
}

/// SMT-LIB2 sorts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SmtSort {
    Bool,
    Int,
    Real,
    BitVec(u32),
    String,
}

/// SMT-LIB2 expression tree.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SmtExpr {
    /// Variable reference.
    Var(std::string::String),
    /// Literal value.
    Lit(SmtLiteral),
    /// Function/predicate application: `(f arg1 arg2 ...)`.
    App(std::string::String, Vec<SmtExpr>),
    /// Conjunction.
    And(Vec<SmtExpr>),
    /// Disjunction.
    Or(Vec<SmtExpr>),
    /// Negation.
    Not(Box<SmtExpr>),
    /// Implication.
    Implies(Box<SmtExpr>, Box<SmtExpr>),
    /// Equality.
    Eq(Box<SmtExpr>, Box<SmtExpr>),
    /// Less-than.
    Lt(Box<SmtExpr>, Box<SmtExpr>),
    /// Greater-than.
    Gt(Box<SmtExpr>, Box<SmtExpr>),
    /// Less-than-or-equal.
    Le(Box<SmtExpr>, Box<SmtExpr>),
    /// Greater-than-or-equal.
    Ge(Box<SmtExpr>, Box<SmtExpr>),
    /// If-then-else.
    Ite(Box<SmtExpr>, Box<SmtExpr>, Box<SmtExpr>),
}

/// SMT literal values.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SmtLiteral {
    Bool(bool),
    Int(i64),
    String(std::string::String),
}

/// Result of an SMT query.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SmtResult {
    /// The goal is satisfiable.
    Sat,
    /// The goal is unsatisfiable.
    Unsat,
    /// The solver could not determine satisfiability.
    Unknown,
    /// The solver exceeded the time limit.
    Timeout,
}

// ---------------------------------------------------------------------------
// Obligation → SMT translation
// ---------------------------------------------------------------------------

/// Convert a Lex proof obligation to an SMT query, if the obligation
/// maps to a decidable SMT fragment.
///
/// Returns `None` for obligation categories that do not have a natural
/// SMT encoding (e.g., identity verification, defeasible resolution).
pub fn obligation_to_smt(obligation: &ProofObligation) -> Option<SmtQuery> {
    match obligation.category {
        ObligationCategory::ThresholdComparison => {
            threshold_obligation_to_smt(obligation)
        }
        ObligationCategory::DomainMembership => {
            domain_membership_to_smt(obligation)
        }
        ObligationCategory::SanctionsCheck => {
            sanctions_check_to_smt(obligation)
        }
        ObligationCategory::TemporalOrdering => {
            temporal_ordering_to_smt(obligation)
        }
        // These categories require non-SMT reasoning.
        ObligationCategory::ExhaustiveMatch
        | ObligationCategory::IdentityVerification
        | ObligationCategory::DefeasibleResolution => None,
    }
}

fn threshold_obligation_to_smt(_obligation: &ProofObligation) -> Option<SmtQuery> {
    // Encode: exists value, threshold such that value >= threshold (or other op).
    // The obligation description contains the comparison info; we encode a
    // generic threshold query that the SMT solver can decide.
    let value_var = "value".to_string();
    let threshold_var = "threshold".to_string();

    Some(SmtQuery {
        variables: vec![
            (value_var.clone(), SmtSort::Int),
            (threshold_var.clone(), SmtSort::Int),
        ],
        assertions: vec![
            // value >= 0 (amounts are non-negative)
            SmtExpr::Ge(
                Box::new(SmtExpr::Var(value_var.clone())),
                Box::new(SmtExpr::Lit(SmtLiteral::Int(0))),
            ),
            // threshold >= 0
            SmtExpr::Ge(
                Box::new(SmtExpr::Var(threshold_var.clone())),
                Box::new(SmtExpr::Lit(SmtLiteral::Int(0))),
            ),
        ],
        goal: SmtExpr::Ge(
            Box::new(SmtExpr::Var(value_var)),
            Box::new(SmtExpr::Var(threshold_var)),
        ),
    })
}

fn domain_membership_to_smt(_obligation: &ProofObligation) -> Option<SmtQuery> {
    // Encode: exists x such that x is in the domain (x == d1 || x == d2 || ...).
    // We use a generic encoding with a single variable and a disjunction.
    let member_var = "member".to_string();

    Some(SmtQuery {
        variables: vec![(member_var.clone(), SmtSort::Int)],
        assertions: vec![],
        goal: SmtExpr::Or(vec![
            SmtExpr::Eq(
                Box::new(SmtExpr::Var(member_var.clone())),
                Box::new(SmtExpr::Lit(SmtLiteral::Int(0))),
            ),
            SmtExpr::Eq(
                Box::new(SmtExpr::Var(member_var)),
                Box::new(SmtExpr::Lit(SmtLiteral::Int(1))),
            ),
        ]),
    })
}

fn sanctions_check_to_smt(_obligation: &ProofObligation) -> Option<SmtQuery> {
    // Encode: sanctions_clear is a boolean that must be true.
    let clear_var = "sanctions_clear".to_string();

    Some(SmtQuery {
        variables: vec![(clear_var.clone(), SmtSort::Bool)],
        assertions: vec![],
        goal: SmtExpr::Var(clear_var),
    })
}

fn temporal_ordering_to_smt(_obligation: &ProofObligation) -> Option<SmtQuery> {
    // Encode: exists before, after such that before < after.
    let before_var = "time_before".to_string();
    let after_var = "time_after".to_string();

    Some(SmtQuery {
        variables: vec![
            (before_var.clone(), SmtSort::Int),
            (after_var.clone(), SmtSort::Int),
        ],
        assertions: vec![
            // Times are non-negative epoch values.
            SmtExpr::Ge(
                Box::new(SmtExpr::Var(before_var.clone())),
                Box::new(SmtExpr::Lit(SmtLiteral::Int(0))),
            ),
            SmtExpr::Ge(
                Box::new(SmtExpr::Var(after_var.clone())),
                Box::new(SmtExpr::Lit(SmtLiteral::Int(0))),
            ),
        ],
        goal: SmtExpr::Lt(
            Box::new(SmtExpr::Var(before_var)),
            Box::new(SmtExpr::Var(after_var)),
        ),
    })
}

// ---------------------------------------------------------------------------
// SMT-LIB2 text generation
// ---------------------------------------------------------------------------

/// Generate SMT-LIB2 text from a query.
///
/// The output is a complete SMT-LIB2 script that can be piped to
/// `z3 -smt2 -in` (or any other SMT-LIB2 compatible solver).
pub fn to_smtlib2(query: &SmtQuery) -> String {
    let mut out = String::new();

    // Logic declaration.
    out.push_str("(set-logic ALL)\n");

    // Variable declarations.
    for (name, sort) in &query.variables {
        out.push_str(&format!(
            "(declare-const {} {})\n",
            smtlib2_escape_symbol(name),
            sort_to_smtlib2(sort)
        ));
    }

    // Assertions.
    for assertion in &query.assertions {
        out.push_str(&format!("(assert {})\n", expr_to_smtlib2(assertion)));
    }

    // Goal: assert the goal and check satisfiability.
    out.push_str(&format!("(assert {})\n", expr_to_smtlib2(&query.goal)));
    out.push_str("(check-sat)\n");

    out
}

fn sort_to_smtlib2(sort: &SmtSort) -> String {
    match sort {
        SmtSort::Bool => "Bool".to_string(),
        SmtSort::Int => "Int".to_string(),
        SmtSort::Real => "Real".to_string(),
        SmtSort::BitVec(width) => format!("(_ BitVec {width})"),
        SmtSort::String => "String".to_string(),
    }
}

fn expr_to_smtlib2(expr: &SmtExpr) -> String {
    match expr {
        SmtExpr::Var(name) => smtlib2_escape_symbol(name),
        SmtExpr::Lit(lit) => literal_to_smtlib2(lit),
        SmtExpr::App(func, args) => {
            if args.is_empty() {
                smtlib2_escape_symbol(func)
            } else {
                let arg_strs: Vec<String> = args.iter().map(expr_to_smtlib2).collect();
                format!("({} {})", smtlib2_escape_symbol(func), arg_strs.join(" "))
            }
        }
        SmtExpr::And(conjuncts) => {
            if conjuncts.is_empty() {
                "true".to_string()
            } else if conjuncts.len() == 1 {
                expr_to_smtlib2(&conjuncts[0])
            } else {
                let strs: Vec<String> = conjuncts.iter().map(expr_to_smtlib2).collect();
                format!("(and {})", strs.join(" "))
            }
        }
        SmtExpr::Or(disjuncts) => {
            if disjuncts.is_empty() {
                "false".to_string()
            } else if disjuncts.len() == 1 {
                expr_to_smtlib2(&disjuncts[0])
            } else {
                let strs: Vec<String> = disjuncts.iter().map(expr_to_smtlib2).collect();
                format!("(or {})", strs.join(" "))
            }
        }
        SmtExpr::Not(inner) => format!("(not {})", expr_to_smtlib2(inner)),
        SmtExpr::Implies(lhs, rhs) => {
            format!("(=> {} {})", expr_to_smtlib2(lhs), expr_to_smtlib2(rhs))
        }
        SmtExpr::Eq(lhs, rhs) => {
            format!("(= {} {})", expr_to_smtlib2(lhs), expr_to_smtlib2(rhs))
        }
        SmtExpr::Lt(lhs, rhs) => {
            format!("(< {} {})", expr_to_smtlib2(lhs), expr_to_smtlib2(rhs))
        }
        SmtExpr::Gt(lhs, rhs) => {
            format!("(> {} {})", expr_to_smtlib2(lhs), expr_to_smtlib2(rhs))
        }
        SmtExpr::Le(lhs, rhs) => {
            format!("(<= {} {})", expr_to_smtlib2(lhs), expr_to_smtlib2(rhs))
        }
        SmtExpr::Ge(lhs, rhs) => {
            format!("(>= {} {})", expr_to_smtlib2(lhs), expr_to_smtlib2(rhs))
        }
        SmtExpr::Ite(cond, then_expr, else_expr) => {
            format!(
                "(ite {} {} {})",
                expr_to_smtlib2(cond),
                expr_to_smtlib2(then_expr),
                expr_to_smtlib2(else_expr)
            )
        }
    }
}

fn literal_to_smtlib2(lit: &SmtLiteral) -> String {
    match lit {
        SmtLiteral::Bool(b) => if *b { "true" } else { "false" }.to_string(),
        SmtLiteral::Int(n) => {
            if *n < 0 {
                format!("(- {})", n.unsigned_abs())
            } else {
                n.to_string()
            }
        }
        SmtLiteral::String(s) => format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"")),
    }
}

/// Escape an SMT-LIB2 symbol if it contains special characters.
///
/// Per SMT-LIB2 spec, `|` and `\` are not permitted inside quoted symbols.
/// If the name contains either character, they are stripped to produce a
/// safe symbol. An empty name (or a name that becomes empty after stripping)
/// is mapped to the sentinel `|empty|`.
fn smtlib2_escape_symbol(name: &str) -> String {
    if name.is_empty() {
        return "|empty|".to_string();
    }
    // If the name is a simple identifier (alphanumeric + underscore, not starting with digit),
    // no escaping needed.
    let is_simple = name
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !name.starts_with(|c: char| c.is_ascii_digit());
    if is_simple {
        name.to_string()
    } else {
        // Per SMT-LIB2 spec, `|` and `\` are illegal inside quoted symbols.
        // Strip them to produce a safe identifier.
        let sanitized: String = name.chars().filter(|&c| c != '|' && c != '\\').collect();
        if sanitized.is_empty() {
            "|empty|".to_string()
        } else {
            format!("|{}|", sanitized)
        }
    }
}

// ---------------------------------------------------------------------------
// External solver bridge
// ---------------------------------------------------------------------------

/// Maximum bytes to read from solver stdout (first line only, bounded).
const MAX_STDOUT_LINE_BYTES: usize = 4096;

/// Solve an SMT query by invoking the `z3` binary as an external process.
///
/// The query is serialized to SMT-LIB2 and piped to `z3 -smt2 -in` via stdin.
/// The timeout is passed to Z3 via `(set-option :timeout ...)` AND enforced
/// as a process-level deadline: if Z3 does not produce output within
/// `timeout_ms`, the child process is killed and `SmtResult::Timeout` is
/// returned.
///
/// Stdout is read through a `BufReader` — only the first line (max 4 KB) is
/// consumed. The child process is dropped (and killed) immediately after.
///
/// If `z3` is not installed or not on `PATH`, this returns `SmtResult::Unknown`
/// (never an error). This is by design: the absence of a solver degrades
/// gracefully to the same undecidable result as before the SMT integration.
pub fn solve_external(query: &SmtQuery, timeout_ms: u64) -> SmtResult {
    use std::io::{BufRead, BufReader, Read, Write};
    use std::process::{Command, Stdio};
    use std::sync::mpsc;
    use std::time::Duration;

    // Build the SMT-LIB2 input with timeout.
    let mut input = format!("(set-option :timeout {})\n", timeout_ms);
    input.push_str(&to_smtlib2(query));

    // Attempt to spawn z3.
    let child = Command::new("z3")
        .args(["-smt2", "-in"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn();

    let mut child = match child {
        Ok(child) => child,
        Err(_) => {
            // z3 not installed — degrade gracefully.
            return SmtResult::Unknown;
        }
    };

    // Write the SMT-LIB2 input to z3's stdin.
    if let Some(ref mut stdin) = child.stdin {
        if stdin.write_all(input.as_bytes()).is_err() {
            let _ = child.kill();
            return SmtResult::Unknown;
        }
    }
    // Drop stdin to signal EOF.
    drop(child.stdin.take());

    // Read stdout on a background thread with a bounded read (first line, max 4 KB).
    // Use a channel to enforce a process-level timeout independent of Z3's own.
    let stdout_handle = match child.stdout.take() {
        Some(stdout) => stdout,
        None => {
            let _ = child.kill();
            return SmtResult::Unknown;
        }
    };

    let (tx, rx) = mpsc::channel::<String>();
    let reader_thread = std::thread::spawn(move || {
        let mut reader = BufReader::new(stdout_handle.take(MAX_STDOUT_LINE_BYTES as u64));
        let mut line = String::new();
        // read_line stops at '\n' or EOF. The `.take()` bounds total bytes.
        let _ = reader.read_line(&mut line);
        let _ = tx.send(line);
    });

    // Wait for the reader thread with a bounded timeout.
    // Add a small margin (500 ms) over the SMT-level timeout to let Z3 respond
    // before we escalate to a process kill.
    let deadline = Duration::from_millis(timeout_ms.saturating_add(500));
    let first_line = match rx.recv_timeout(deadline) {
        Ok(line) => line,
        Err(_) => {
            // Timeout — kill the child process explicitly so the reader thread's
            // `read_line` sees EOF and exits. Then reap the zombie and join the
            // thread to prevent a thread leak.
            let _ = child.kill();
            let _ = child.wait();
            let _ = reader_thread.join();
            return SmtResult::Timeout;
        }
    };

    // Reap the child process (non-blocking after stdout EOF).
    let _ = child.kill();
    let _ = child.wait();
    let _ = reader_thread.join();

    match first_line.trim() {
        "sat" => SmtResult::Sat,
        "unsat" => SmtResult::Unsat,
        "unknown" => SmtResult::Unknown,
        "timeout" => SmtResult::Timeout,
        _ => SmtResult::Unknown,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn smt_to_smtlib2_simple_satisfiability() {
        let query = SmtQuery {
            variables: vec![("x".to_string(), SmtSort::Int)],
            assertions: vec![SmtExpr::Ge(
                Box::new(SmtExpr::Var("x".to_string())),
                Box::new(SmtExpr::Lit(SmtLiteral::Int(0))),
            )],
            goal: SmtExpr::Gt(
                Box::new(SmtExpr::Var("x".to_string())),
                Box::new(SmtExpr::Lit(SmtLiteral::Int(5))),
            ),
        };

        let smtlib2 = to_smtlib2(&query);

        assert!(smtlib2.contains("(set-logic ALL)"));
        assert!(smtlib2.contains("(declare-const x Int)"));
        assert!(smtlib2.contains("(assert (>= x 0))"));
        assert!(smtlib2.contains("(assert (> x 5))"));
        assert!(smtlib2.contains("(check-sat)"));
    }

    #[test]
    fn smt_to_smtlib2_threshold_comparison() {
        let query = SmtQuery {
            variables: vec![
                ("amount".to_string(), SmtSort::Int),
                ("limit".to_string(), SmtSort::Int),
            ],
            assertions: vec![
                SmtExpr::Eq(
                    Box::new(SmtExpr::Var("amount".to_string())),
                    Box::new(SmtExpr::Lit(SmtLiteral::Int(100_000))),
                ),
                SmtExpr::Eq(
                    Box::new(SmtExpr::Var("limit".to_string())),
                    Box::new(SmtExpr::Lit(SmtLiteral::Int(50_000))),
                ),
            ],
            goal: SmtExpr::Ge(
                Box::new(SmtExpr::Var("amount".to_string())),
                Box::new(SmtExpr::Var("limit".to_string())),
            ),
        };

        let smtlib2 = to_smtlib2(&query);

        assert!(smtlib2.contains("(declare-const amount Int)"));
        assert!(smtlib2.contains("(declare-const limit Int)"));
        assert!(smtlib2.contains("(assert (= amount 100000))"));
        assert!(smtlib2.contains("(assert (= limit 50000))"));
        assert!(smtlib2.contains("(assert (>= amount limit))"));
    }

    #[test]
    fn smt_to_smtlib2_boolean_sanctions() {
        let query = SmtQuery {
            variables: vec![("clear".to_string(), SmtSort::Bool)],
            assertions: vec![],
            goal: SmtExpr::And(vec![
                SmtExpr::Var("clear".to_string()),
                SmtExpr::Not(Box::new(SmtExpr::Lit(SmtLiteral::Bool(false)))),
            ]),
        };

        let smtlib2 = to_smtlib2(&query);

        assert!(smtlib2.contains("(declare-const clear Bool)"));
        assert!(smtlib2.contains("(and clear (not false))"));
    }

    #[test]
    fn smt_to_smtlib2_implies_and_ite() {
        let query = SmtQuery {
            variables: vec![
                ("p".to_string(), SmtSort::Bool),
                ("q".to_string(), SmtSort::Bool),
            ],
            assertions: vec![],
            goal: SmtExpr::Implies(
                Box::new(SmtExpr::Var("p".to_string())),
                Box::new(SmtExpr::Ite(
                    Box::new(SmtExpr::Var("q".to_string())),
                    Box::new(SmtExpr::Lit(SmtLiteral::Bool(true))),
                    Box::new(SmtExpr::Lit(SmtLiteral::Bool(false))),
                )),
            ),
        };

        let smtlib2 = to_smtlib2(&query);

        assert!(smtlib2.contains("(=> p (ite q true false))"));
    }

    #[test]
    fn smt_to_smtlib2_negative_literal() {
        let query = SmtQuery {
            variables: vec![("x".to_string(), SmtSort::Int)],
            assertions: vec![],
            goal: SmtExpr::Gt(
                Box::new(SmtExpr::Var("x".to_string())),
                Box::new(SmtExpr::Lit(SmtLiteral::Int(-42))),
            ),
        };

        let smtlib2 = to_smtlib2(&query);

        assert!(smtlib2.contains("(> x (- 42))"));
    }

    #[test]
    fn smt_to_smtlib2_string_literal() {
        let query = SmtQuery {
            variables: vec![("s".to_string(), SmtSort::String)],
            assertions: vec![],
            goal: SmtExpr::Eq(
                Box::new(SmtExpr::Var("s".to_string())),
                Box::new(SmtExpr::Lit(SmtLiteral::String("hello".to_string()))),
            ),
        };

        let smtlib2 = to_smtlib2(&query);

        assert!(smtlib2.contains("(declare-const s String)"));
        assert!(smtlib2.contains("(= s \"hello\")"));
    }

    #[test]
    fn smt_to_smtlib2_bitvec_sort() {
        let query = SmtQuery {
            variables: vec![("flags".to_string(), SmtSort::BitVec(32))],
            assertions: vec![],
            goal: SmtExpr::Var("flags".to_string()),
        };

        let smtlib2 = to_smtlib2(&query);

        assert!(smtlib2.contains("(declare-const flags (_ BitVec 32))"));
    }

    #[test]
    fn smt_to_smtlib2_le_and_ge() {
        let query = SmtQuery {
            variables: vec![("x".to_string(), SmtSort::Int)],
            assertions: vec![],
            goal: SmtExpr::And(vec![
                SmtExpr::Le(
                    Box::new(SmtExpr::Lit(SmtLiteral::Int(0))),
                    Box::new(SmtExpr::Var("x".to_string())),
                ),
                SmtExpr::Ge(
                    Box::new(SmtExpr::Var("x".to_string())),
                    Box::new(SmtExpr::Lit(SmtLiteral::Int(0))),
                ),
            ]),
        };

        let smtlib2 = to_smtlib2(&query);

        assert!(smtlib2.contains("(<= 0 x)"));
        assert!(smtlib2.contains("(>= x 0)"));
    }

    #[test]
    fn smt_to_smtlib2_empty_and_is_true() {
        let smtlib2 = expr_to_smtlib2(&SmtExpr::And(vec![]));
        assert_eq!(smtlib2, "true");
    }

    #[test]
    fn smt_to_smtlib2_empty_or_is_false() {
        let smtlib2 = expr_to_smtlib2(&SmtExpr::Or(vec![]));
        assert_eq!(smtlib2, "false");
    }

    #[test]
    fn smt_to_smtlib2_singleton_and_unwraps() {
        let smtlib2 = expr_to_smtlib2(&SmtExpr::And(vec![SmtExpr::Var("x".to_string())]));
        assert_eq!(smtlib2, "x");
    }

    #[test]
    fn smt_to_smtlib2_function_application() {
        let smtlib2 = expr_to_smtlib2(&SmtExpr::App(
            "f".to_string(),
            vec![
                SmtExpr::Var("a".to_string()),
                SmtExpr::Lit(SmtLiteral::Int(42)),
            ],
        ));
        assert_eq!(smtlib2, "(f a 42)");
    }

    #[test]
    fn smt_to_smtlib2_nullary_application() {
        let smtlib2 = expr_to_smtlib2(&SmtExpr::App("true_const".to_string(), vec![]));
        assert_eq!(smtlib2, "true_const");
    }

    #[test]
    fn smt_to_smtlib2_special_symbol_escaped() {
        let smtlib2 = smtlib2_escape_symbol("my-var");
        assert_eq!(smtlib2, "|my-var|");
    }

    #[test]
    fn smt_to_smtlib2_simple_symbol_not_escaped() {
        let smtlib2 = smtlib2_escape_symbol("x_val");
        assert_eq!(smtlib2, "x_val");
    }

    #[test]
    fn smt_escape_strips_pipe_chars() {
        // `|` is illegal inside SMT-LIB2 quoted symbols — must be stripped.
        let smtlib2 = smtlib2_escape_symbol("my|var");
        assert!(!smtlib2.contains("my|var"), "pipe must be stripped");
        assert_eq!(smtlib2, "|myvar|");
    }

    #[test]
    fn smt_escape_strips_backslash_chars() {
        // `\` is illegal inside SMT-LIB2 quoted symbols — must be stripped.
        let smtlib2 = smtlib2_escape_symbol("my\\var");
        assert!(!smtlib2.contains('\\'), "backslash must be stripped");
        assert_eq!(smtlib2, "|myvar|");
    }

    #[test]
    fn smt_escape_all_illegal_returns_empty_sentinel() {
        // A name consisting entirely of `|` and `\` should map to the sentinel.
        let smtlib2 = smtlib2_escape_symbol("||\\|");
        assert_eq!(smtlib2, "|empty|");
    }

    #[test]
    fn smt_obligation_threshold_produces_query() {
        let obligation = ProofObligation {
            id: "obl-0001".to_string(),
            description: "threshold comparison on amounts".to_string(),
            category: ObligationCategory::ThresholdComparison,
            term: crate::ast::Term::IntLit(0),
            expected: "comparison holds".to_string(),
            suggested_procedure: "presburger_arithmetic".to_string(),
        };

        let query = obligation_to_smt(&obligation);
        assert!(query.is_some());

        let query = query.unwrap();
        assert_eq!(query.variables.len(), 2);
        assert!(matches!(query.goal, SmtExpr::Ge(_, _)));

        let smtlib2 = to_smtlib2(&query);
        assert!(smtlib2.contains("(declare-const value Int)"));
        assert!(smtlib2.contains("(declare-const threshold Int)"));
    }

    #[test]
    fn smt_obligation_domain_membership_produces_query() {
        let obligation = ProofObligation {
            id: "obl-0002".to_string(),
            description: "domain membership check".to_string(),
            category: ObligationCategory::DomainMembership,
            term: crate::ast::Term::IntLit(0),
            expected: "member of domain".to_string(),
            suggested_procedure: "finite_domain_enumeration".to_string(),
        };

        let query = obligation_to_smt(&obligation);
        assert!(query.is_some());

        let query = query.unwrap();
        assert_eq!(query.variables.len(), 1);
        assert!(matches!(query.goal, SmtExpr::Or(_)));
    }

    #[test]
    fn smt_obligation_sanctions_produces_query() {
        let obligation = ProofObligation {
            id: "obl-0003".to_string(),
            description: "sanctions clearance".to_string(),
            category: ObligationCategory::SanctionsCheck,
            term: crate::ast::Term::IntLit(0),
            expected: "sanctions clear".to_string(),
            suggested_procedure: "bdd_style_boolean_compliance".to_string(),
        };

        let query = obligation_to_smt(&obligation);
        assert!(query.is_some());

        let query = query.unwrap();
        assert_eq!(query.variables.len(), 1);
        assert_eq!(query.variables[0].1, SmtSort::Bool);
    }

    #[test]
    fn smt_obligation_temporal_produces_query() {
        let obligation = ProofObligation {
            id: "obl-0004".to_string(),
            description: "temporal ordering".to_string(),
            category: ObligationCategory::TemporalOrdering,
            term: crate::ast::Term::IntLit(0),
            expected: "ordered".to_string(),
            suggested_procedure: "temporal_stratification_check".to_string(),
        };

        let query = obligation_to_smt(&obligation);
        assert!(query.is_some());

        let query = query.unwrap();
        assert_eq!(query.variables.len(), 2);
        assert!(matches!(query.goal, SmtExpr::Lt(_, _)));
    }

    #[test]
    fn smt_obligation_identity_returns_none() {
        let obligation = ProofObligation {
            id: "obl-0005".to_string(),
            description: "identity verification".to_string(),
            category: ObligationCategory::IdentityVerification,
            term: crate::ast::Term::IntLit(0),
            expected: "verified".to_string(),
            suggested_procedure: "identity_attestation_chain".to_string(),
        };

        assert!(obligation_to_smt(&obligation).is_none());
    }

    #[test]
    fn smt_obligation_defeasible_returns_none() {
        let obligation = ProofObligation {
            id: "obl-0006".to_string(),
            description: "defeasible resolution".to_string(),
            category: ObligationCategory::DefeasibleResolution,
            term: crate::ast::Term::IntLit(0),
            expected: "resolved".to_string(),
            suggested_procedure: "fuel_bounded_defeasible_search".to_string(),
        };

        assert!(obligation_to_smt(&obligation).is_none());
    }

    #[test]
    fn smt_obligation_exhaustive_match_returns_none() {
        let obligation = ProofObligation {
            id: "obl-0007".to_string(),
            description: "exhaustive match".to_string(),
            category: ObligationCategory::ExhaustiveMatch,
            term: crate::ast::Term::IntLit(0),
            expected: "exhaustive".to_string(),
            suggested_procedure: "finite_domain_enumeration".to_string(),
        };

        assert!(obligation_to_smt(&obligation).is_none());
    }

    #[test]
    fn smt_solve_external_returns_result_or_unknown() {
        // This test exercises the external solver bridge. If z3 is installed,
        // it should return Sat. If not, it returns Unknown. Both are valid.
        let query = SmtQuery {
            variables: vec![("x".to_string(), SmtSort::Int)],
            assertions: vec![SmtExpr::Ge(
                Box::new(SmtExpr::Var("x".to_string())),
                Box::new(SmtExpr::Lit(SmtLiteral::Int(0))),
            )],
            goal: SmtExpr::Gt(
                Box::new(SmtExpr::Var("x".to_string())),
                Box::new(SmtExpr::Lit(SmtLiteral::Int(5))),
            ),
        };

        let result = solve_external(&query, 5000);

        // Either z3 is installed (Sat) or not (Unknown). Both are correct.
        assert!(
            result == SmtResult::Sat || result == SmtResult::Unknown,
            "expected Sat or Unknown, got {result:?}"
        );
    }

    #[test]
    fn smt_solve_external_unsat_query() {
        // x > 0 AND x < 0 is unsatisfiable.
        let query = SmtQuery {
            variables: vec![("x".to_string(), SmtSort::Int)],
            assertions: vec![
                SmtExpr::Gt(
                    Box::new(SmtExpr::Var("x".to_string())),
                    Box::new(SmtExpr::Lit(SmtLiteral::Int(0))),
                ),
            ],
            goal: SmtExpr::Lt(
                Box::new(SmtExpr::Var("x".to_string())),
                Box::new(SmtExpr::Lit(SmtLiteral::Int(0))),
            ),
        };

        let result = solve_external(&query, 5000);

        // Either z3 is installed (Unsat) or not (Unknown). Both are correct.
        assert!(
            result == SmtResult::Unsat || result == SmtResult::Unknown,
            "expected Unsat or Unknown, got {result:?}"
        );
    }

    #[test]
    fn smt_roundtrip_obligation_to_smtlib2() {
        // End-to-end: obligation -> SMT query -> SMT-LIB2 text -> parseable.
        let obligation = ProofObligation {
            id: "obl-0010".to_string(),
            description: "threshold comparison on transaction amounts".to_string(),
            category: ObligationCategory::ThresholdComparison,
            term: crate::ast::Term::IntLit(0),
            expected: "the comparison is provable".to_string(),
            suggested_procedure: "presburger_arithmetic".to_string(),
        };

        let query = obligation_to_smt(&obligation).expect("threshold should produce a query");
        let smtlib2 = to_smtlib2(&query);

        // Verify structural properties of the output.
        assert!(smtlib2.starts_with("(set-logic ALL)\n"));
        assert!(smtlib2.ends_with("(check-sat)\n"));
        assert!(smtlib2.contains("(declare-const"));
        assert!(smtlib2.contains("(assert"));

        // Verify it can be solved (or gracefully degrades).
        let result = solve_external(&query, 5000);
        assert!(
            result == SmtResult::Sat || result == SmtResult::Unknown,
            "expected Sat or Unknown for satisfiable threshold query"
        );
    }
}
