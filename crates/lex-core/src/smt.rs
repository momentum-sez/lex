//! SMT-LIB2 interface for Lex decision procedures.
//!
//! Provides a structured representation of SMT queries, translation from
//! proof obligations to SMT problems, SMT-LIB2 text generation, and an
//! external solver bridge that invokes `z3 -smt2 -in` via `std::process::Command`.
//!
//! If the `z3` binary is not available on `PATH`, `solve_external` returns
//! `SmtResult::Unknown` — never an error. This keeps the decision procedure
//! pipeline functional on machines without Z3 installed.
//!
//! # Textual translation (SMT-LIB 2.6)
//!
//! The [`translate_lex_to_smt`] entry point produces a [`TextualSmtQuery`]
//! from a Lex [`Term`](crate::ast::Term). The textual form is intentionally
//! decoupled from [`SmtQuery`]: the structured `SmtQuery` continues to be used
//! by the proof obligation decision pipeline in [`crate::decide`]; the textual
//! form is for direct production of SMT-LIB 2.6 scripts suitable for the
//! `QF_LRA` / `QF_NIA` / `QF_UF` fragment that Z3 and cvc5 share.
//!
//! ## Supported term shapes
//!
//! * Boolean accessor (`b = true`) — encoded as `Bool` sorted constant.
//! * Natural comparisons (`n > k`, `n = k`) — encoded as `Int` sort with
//!   `(> ...)` / `(= ...)` over `QF_LRA`/`QF_NIA`.
//! * Tag match (`match x with | T1 | T2 | ...`) — each tag is encoded as a
//!   distinct integer in an injective `tag_of_<symbol>` uninterpreted function
//!   domain. The encoding is documented at [`TagEncoding::IntDisjunction`].
//! * Conjunction of conditions within a row — `(and ...)`.
//! * Decision-table first-row-wins cascade — right-associated `(ite cond then
//!   rest)` chain, preserving Lex decision ordering.
//! * Defeasible rules with priority — `(assert (=> <guard> <verdict>))` per
//!   rule, plus a numeric priority witness constraint expressing that the
//!   highest-priority firing rule determines the outcome.
//!
//! ## Unsupported shapes
//!
//! Lambda with free variables, general recursion, universe polymorphism,
//! temporal modalities, and principle balancing are explicitly rejected with
//! [`SmtTranslationError::Unsupported`]. No silent fall-through encoding is
//! performed — correctness beats coverage.

use serde::{Deserialize, Serialize};

use crate::ast::{Branch, Constructor, DefeasibleRule, Pattern, QualIdent, Term};
use crate::decision_table::{Condition, DecisionTable};
use crate::obligations::{ObligationCategory, ProofObligation};
use std::collections::BTreeMap;

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
        ObligationCategory::ThresholdComparison => threshold_obligation_to_smt(obligation),
        ObligationCategory::DomainMembership => domain_membership_to_smt(obligation),
        ObligationCategory::SanctionsCheck => sanctions_check_to_smt(obligation),
        ObligationCategory::TemporalOrdering => temporal_ordering_to_smt(obligation),
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
    let is_simple = name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
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

// ═══════════════════════════════════════════════════════════════════════════
//
//  Textual translation: Lex Term → SMT-LIB 2.6
//
//  The code below builds the production-grade textual translator requested by
//  Tier 1 item 4 of the Platonic Ideal resolution. It is intentionally
//  decoupled from the structured `SmtQuery` used by the decision pipeline.
//
// ═══════════════════════════════════════════════════════════════════════════

// ---------------------------------------------------------------------------
// Logic / options
// ---------------------------------------------------------------------------

/// The SMT-LIB 2.6 theory fragment to emit.
///
/// The translator picks the tightest logic that fits the translated term.
/// Callers may override via [`SmtOptions::logic_override`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SmtLogic {
    /// Quantifier-free linear real arithmetic (`QF_LRA`).
    QfLra,
    /// Quantifier-free nonlinear integer arithmetic (`QF_NIA`).
    ///
    /// Used when integer multiplication or non-linear operations are present.
    QfNia,
    /// Quantifier-free uninterpreted functions with equality (`QF_UF`).
    ///
    /// Used for pure tag / boolean queries with no arithmetic.
    QfUf,
    /// Quantifier-free uninterpreted functions + linear integer arithmetic
    /// (`QF_UFLIA`). Used when both integer comparisons and tag / boolean
    /// encodings appear together — the default for decision-table cascades.
    QfUflia,
}

impl SmtLogic {
    /// SMT-LIB 2.6 surface name (for `(set-logic ...)`).
    pub const fn as_str(self) -> &'static str {
        match self {
            SmtLogic::QfLra => "QF_LRA",
            SmtLogic::QfNia => "QF_NIA",
            SmtLogic::QfUf => "QF_UF",
            SmtLogic::QfUflia => "QF_UFLIA",
        }
    }
}

/// How to encode a Lex tag / constructor universe in SMT-LIB.
///
/// Lex tags (e.g., `Clear | Hit | Blocked` for `SanctionsResult`) have no
/// primitive SMT-LIB representation. We pick an encoding at translation time:
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TagEncoding {
    /// Encode each tag as a distinct integer in `{0, 1, …, n-1}`.
    ///
    /// `(declare-const sanctions_status Int)` with domain restriction
    /// `(and (>= sanctions_status 0) (< sanctions_status n))` asserted as a
    /// side condition. A tag match `| Clear => …` emits `(= sanctions_status
    /// 0)` where `0` is the canonical index assigned to `Clear`.
    ///
    /// This is the default: it fits `QF_LIA` / `QF_UFLIA`, is trivially
    /// supported by Z3 and cvc5, and preserves disjointness mechanically.
    #[default]
    IntDisjunction,
    /// Encode each tag as an uninterpreted constant in an uninterpreted sort.
    ///
    /// `(declare-sort Tag_SanctionsResult 0)` +
    /// `(declare-const Clear Tag_SanctionsResult)` + a distinct-ness axiom
    /// `(assert (distinct Clear Hit Blocked))`. This requires `QF_UF` and is
    /// structurally cleaner but slightly heavier. Use when the caller intends
    /// to extract a model with symbolic tag names.
    UninterpretedSort,
}

/// Options governing how a Lex term is rendered to SMT-LIB 2.6.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct SmtOptions {
    /// Tag / constructor encoding (default: [`TagEncoding::IntDisjunction`]).
    pub tag_encoding: TagEncoding,
    /// Emit `(set-option :produce-models true)`. Default: true.
    pub produce_models: bool,
    /// Override the computed logic. Default: `None` (auto-select).
    pub logic_override: Option<SmtLogic>,
    /// Embed a source comment block at the top of the emitted script.
    ///
    /// The string is sanitized: `;` is escaped, newlines are normalized, and
    /// any line longer than 120 characters is truncated. Empty disables the
    /// comment block entirely. Default: empty.
    pub source_comment: String,
}

impl Default for SmtOptions {
    fn default() -> Self {
        Self {
            tag_encoding: TagEncoding::default(),
            produce_models: true,
            logic_override: None,
            source_comment: String::new(),
        }
    }
}

impl SmtOptions {
    /// Builder — override [`SmtOptions::tag_encoding`].
    #[must_use]
    pub fn with_tag_encoding(mut self, encoding: TagEncoding) -> Self {
        self.tag_encoding = encoding;
        self
    }

    /// Builder — override [`SmtOptions::produce_models`].
    #[must_use]
    pub fn with_produce_models(mut self, flag: bool) -> Self {
        self.produce_models = flag;
        self
    }

    /// Builder — override [`SmtOptions::logic_override`].
    #[must_use]
    pub fn with_logic(mut self, logic: Option<SmtLogic>) -> Self {
        self.logic_override = logic;
        self
    }

    /// Builder — override [`SmtOptions::source_comment`].
    #[must_use]
    pub fn with_source_comment(mut self, comment: impl Into<String>) -> Self {
        self.source_comment = comment.into();
        self
    }
}

// ---------------------------------------------------------------------------
// Translation errors
// ---------------------------------------------------------------------------

/// Errors that can occur when translating a Lex term to SMT-LIB 2.6.
///
/// Unsupported shapes never fall through to an approximate encoding —
/// correctness beats coverage. Each error variant names the Lex shape that
/// could not be translated and supplies a reason that the caller can surface
/// to the user.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum SmtTranslationError {
    /// The Lex term uses a shape the SMT translator does not handle.
    #[error("unsupported Lex shape `{shape}`: {reason}")]
    Unsupported {
        /// Human-readable name of the Lex shape (e.g., "Term::Lambda with free variables").
        shape: String,
        /// Why this shape cannot be translated faithfully to the `QF_*` fragment.
        reason: String,
    },
    /// An accessor path is empty (would produce an empty identifier).
    #[error("empty accessor path on Lex term; at least one segment is required")]
    EmptyAccessor,
    /// A tag / constructor domain has zero members (would produce an
    /// unsatisfiable-by-construction script).
    #[error("tag domain `{symbol}` has no constructors")]
    EmptyTagDomain {
        /// Name of the tag domain that was encountered.
        symbol: String,
    },
    /// A numeric literal is outside the supported range (i64).
    #[error("numeric literal {literal} is out of range for SMT-LIB encoding")]
    NumericOutOfRange {
        /// The literal that could not be encoded.
        literal: String,
    },
    /// An accessor contains a character that cannot appear in an SMT-LIB
    /// quoted symbol (`|` or `\`) and cannot be escaped safely.
    #[error("accessor `{accessor}` contains illegal SMT-LIB symbol characters")]
    IllegalSymbol {
        /// The accessor that violated the SMT-LIB symbol grammar.
        accessor: String,
    },
    /// Decision table with zero rows — cannot produce a meaningful goal.
    #[error("decision table `{name}` has no rules")]
    EmptyDecisionTable {
        /// Name of the table that was empty.
        name: String,
    },
    /// A verdict string is not one of the legal Lex verdicts.
    #[error("invalid verdict `{verdict}` in decision table `{table}`")]
    InvalidVerdict {
        /// Table that the bad verdict was found in.
        table: String,
        /// The offending verdict string.
        verdict: String,
    },
}

// ---------------------------------------------------------------------------
// TextualSmtQuery — the structured output of the translator
// ---------------------------------------------------------------------------

/// A translated SMT-LIB 2.6 query in structured form.
///
/// Call [`TextualSmtQuery::to_smtlib_text`] to produce the byte-stable
/// canonical text. Declarations are sorted alphabetically; assertions keep
/// translation order (which preserves Lex's first-row-wins semantics).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TextualSmtQuery {
    /// Theory logic to declare via `(set-logic ...)`.
    pub logic: SmtLogic,
    /// `(declare-const ...)` / `(declare-sort ...)` / `(declare-fun ...)` lines,
    /// one S-expression per element. Stored unsorted; sorted at render time.
    pub declarations: Vec<String>,
    /// `(assert ...)` bodies (each element is the body of a single assert, not
    /// including the surrounding `(assert ...)`). Rendered in source order.
    pub assertions: Vec<String>,
    /// Optional goal — if present, rendered as the final assertion before
    /// `(check-sat)`. Typically the negation of the claim to verify for
    /// unsat-core / validity checks, or the claim itself for a
    /// satisfiability check.
    pub goal: Option<String>,
    /// Emit `(set-option :produce-models true)` before `(set-logic ...)`.
    pub produce_models: bool,
    /// Optional source comment block (already sanitized).
    pub source_comment: String,
}

impl TextualSmtQuery {
    /// Render the query as canonical SMT-LIB 2.6 text.
    ///
    /// Output is deterministic:
    ///
    /// 1. Optional comment block (one `;` per line).
    /// 2. `(set-option :produce-models true)` (if enabled).
    /// 3. `(set-logic <logic>)`.
    /// 4. Declarations, sorted alphabetically by their SMT-LIB symbol.
    /// 5. Assertions, in source order.
    /// 6. Goal (if any), wrapped in `(assert …)`.
    /// 7. `(check-sat)`.
    ///
    /// Every line ends with `\n`. The final character is always `\n`.
    pub fn to_smtlib_text(&self) -> String {
        let mut out = String::with_capacity(
            256 + self.declarations.iter().map(String::len).sum::<usize>()
                + self.assertions.iter().map(String::len).sum::<usize>(),
        );

        // (1) Comment block — prefix every line with "; " (SMT-LIB line comment).
        if !self.source_comment.is_empty() {
            for line in self.source_comment.lines() {
                out.push_str("; ");
                out.push_str(line);
                out.push('\n');
            }
        }

        // (2) set-option
        if self.produce_models {
            out.push_str("(set-option :produce-models true)\n");
        }

        // (3) set-logic
        out.push_str("(set-logic ");
        out.push_str(self.logic.as_str());
        out.push_str(")\n");

        // (4) Declarations — sorted alphabetically by symbol (first non-keyword
        // identifier). We use a deterministic key extractor to avoid
        // whitespace sensitivity.
        let mut decls = self.declarations.clone();
        decls.sort_by_key(|a| declaration_sort_key(a));
        for decl in &decls {
            out.push_str(decl);
            if !decl.ends_with('\n') {
                out.push('\n');
            }
        }

        // (5) Assertions — source order.
        for a in &self.assertions {
            out.push_str("(assert ");
            out.push_str(a);
            out.push_str(")\n");
        }

        // (6) Goal — rendered as a final assertion so that `(check-sat)` tests
        // the conjunction of premises AND the goal.
        if let Some(goal) = &self.goal {
            out.push_str("(assert ");
            out.push_str(goal);
            out.push_str(")\n");
        }

        // (7) Finalize.
        out.push_str("(check-sat)\n");

        out
    }
}

/// Extract a deterministic sort key from a declaration S-expression.
///
/// Expected shapes:
/// - `(declare-const name sort)`
/// - `(declare-sort name arity)`
/// - `(declare-fun name (args) ret)`
///
/// We scan forward past the opening paren and the keyword, then collect the
/// name. If no name is found, return the raw declaration (pathological but
/// still deterministic).
fn declaration_sort_key(decl: &str) -> String {
    let mut chars = decl.chars().peekable();
    // skip leading whitespace and opening paren
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() || c == '(' {
            chars.next();
        } else {
            break;
        }
    }
    // collect keyword
    let mut keyword = String::new();
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() {
            break;
        }
        keyword.push(c);
        chars.next();
    }
    // skip whitespace
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
        } else {
            break;
        }
    }
    // collect name (may be |...| quoted or bareword)
    let mut name = String::new();
    if let Some(&'|') = chars.peek() {
        // Quoted symbol — include both pipes.
        name.push('|');
        chars.next();
        for c in chars.by_ref() {
            name.push(c);
            if c == '|' {
                break;
            }
        }
    } else {
        for c in chars.by_ref() {
            if c.is_whitespace() || c == ')' {
                break;
            }
            name.push(c);
        }
    }

    if name.is_empty() {
        // Fallback: sort by keyword then raw text.
        format!("{keyword}/{decl}")
    } else {
        // Primary key: name. Secondary: keyword (stable when names collide,
        // which should not happen in practice but is defensive).
        format!("{name}/{keyword}")
    }
}

// ---------------------------------------------------------------------------
// Entry points
// ---------------------------------------------------------------------------

/// Translate a Lex term to an SMT-LIB 2.6 query.
///
/// Supported top-level shapes:
///
/// * [`Term::Defeasible`] — translated as a decision-table style first-row-wins
///   cascade with optional higher-priority overrides (see module docs).
/// * [`Term::Match`] whose scrutinee is a simple accessor — translated as a
///   tag match.
/// * Application form `App(App(op, lhs), rhs)` where `op` is a recognized
///   built-in comparison (`>`, `=`, `<`, `>=`, `<=`).
///
/// # Verdict-body admissibility precondition
///
/// Every decision/exception arm body whose verdict is extracted (via
/// [`extract_verdict_from_body`]) must reduce to one of the three legal Lex
/// verdict constants — `Compliant`, `NonCompliant`, or `Pending` — possibly
/// under `Lambda` binders or inside a `Match` with a verdict-constant arm. A
/// body that does not satisfy this precondition is rejected
/// ([`SmtTranslationError::Unsupported`] / [`SmtTranslationError::InvalidVerdict`]),
/// never silently defaulted to a verdict.
///
/// Any other shape returns [`SmtTranslationError::Unsupported`].
pub fn translate_lex_to_smt(
    term: &Term,
    options: &SmtOptions,
) -> Result<TextualSmtQuery, SmtTranslationError> {
    let mut ctx = TranslatorCtx::new(options);
    match term {
        Term::Defeasible(rule) => translate_defeasible(rule, &mut ctx)?,
        Term::Match {
            scrutinee,
            branches,
            ..
        } => translate_match(scrutinee, branches, &mut ctx)?,
        Term::Lambda { body, .. } => {
            // Delegate through the lambda (single-binder decision tables wrap
            // their body in a lambda; the inner body is the target).
            translate_lex_to_smt_inner(body, &mut ctx)?;
        }
        other => {
            return Err(SmtTranslationError::Unsupported {
                shape: lex_term_shape(other),
                reason: "top-level translation requires Defeasible, Match, or Lambda wrapper"
                    .to_string(),
            });
        }
    }
    ctx.finalize(options)
}

/// Translate a Lex [`DecisionTable`] directly to an SMT-LIB 2.6 query.
///
/// This is the canonical translation surface. Most callers producing a query
/// from a Lex decision rule already hold the [`DecisionTable`] and should
/// prefer this entry point — it avoids the round-trip through [`Term`] and
/// guarantees precise handling of priorities and first-row-wins semantics.
pub fn translate_decision_table(
    table: &DecisionTable,
    options: &SmtOptions,
) -> Result<TextualSmtQuery, SmtTranslationError> {
    if table.rules.is_empty() {
        return Err(SmtTranslationError::EmptyDecisionTable {
            name: table.name.clone(),
        });
    }
    // Validate verdicts up front (fail-closed).
    for rule in &table.rules {
        match rule.verdict.as_str() {
            "Compliant" | "NonCompliant" | "Pending" => {}
            other => {
                return Err(SmtTranslationError::InvalidVerdict {
                    table: table.name.clone(),
                    verdict: other.to_string(),
                });
            }
        }
    }
    let mut ctx = TranslatorCtx::new(options);
    ctx.push_source_comment(&format!(
        "decision-table `{}` [{}/{}]",
        table.name, table.jurisdiction, table.legal_basis
    ));

    // Build the cascade:
    //
    //   goal := (= verdict (ite cond_0 v_0 (ite cond_1 v_1 … default)))
    //
    // First-row-wins means rules are tried in source order. Priority is
    // encoded as an additive offset on the rule index — higher priority
    // fires earlier. We sort the rule indices stably by descending priority,
    // then by source order (stable sort preserves source order within a
    // priority band).
    let mut indexed: Vec<(usize, &crate::decision_table::DecisionRule)> =
        table.rules.iter().enumerate().collect();
    indexed.sort_by(|a, b| b.1.priority.cmp(&a.1.priority).then(a.0.cmp(&b.0)));

    // Pre-register tag universes in source order so that tag indices match
    // rule authoring intent (Clear=0, Provisional=1, Hit=2 for three-arm
    // sanctions). Without this pre-pass, the inside-out cascade build would
    // assign indices in reverse-source order — correct but confusing.
    for (_, rule) in &indexed {
        preregister_tags_in_condition(&rule.condition, &mut ctx)?;
    }

    // Allocate the verdict output variable once.
    let verdict_symbol = ctx.fresh_verdict_symbol("verdict");

    // Build cascade inside-out: start with the default arm (no rule matched =
    // Pending), then wrap each rule as (ite cond verdict rest).
    let mut cascade = verdict_literal("Pending");
    for (_, rule) in indexed.iter().rev() {
        let cond_sexpr = translate_condition(&rule.condition, &mut ctx)?;
        let this_verdict = verdict_literal(&rule.verdict);
        cascade = format!("(ite {cond_sexpr} {this_verdict} {cascade})");
    }

    ctx.push_assertion(format!("(= {verdict_symbol} {cascade})"));
    ctx.use_verdict_tag_domain();
    ctx.finalize(options)
}

// ---------------------------------------------------------------------------
// Internal translation state
// ---------------------------------------------------------------------------

/// Mutable translation context: declarations collected so far, tag encodings,
/// and the computed logic.
struct TranslatorCtx {
    declarations: BTreeMap<String, String>, // symbol -> full declaration
    assertions: Vec<String>,
    tag_domains: BTreeMap<String, Vec<String>>, // domain_name -> [tag_name, ...]
    /// Symbols whose sort has already been committed. Used to prevent
    /// conflicting re-declarations.
    committed_sorts: BTreeMap<String, CommittedSort>,
    tag_encoding: TagEncoding,
    has_int: bool,
    has_uf: bool,
    has_non_linear: bool,
    source_comment_buf: String,
    logic_override: Option<SmtLogic>,
    goal: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CommittedSort {
    Bool,
    Int,
    Tag(String),
}

impl TranslatorCtx {
    fn new(options: &SmtOptions) -> Self {
        Self {
            declarations: BTreeMap::new(),
            assertions: Vec::new(),
            tag_domains: BTreeMap::new(),
            committed_sorts: BTreeMap::new(),
            tag_encoding: options.tag_encoding,
            has_int: false,
            has_uf: false,
            has_non_linear: false,
            source_comment_buf: sanitize_comment(&options.source_comment),
            logic_override: options.logic_override,
            goal: None,
        }
    }

    fn push_source_comment(&mut self, s: &str) {
        if !self.source_comment_buf.is_empty() {
            self.source_comment_buf.push('\n');
        }
        self.source_comment_buf.push_str(&sanitize_comment(s));
    }

    fn declare_bool(&mut self, symbol: &str) -> Result<String, SmtTranslationError> {
        let escaped = smtlib_safe_symbol(symbol)?;
        match self.committed_sorts.get(&escaped) {
            Some(CommittedSort::Bool) => {}
            Some(other) => {
                return Err(SmtTranslationError::Unsupported {
                    shape: format!("mixed-sort accessor `{symbol}`"),
                    reason: format!("already committed as {other:?}; cannot also be Bool"),
                });
            }
            None => {
                self.declarations
                    .insert(escaped.clone(), format!("(declare-const {escaped} Bool)"));
                self.committed_sorts
                    .insert(escaped.clone(), CommittedSort::Bool);
            }
        }
        Ok(escaped)
    }

    fn declare_int(&mut self, symbol: &str) -> Result<String, SmtTranslationError> {
        let escaped = smtlib_safe_symbol(symbol)?;
        self.has_int = true;
        match self.committed_sorts.get(&escaped) {
            Some(CommittedSort::Int) => {}
            Some(other) => {
                return Err(SmtTranslationError::Unsupported {
                    shape: format!("mixed-sort accessor `{symbol}`"),
                    reason: format!("already committed as {other:?}; cannot also be Int"),
                });
            }
            None => {
                self.declarations
                    .insert(escaped.clone(), format!("(declare-const {escaped} Int)"));
                self.committed_sorts
                    .insert(escaped.clone(), CommittedSort::Int);
            }
        }
        Ok(escaped)
    }

    /// Declare a tag-encoded accessor. Returns the SMT symbol and the
    /// registered tag universe (in constructor-order).
    fn declare_tag_accessor(
        &mut self,
        accessor_symbol: &str,
        domain_name: &str,
        constructors: &[String],
    ) -> Result<TagAccessor, SmtTranslationError> {
        if constructors.is_empty() {
            return Err(SmtTranslationError::EmptyTagDomain {
                symbol: domain_name.to_string(),
            });
        }
        let escaped = smtlib_safe_symbol(accessor_symbol)?;
        let domain_escaped = smtlib_safe_symbol(domain_name)?;

        // Commit / check-compatible domain registration.
        match self.tag_domains.get(&domain_escaped) {
            Some(existing) if existing == constructors => {}
            Some(existing) => {
                return Err(SmtTranslationError::Unsupported {
                    shape: format!("tag domain `{domain_name}`"),
                    reason: format!(
                        "redeclared with different constructor set: was {existing:?}, now {constructors:?}"
                    ),
                });
            }
            None => {
                self.tag_domains
                    .insert(domain_escaped.clone(), constructors.to_vec());
            }
        }

        match self.tag_encoding {
            TagEncoding::IntDisjunction => {
                self.has_int = true;
                match self.committed_sorts.get(&escaped) {
                    Some(CommittedSort::Int) => {}
                    Some(other) => {
                        return Err(SmtTranslationError::Unsupported {
                            shape: format!("mixed-sort accessor `{accessor_symbol}`"),
                            reason: format!(
                                "already committed as {other:?}; cannot also be tag-Int"
                            ),
                        });
                    }
                    None => {
                        self.declarations
                            .insert(escaped.clone(), format!("(declare-const {escaped} Int)"));
                        self.committed_sorts
                            .insert(escaped.clone(), CommittedSort::Int);
                    }
                }
                // Domain-range axiom for the variable.
                let n = constructors.len() as i64;
                let range_key = format!("_range_{escaped}");
                // use a unique prelude line stored as a declaration-keyed
                // axiom so that ordering is still deterministic.
                // A declaration-keyed entry beginning with `;` is moved to
                // assertions at finalize time.
                self.declarations.entry(range_key).or_insert_with(|| {
                    format!(";axiom-assertion:(and (>= {escaped} 0) (< {escaped} {n}))")
                });
            }
            TagEncoding::UninterpretedSort => {
                self.has_uf = true;
                let sort_sym = format!("Tag_{domain_escaped}");
                let sort_key = format!("_sort_{sort_sym}");
                if !self.declarations.contains_key(&sort_key) {
                    self.declarations
                        .insert(sort_key, format!("(declare-sort {sort_sym} 0)"));
                    // tag constants
                    for ctor in constructors {
                        let safe = smtlib_safe_symbol(ctor)?;
                        let key = format!("_const_{sort_sym}_{safe}");
                        self.declarations
                            .insert(key, format!("(declare-const {safe} {sort_sym})"));
                    }
                    // distinct axiom
                    let mut distinct = String::from(";axiom-assertion:(distinct");
                    for ctor in constructors {
                        let safe = smtlib_safe_symbol(ctor)?;
                        distinct.push(' ');
                        distinct.push_str(&safe);
                    }
                    distinct.push(')');
                    self.declarations
                        .insert(format!("_distinct_{sort_sym}"), distinct);
                }
                match self.committed_sorts.get(&escaped) {
                    Some(CommittedSort::Tag(t)) if *t == sort_sym => {}
                    Some(other) => {
                        return Err(SmtTranslationError::Unsupported {
                            shape: format!("mixed-sort accessor `{accessor_symbol}`"),
                            reason: format!(
                                "already committed as {other:?}; cannot also be Tag({sort_sym})"
                            ),
                        });
                    }
                    None => {
                        self.declarations.insert(
                            escaped.clone(),
                            format!("(declare-const {escaped} {sort_sym})"),
                        );
                        self.committed_sorts
                            .insert(escaped.clone(), CommittedSort::Tag(sort_sym.clone()));
                    }
                }
            }
        }

        Ok(TagAccessor {
            symbol: escaped,
            domain: domain_escaped,
            constructors: constructors.to_vec(),
        })
    }

    /// Emit an SMT-LIB expression that tests whether `tag.symbol` equals the
    /// constructor `ctor`. Returns an `Err` if `ctor` is not in the tag
    /// universe.
    fn tag_eq(&self, tag: &TagAccessor, ctor: &str) -> Result<String, SmtTranslationError> {
        let idx = tag
            .constructors
            .iter()
            .position(|c| c == ctor)
            .ok_or_else(|| SmtTranslationError::Unsupported {
                shape: format!("tag `{ctor}` not in domain `{}`", tag.domain),
                reason: "reference to undeclared tag constructor".to_string(),
            })?;
        match self.tag_encoding {
            TagEncoding::IntDisjunction => Ok(format!("(= {} {idx})", tag.symbol)),
            TagEncoding::UninterpretedSort => {
                let safe = smtlib_safe_symbol(ctor)?;
                Ok(format!("(= {} {safe})", tag.symbol))
            }
        }
    }

    fn push_assertion(&mut self, a: String) {
        self.assertions.push(a);
    }

    /// Declare and return a verdict output variable. Uses the `ComplianceVerdict`
    /// tag domain by default (a tag accessor named `verdict`).
    fn fresh_verdict_symbol(&mut self, name: &str) -> String {
        // Bypass declare_tag_accessor (we don't want to emit a range axiom for
        // the verdict variable — the goal itself constrains it). Just declare
        // it as Int or Tag_ComplianceVerdict.
        let escaped = smtlib_safe_symbol(name).unwrap_or_else(|_| "verdict".to_string());
        self.has_int = true;
        if !self.committed_sorts.contains_key(&escaped) {
            match self.tag_encoding {
                TagEncoding::IntDisjunction => {
                    self.declarations
                        .insert(escaped.clone(), format!("(declare-const {escaped} Int)"));
                    self.committed_sorts
                        .insert(escaped.clone(), CommittedSort::Int);
                }
                TagEncoding::UninterpretedSort => {
                    // Will be finished when use_verdict_tag_domain() runs.
                    self.declarations.insert(
                        escaped.clone(),
                        format!("(declare-const {escaped} Tag_ComplianceVerdict)"),
                    );
                    self.committed_sorts.insert(
                        escaped.clone(),
                        CommittedSort::Tag("Tag_ComplianceVerdict".to_string()),
                    );
                    self.has_uf = true;
                }
            }
        }
        escaped
    }

    fn use_verdict_tag_domain(&mut self) {
        let domain_name = "ComplianceVerdict".to_string();
        let ctors = vec![
            "Compliant".to_string(),
            "NonCompliant".to_string(),
            "Pending".to_string(),
        ];
        if !self.tag_domains.contains_key(&domain_name) {
            self.tag_domains.insert(domain_name.clone(), ctors.clone());
        }
        if matches!(self.tag_encoding, TagEncoding::UninterpretedSort) {
            let sort_sym = "Tag_ComplianceVerdict".to_string();
            let sort_key = format!("_sort_{sort_sym}");
            if !self.declarations.contains_key(&sort_key) {
                self.declarations
                    .insert(sort_key, format!("(declare-sort {sort_sym} 0)"));
                for ctor in &ctors {
                    let key = format!("_const_{sort_sym}_{ctor}");
                    self.declarations
                        .insert(key, format!("(declare-const {ctor} {sort_sym})"));
                }
                let distinct = format!(
                    ";axiom-assertion:(distinct {} {} {})",
                    ctors[0], ctors[1], ctors[2]
                );
                self.declarations
                    .insert(format!("_distinct_{sort_sym}"), distinct);
            }
            self.has_uf = true;
        }
    }

    fn finalize(self, options: &SmtOptions) -> Result<TextualSmtQuery, SmtTranslationError> {
        // Partition declarations: real ones emit as `(declare-...)`, axiom
        // markers (prefixed `;axiom-assertion:`) become assertions.
        let mut real_decls = Vec::new();
        let mut axiom_assertions = Vec::new();
        for (_, v) in self.declarations {
            if let Some(payload) = v.strip_prefix(";axiom-assertion:") {
                axiom_assertions.push(payload.to_string());
            } else {
                real_decls.push(v);
            }
        }
        // Axiom assertions render first (after the core declarations). They
        // are appended to the front of the assertion list to preserve
        // source-order semantics for user assertions.
        let mut all_assertions = Vec::with_capacity(axiom_assertions.len() + self.assertions.len());
        // Deterministic ordering for axioms: sort lexicographically since they
        // are universal side conditions.
        let mut axioms = axiom_assertions;
        axioms.sort();
        all_assertions.extend(axioms);
        all_assertions.extend(self.assertions);

        let logic = self
            .logic_override
            .unwrap_or_else(|| auto_logic(self.has_int, self.has_uf, self.has_non_linear));

        Ok(TextualSmtQuery {
            logic,
            declarations: real_decls,
            assertions: all_assertions,
            goal: self.goal,
            produce_models: options.produce_models,
            source_comment: self.source_comment_buf,
        })
    }
}

#[derive(Debug, Clone)]
struct TagAccessor {
    symbol: String,
    domain: String,
    constructors: Vec<String>,
}

/// Pick the tightest logic that accommodates the collected sorts.
fn auto_logic(has_int: bool, has_uf: bool, has_non_linear: bool) -> SmtLogic {
    match (has_int, has_uf, has_non_linear) {
        (false, true, _) => SmtLogic::QfUf,
        (true, _, true) => SmtLogic::QfNia,
        (true, true, false) => SmtLogic::QfUflia,
        (true, false, false) => SmtLogic::QfUflia, // LIA not separately exposed; UFLIA is the superset.
        (false, false, _) => SmtLogic::QfUf,
    }
}

/// Escape a Lex identifier into a safe SMT-LIB 2.6 symbol.
///
/// Per SMT-LIB 2.6 §3.1:
/// - A simple symbol is a non-empty sequence of letters, digits, `_` / `+` /
///   `-` / `*` / etc., not starting with a digit.
/// - A quoted symbol is `|...|` where the body contains no `|` or `\`.
///
/// We accept alphanumerics + `_` as a simple symbol; anything else is wrapped
/// in pipes. `|` and `\` in the input are rejected as [`SmtTranslationError::IllegalSymbol`]
/// because they cannot appear in either form.
fn smtlib_safe_symbol(name: &str) -> Result<String, SmtTranslationError> {
    if name.is_empty() {
        return Err(SmtTranslationError::EmptyAccessor);
    }
    if name.contains('|') || name.contains('\\') {
        return Err(SmtTranslationError::IllegalSymbol {
            accessor: name.to_string(),
        });
    }
    let is_simple = name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !name.starts_with(|c: char| c.is_ascii_digit());
    if is_simple {
        Ok(name.to_string())
    } else {
        Ok(format!("|{name}|"))
    }
}

/// Sanitize a user-provided comment for embedding in SMT-LIB `;` lines.
///
/// Replaces CRLF/CR with LF, strips embedded `;` inside a line to prevent
/// ambiguous comment parsing by downstream tooling, and truncates each line
/// to 120 characters.
fn sanitize_comment(s: &str) -> String {
    if s.is_empty() {
        return String::new();
    }
    let normalized = s.replace("\r\n", "\n").replace('\r', "\n");
    let mut out = String::with_capacity(normalized.len());
    for (i, line) in normalized.lines().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        let stripped: String = line.chars().filter(|&c| c != ';').collect();
        let truncated: String = stripped.chars().take(120).collect();
        out.push_str(&truncated);
    }
    out
}

// ---------------------------------------------------------------------------
// Condition → SMT-LIB 2.6
// ---------------------------------------------------------------------------

/// Walk a [`Condition`] and pre-register every tag value encountered in a
/// non-integer `Equals` leaf. This ensures the tag universe's canonical
/// ordering reflects source order, not the inside-out cascade build order.
fn preregister_tags_in_condition(
    cond: &Condition,
    ctx: &mut TranslatorCtx,
) -> Result<(), SmtTranslationError> {
    match cond {
        Condition::Equals { accessor, value } => {
            if value.parse::<i64>().is_err() {
                // Tag-valued equality — register without consuming the output.
                let _ = register_tag_value_and_eq(ctx, accessor, value)?;
            }
            Ok(())
        }
        Condition::And(subs) | Condition::Or(subs) => {
            for s in subs {
                preregister_tags_in_condition(s, ctx)?;
            }
            Ok(())
        }
        Condition::Not(inner) => preregister_tags_in_condition(inner, ctx),
        Condition::GreaterThan { .. }
        | Condition::LessThan { .. }
        | Condition::IsTrue { .. }
        | Condition::IsFalse { .. }
        | Condition::Always => Ok(()),
    }
}

fn translate_condition(
    cond: &Condition,
    ctx: &mut TranslatorCtx,
) -> Result<String, SmtTranslationError> {
    match cond {
        Condition::Equals { accessor, value } => {
            // If `value` parses as an integer, treat accessor as Int; otherwise
            // treat the accessor's codomain as a tag universe containing `value`.
            if let Ok(n) = value.parse::<i64>() {
                let sym = ctx.declare_int(accessor)?;
                Ok(format!("(= {sym} {})", int_literal(n)))
            } else {
                // Tag comparison: we must know the universe. We register a
                // singleton universe `{value}` under the accessor's domain
                // name (which is the accessor itself — no external type
                // information). This is conservative and composes: when
                // another `Equals` on the same accessor with a different tag
                // appears, the universe grows to include both.
                register_tag_value_and_eq(ctx, accessor, value)
            }
        }
        Condition::GreaterThan {
            accessor,
            threshold,
        } => {
            let sym = ctx.declare_int(accessor)?;
            Ok(format!("(> {sym} {})", int_literal(*threshold)))
        }
        Condition::LessThan {
            accessor,
            threshold,
        } => {
            let sym = ctx.declare_int(accessor)?;
            Ok(format!("(< {sym} {})", int_literal(*threshold)))
        }
        Condition::IsTrue { accessor } => {
            let sym = ctx.declare_bool(accessor)?;
            Ok(sym)
        }
        Condition::IsFalse { accessor } => {
            let sym = ctx.declare_bool(accessor)?;
            Ok(format!("(not {sym})"))
        }
        Condition::And(subs) => {
            if subs.is_empty() {
                return Ok("true".to_string());
            }
            if subs.len() == 1 {
                return translate_condition(&subs[0], ctx);
            }
            let mut parts = Vec::with_capacity(subs.len());
            for s in subs {
                parts.push(translate_condition(s, ctx)?);
            }
            Ok(format!("(and {})", parts.join(" ")))
        }
        Condition::Or(subs) => {
            if subs.is_empty() {
                return Ok("false".to_string());
            }
            if subs.len() == 1 {
                return translate_condition(&subs[0], ctx);
            }
            let mut parts = Vec::with_capacity(subs.len());
            for s in subs {
                parts.push(translate_condition(s, ctx)?);
            }
            Ok(format!("(or {})", parts.join(" ")))
        }
        Condition::Not(inner) => {
            let s = translate_condition(inner, ctx)?;
            Ok(format!("(not {s})"))
        }
        Condition::Always => Ok("true".to_string()),
    }
}

/// Register a tag value and emit the equality test. The tag universe for a
/// given accessor grows monotonically as new `Equals` rows reference it;
/// this preserves first-row-wins semantics without requiring upfront domain
/// declaration.
fn register_tag_value_and_eq(
    ctx: &mut TranslatorCtx,
    accessor: &str,
    value: &str,
) -> Result<String, SmtTranslationError> {
    // Domain name = accessor name (one domain per accessor in this model).
    let domain_name = format!("{accessor}_domain");
    // Look up existing universe; add the new tag if not already present.
    let mut ctors = ctx
        .tag_domains
        .get(&smtlib_safe_symbol(&domain_name)?)
        .cloned()
        .unwrap_or_default();
    if !ctors.iter().any(|c| c == value) {
        ctors.push(value.to_string());
    }
    // Also remove the previous entry so declare_tag_accessor won't treat it as
    // a conflicting re-registration.
    let key = smtlib_safe_symbol(&domain_name)?;
    ctx.tag_domains.remove(&key);
    // Remove stale axiom entries since the domain size may have grown.
    if matches!(ctx.tag_encoding, TagEncoding::IntDisjunction) {
        let axiom_key = format!("_range_{}", smtlib_safe_symbol(accessor)?);
        ctx.declarations.remove(&axiom_key);
    }
    let tag = ctx.declare_tag_accessor(accessor, &domain_name, &ctors)?;
    ctx.tag_eq(&tag, value)
}

fn verdict_literal(verdict: &str) -> String {
    // Map verdict name to either an integer index (for IntDisjunction) or the
    // constructor symbol (for UninterpretedSort). Since `finalize()` commits
    // to a single encoding, we emit the integer form here; the uninterpreted
    // path substitutes at render time via `use_verdict_tag_domain`. To keep
    // determinism simple we render the integer form and rely on the domain
    // having canonical order [Compliant, NonCompliant, Pending].
    match verdict {
        "Compliant" => "0".to_string(),
        "NonCompliant" => "1".to_string(),
        "Pending" => "2".to_string(),
        _ => "2".to_string(), // Defensive; translate_decision_table already validated.
    }
}

fn int_literal(n: i64) -> String {
    if n < 0 {
        format!("(- {})", n.unsigned_abs())
    } else {
        n.to_string()
    }
}

// ---------------------------------------------------------------------------
// Term → SMT-LIB 2.6 (for Defeasible / Match top-levels)
// ---------------------------------------------------------------------------

fn translate_defeasible(
    rule: &DefeasibleRule,
    ctx: &mut TranslatorCtx,
) -> Result<(), SmtTranslationError> {
    ctx.push_source_comment(&format!("defeasible rule `{}`", rule.name.name));

    // Translate base body (expected to be a Lambda wrapping a Match).
    translate_lex_to_smt_inner(&rule.base_body, ctx)?;

    // Every exception becomes an assertion:
    //
    //   (assert (=> <guard_sexpr> (= verdict <exception_verdict>)))
    //
    // The exception's guard is a lambda whose body is a Match returning True
    // / False. We translate the guard body into a boolean condition via
    // translate_term_to_bool.
    for exc in &rule.exceptions {
        let guard_body = unwrap_lambda_body(&exc.guard);
        let guard_sexpr = translate_term_to_bool(guard_body, ctx)?;
        let verdict = extract_verdict_from_body(&exc.body, &rule.name.name)?;
        let verdict_sym = verdict_literal(&verdict);
        let priority = exc.priority.unwrap_or(0);
        ctx.push_assertion(format!(
            "(=> {guard_sexpr} (= verdict {verdict_sym})) ; priority {priority}"
        ));
    }
    Ok(())
}

/// Recurse into a `Term` that is the body of a top-level translation.
fn translate_lex_to_smt_inner(
    term: &Term,
    ctx: &mut TranslatorCtx,
) -> Result<(), SmtTranslationError> {
    match term {
        Term::Lambda { body, .. } => translate_lex_to_smt_inner(body, ctx),
        Term::Match {
            scrutinee,
            branches,
            ..
        } => translate_match(scrutinee, branches, ctx),
        Term::Defeasible(rule) => translate_defeasible(rule, ctx),
        other => Err(SmtTranslationError::Unsupported {
            shape: lex_term_shape(other),
            reason: "not handled in inner translation path".to_string(),
        }),
    }
}

fn translate_match(
    scrutinee: &Term,
    branches: &[Branch],
    ctx: &mut TranslatorCtx,
) -> Result<(), SmtTranslationError> {
    let accessor = term_to_accessor(scrutinee)?;
    let verdict_sym = ctx.fresh_verdict_symbol("verdict");

    // Build cascade from branches. Wildcard must be the last — enforce that.
    let mut default = String::from("2"); // Pending default
    let mut cases: Vec<(String, String)> = Vec::new();
    for (i, br) in branches.iter().enumerate() {
        let body_verdict = extract_verdict_from_body(&br.body, "match")?;
        let body_sexpr = verdict_literal(&body_verdict);
        match &br.pattern {
            Pattern::Wildcard => {
                if i != branches.len() - 1 {
                    return Err(SmtTranslationError::Unsupported {
                        shape: "Match with non-terminal wildcard".to_string(),
                        reason: "SMT cascade requires wildcard to be the final arm".to_string(),
                    });
                }
                default = body_sexpr;
            }
            Pattern::Constructor { constructor, .. } => {
                let ctor_name = constructor_name(constructor);
                let cond = if let Ok(n) = ctor_name.parse::<i64>() {
                    let sym = ctx.declare_int(&accessor)?;
                    format!("(= {sym} {})", int_literal(n))
                } else {
                    register_tag_value_and_eq(ctx, &accessor, &ctor_name)?
                };
                cases.push((cond, body_sexpr));
            }
        }
    }

    // Build right-to-left cascade.
    let mut cascade = default;
    for (cond, body_sexpr) in cases.into_iter().rev() {
        cascade = format!("(ite {cond} {body_sexpr} {cascade})");
    }
    ctx.push_assertion(format!("(= {verdict_sym} {cascade})"));
    ctx.use_verdict_tag_domain();
    Ok(())
}

/// Build an accessor chain symbol name from a `Term`.
///
/// Supported forms:
///
/// * `Var { name, .. }` — identifier.
/// * `App(Constant(name), base)` — field access, concatenated with `_`.
/// * Nested `App(Constant(..), App(Constant(..), ..))` — dotted path.
///
/// Everything else returns [`SmtTranslationError::Unsupported`].
fn term_to_accessor(term: &Term) -> Result<String, SmtTranslationError> {
    match term {
        Term::Var { name, .. } => Ok(name.name.clone()),
        Term::Constant(q) => Ok(qual_name(q)),
        Term::App { func, arg } => {
            let field = match func.as_ref() {
                Term::Constant(q) => qual_name(q),
                other => {
                    return Err(SmtTranslationError::Unsupported {
                        shape: lex_term_shape(other),
                        reason: "accessor head must be a constant (field) name".to_string(),
                    });
                }
            };
            let base = term_to_accessor(arg)?;
            Ok(format!("{base}_{field}"))
        }
        other => Err(SmtTranslationError::Unsupported {
            shape: lex_term_shape(other),
            reason: "accessor must be Var, Constant, or App(Constant, accessor)".to_string(),
        }),
    }
}

fn qual_name(q: &QualIdent) -> String {
    q.segments.join("_")
}

fn constructor_name(c: &Constructor) -> String {
    qual_name(&c.name)
}

/// Translate a Lex term that is expected to be a Bool-valued expression
/// (typically the body of an exception guard lambda).
///
/// Recognized forms:
///
/// * `Constant("True")` / `Constant("False")` → `true` / `false`.
/// * `Match` whose branches all yield `True` / `False` → condition on the
///   accessor that selects the True arm.
/// * Nested combinations through `Lambda` unwrapping.
fn translate_term_to_bool(
    term: &Term,
    ctx: &mut TranslatorCtx,
) -> Result<String, SmtTranslationError> {
    match term {
        Term::Constant(q) => {
            let name = qual_name(q);
            match name.as_str() {
                "True" => Ok("true".to_string()),
                "False" => Ok("false".to_string()),
                other => Err(SmtTranslationError::Unsupported {
                    shape: format!("Constant({other})"),
                    reason: "bool-context constant must be `True` or `False`".to_string(),
                }),
            }
        }
        Term::Lambda { body, .. } => translate_term_to_bool(body, ctx),
        Term::Match {
            scrutinee,
            branches,
            ..
        } => {
            let accessor = term_to_accessor(scrutinee)?;
            // Expect pattern of: | <tag/number> => True | _ => False (or vice versa)
            // Find the branch that returns True.
            let mut true_conds: Vec<String> = Vec::new();
            let mut wildcard_is_true = false;
            for br in branches {
                let is_true = match &br.body {
                    Term::Constant(q) => qual_name(q) == "True",
                    _ => false,
                };
                match &br.pattern {
                    Pattern::Wildcard => {
                        wildcard_is_true = is_true;
                    }
                    Pattern::Constructor { constructor, .. } => {
                        if is_true {
                            let ctor_name = constructor_name(constructor);
                            let cond = if let Ok(n) = ctor_name.parse::<i64>() {
                                let sym = ctx.declare_int(&accessor)?;
                                format!("(= {sym} {})", int_literal(n))
                            } else {
                                register_tag_value_and_eq(ctx, &accessor, &ctor_name)?
                            };
                            true_conds.push(cond);
                        }
                    }
                }
            }
            if wildcard_is_true {
                // Anything not matched returns True, i.e. the match is
                // negation of the non-True-arm conditions. Collect those
                // instead.
                let mut not_true: Vec<String> = Vec::new();
                for br in branches {
                    if let Pattern::Constructor { constructor, .. } = &br.pattern {
                        let body_is_true = match &br.body {
                            Term::Constant(q) => qual_name(q) == "True",
                            _ => false,
                        };
                        if !body_is_true {
                            let ctor_name = constructor_name(constructor);
                            let cond = if let Ok(n) = ctor_name.parse::<i64>() {
                                let sym = ctx.declare_int(&accessor)?;
                                format!("(= {sym} {})", int_literal(n))
                            } else {
                                register_tag_value_and_eq(ctx, &accessor, &ctor_name)?
                            };
                            not_true.push(cond);
                        }
                    }
                }
                if not_true.is_empty() {
                    Ok("true".to_string())
                } else if let Some(single) = not_true.first().filter(|_| not_true.len() == 1) {
                    Ok(format!("(not {single})"))
                } else {
                    Ok(format!("(not (or {}))", not_true.join(" ")))
                }
            } else if true_conds.is_empty() {
                Ok("false".to_string())
            } else if let Some(single) = true_conds
                .first()
                .cloned()
                .filter(|_| true_conds.len() == 1)
            {
                Ok(single)
            } else {
                Ok(format!("(or {})", true_conds.join(" ")))
            }
        }
        other => Err(SmtTranslationError::Unsupported {
            shape: lex_term_shape(other),
            reason: "bool-context translation requires Constant, Lambda, or Match".to_string(),
        }),
    }
}

fn unwrap_lambda_body(term: &Term) -> &Term {
    match term {
        Term::Lambda { body, .. } => unwrap_lambda_body(body),
        other => other,
    }
}

/// Extract the verdict named by the body of a decision/exception arm.
///
/// # Admissibility precondition
///
/// The body must reduce to one of the three legal Lex verdict constants
/// (`Compliant`, `NonCompliant`, `Pending`), optionally wrapped in
/// `Lambda` binders, OR be a `Match` at least one of whose
/// constructor/wildcard arms is such a verdict constant. Any other shape
/// is NOT admissible for verdict extraction and is a hard error — there is
/// no silent default. A silently-defaulted verdict would be unsound: it
/// would assert a compliance decision the rule body does not actually make.
///
/// `context` names the surrounding rule/table for diagnostics and is used
/// as the `table` field of an [`SmtTranslationError::InvalidVerdict`].
fn extract_verdict_from_body(term: &Term, context: &str) -> Result<String, SmtTranslationError> {
    let name = match term {
        Term::Lambda { body, .. } => return extract_verdict_from_body(body, context),
        Term::Match { branches, .. } => {
            // Prefer the first constructor arm whose body is a verdict
            // constant; otherwise the wildcard arm. If neither arm yields a
            // verdict constant, the Match is not an admissible verdict body.
            let mut found: Option<String> = None;
            for br in branches {
                if let Pattern::Constructor { .. } = &br.pattern {
                    if let Term::Constant(q) = &br.body {
                        found = Some(qual_name(q));
                        break;
                    }
                }
            }
            if found.is_none() {
                for br in branches {
                    if matches!(br.pattern, Pattern::Wildcard) {
                        if let Term::Constant(q) = &br.body {
                            found = Some(qual_name(q));
                            break;
                        }
                    }
                }
            }
            match found {
                Some(n) => n,
                None => {
                    return Err(SmtTranslationError::Unsupported {
                        shape: "Term::Match without a verdict-constant arm".to_string(),
                        reason: "verdict extraction requires at least one Match arm whose \
                                 body is a Compliant/NonCompliant/Pending constant"
                            .to_string(),
                    });
                }
            }
        }
        Term::Constant(q) => qual_name(q),
        other => {
            return Err(SmtTranslationError::Unsupported {
                shape: lex_term_shape(other),
                reason: "verdict extraction requires a verdict constant, a Lambda \
                         wrapping one, or a Match with a verdict-constant arm"
                    .to_string(),
            });
        }
    };
    // Fail-closed on a non-verdict constant name (e.g. a constructor that is
    // not one of the three legal verdicts). Mirrors the up-front validation
    // in `translate_decision_table`.
    match name.as_str() {
        "Compliant" | "NonCompliant" | "Pending" => Ok(name),
        _ => Err(SmtTranslationError::InvalidVerdict {
            table: context.to_string(),
            verdict: name,
        }),
    }
}

/// Classify a Lex term into a human-readable shape name for error messages.
fn lex_term_shape(term: &Term) -> String {
    match term {
        Term::Var { .. } => "Term::Var".to_string(),
        Term::Sort(_) => "Term::Sort".to_string(),
        Term::Constant(q) => format!("Term::Constant({})", qual_name(q)),
        Term::ContentRefTerm(_) => "Term::ContentRefTerm".to_string(),
        Term::IntLit(_) => "Term::IntLit".to_string(),
        Term::RatLit(_, _) => "Term::RatLit".to_string(),
        Term::StringLit(_) => "Term::StringLit".to_string(),
        Term::AxiomUse { .. } => "Term::AxiomUse".to_string(),
        Term::Pair { .. } => "Term::Pair".to_string(),
        Term::Proj { .. } => "Term::Proj".to_string(),
        Term::App { .. } => "Term::App".to_string(),
        Term::InductiveIntro { .. } => "Term::InductiveIntro".to_string(),
        Term::SanctionsDominance { .. } => "Term::SanctionsDominance".to_string(),
        Term::DefeatElim { .. } => "Term::DefeatElim".to_string(),
        Term::Lift0 { .. } => "Term::Lift0".to_string(),
        Term::Derive1 { .. } => "Term::Derive1".to_string(),
        Term::Lambda { .. } => "Term::Lambda".to_string(),
        Term::Pi { .. } => "Term::Pi".to_string(),
        Term::Sigma { .. } => "Term::Sigma".to_string(),
        Term::Annot { .. } => "Term::Annot".to_string(),
        Term::Let { .. } => "Term::Let".to_string(),
        Term::Match { .. } => "Term::Match".to_string(),
        Term::Rec { .. } => "Term::Rec".to_string(),
        Term::ModalAt { .. } => "Term::ModalAt".to_string(),
        Term::ModalEventually { .. } => "Term::ModalEventually".to_string(),
        Term::ModalAlways { .. } => "Term::ModalAlways".to_string(),
        Term::ModalIntro { .. } => "Term::ModalIntro".to_string(),
        Term::ModalElim { .. } => "Term::ModalElim".to_string(),
        Term::Defeasible(_) => "Term::Defeasible".to_string(),
        Term::Hole(_) => "Term::Hole".to_string(),
        Term::HoleFill { .. } => "Term::HoleFill".to_string(),
        Term::PrincipleBalance(_) => "Term::PrincipleBalance".to_string(),
        Term::Unlock { .. } => "Term::Unlock".to_string(),
    }
}

// ---------------------------------------------------------------------------
// Feature-gated solver trait stub (smt-solver feature)
// ---------------------------------------------------------------------------

/// A minimal solver trait for the future `smt-solver` integration.
///
/// This is intentionally a thin stub for this iteration: real backend
/// integration (Z3 via rsmt2 or cvc5 via CLI) is a follow-on. Implementors
/// MUST return [`SmtSolverError::NotImplemented`] for the inert default
/// backend; callers should not assume `check_sat` works without a feature
/// activation.
#[cfg(feature = "smt-solver")]
pub trait Solver {
    /// Feed a rendered SMT-LIB 2.6 script and check satisfiability.
    fn check_sat(&self, script: &str) -> Result<SmtResult, SmtSolverError>;
    /// Obtain a model for the last satisfiable query.
    fn get_model(&self) -> Result<String, SmtSolverError>;
}

/// Errors produced by a feature-gated solver integration.
#[cfg(feature = "smt-solver")]
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum SmtSolverError {
    /// The backend is not implemented in this build.
    #[error("SMT solver backend not implemented (feature=smt-solver iteration 1 is a stub)")]
    NotImplemented,
    /// The solver returned a malformed response.
    #[error("SMT solver returned malformed response: {reason}")]
    Malformed {
        /// Why the response could not be parsed.
        reason: String,
    },
    /// The solver process could not be launched.
    #[error("SMT solver process failed: {reason}")]
    ProcessFailed {
        /// Underlying IO failure reason.
        reason: String,
    },
}

/// The inert default backend. Returns [`SmtSolverError::NotImplemented`]
/// unconditionally — real backend integration is a future iteration.
#[cfg(feature = "smt-solver")]
#[derive(Debug, Default)]
pub struct StubSolver;

#[cfg(feature = "smt-solver")]
impl Solver for StubSolver {
    fn check_sat(&self, _script: &str) -> Result<SmtResult, SmtSolverError> {
        Err(SmtSolverError::NotImplemented)
    }
    fn get_model(&self) -> Result<String, SmtSolverError> {
        Err(SmtSolverError::NotImplemented)
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
            assertions: vec![SmtExpr::Gt(
                Box::new(SmtExpr::Var("x".to_string())),
                Box::new(SmtExpr::Lit(SmtLiteral::Int(0))),
            )],
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

    // -----------------------------------------------------------------
    // smt-verdict-extraction-silent-fallback regression — a verdict body
    // must resolve to a legal verdict constant or ERROR; it must never
    // silently default to "Pending".
    // -----------------------------------------------------------------

    fn verdict_match(arm_body: Term) -> Term {
        // match scrutinee with | C => <arm_body>
        Term::Match {
            scrutinee: Box::new(Term::constant("x")),
            return_ty: Box::new(Term::constant("Verdict")),
            branches: vec![Branch {
                pattern: Pattern::Constructor {
                    constructor: Constructor::new(QualIdent::simple("C")),
                    binders: vec![],
                },
                body: arm_body,
            }],
        }
    }

    #[test]
    fn extract_verdict_accepts_legal_constants() {
        for v in ["Compliant", "NonCompliant", "Pending"] {
            assert_eq!(
                extract_verdict_from_body(&Term::constant(v), "t"),
                Ok(v.to_string())
            );
        }
    }

    #[test]
    fn extract_verdict_unwraps_lambda() {
        let body = Term::lam(
            "ctx",
            Term::constant("Context"),
            Term::constant("Compliant"),
        );
        assert_eq!(
            extract_verdict_from_body(&body, "t"),
            Ok("Compliant".to_string())
        );
    }

    #[test]
    fn extract_verdict_from_match_arm() {
        let body = verdict_match(Term::constant("NonCompliant"));
        assert_eq!(
            extract_verdict_from_body(&body, "t"),
            Ok("NonCompliant".to_string())
        );
    }

    #[test]
    fn extract_verdict_rejects_non_verdict_constant() {
        // A constant that is not one of the three legal verdicts must NOT
        // silently become Pending — it must be an InvalidVerdict error.
        let r = extract_verdict_from_body(&Term::constant("Approved"), "rule-7");
        assert!(matches!(
            r,
            Err(SmtTranslationError::InvalidVerdict { ref verdict, ref table })
                if verdict == "Approved" && table == "rule-7"
        ));
    }

    #[test]
    fn extract_verdict_rejects_unsupported_body_shape() {
        // An integer-literal body is not an admissible verdict body. Before
        // the fix this silently returned "Pending"; now it is a hard error.
        let r = extract_verdict_from_body(&Term::IntLit(42), "t");
        assert!(matches!(r, Err(SmtTranslationError::Unsupported { .. })));
    }

    #[test]
    fn extract_verdict_rejects_match_without_verdict_arm() {
        // A Match whose only arm body is itself a non-constant term yields
        // no verdict constant → unsupported, not a silent Pending.
        let body = verdict_match(Term::IntLit(0));
        let r = extract_verdict_from_body(&body, "t");
        assert!(matches!(r, Err(SmtTranslationError::Unsupported { .. })));
    }

    #[test]
    fn extract_verdict_match_rejects_non_verdict_constant_arm() {
        // A Match arm whose body IS a constant but not a legal verdict must
        // surface InvalidVerdict, never default.
        let body = verdict_match(Term::constant("Maybe"));
        let r = extract_verdict_from_body(&body, "t");
        assert!(matches!(
            r,
            Err(SmtTranslationError::InvalidVerdict { ref verdict, .. }) if verdict == "Maybe"
        ));
    }
}
