//! # lex-core — Lex: A Logic for Jurisdictional Rules
//!
//! Parser, type checker, evaluator, and proof-obligation generator for the
//! Lex calculus. Foundational types (`CanonicalBytes`, `sha256_digest`,
//! `ComplianceDomain`) come from the in-tree `mez-canonical` crate, so the
//! repository compiles from a cold clone with no external checkouts.

pub mod ast;
pub mod certificate;
pub mod compose;
pub mod core_calculus;
pub mod debruijn;
pub mod decide;
pub mod decision_table;
pub mod effects;
pub mod elaborate;
pub mod elaboration_cert;
pub mod evaluate;
pub mod fuel;
pub mod level_check;
pub mod levels;
pub mod lexer;
pub mod obligations;
pub mod open_world;
pub mod oracle_termination;
pub mod parser;
pub mod predicate_narrowing;
pub mod predicate_runtime;
pub mod prelude;
pub mod pretty;
pub mod principles;
pub mod smt;
pub mod temporal;
pub mod token;
pub mod typecheck;

pub use predicate_narrowing::{caveats_narrow, NarrowingError};
pub use predicate_runtime::{
    evaluate as evaluate_predicate, CaveatKind, EvalContext, EvalError, LexCaveat, LexProposition,
    LexValue,
};
