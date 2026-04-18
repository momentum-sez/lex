//! # Lex Core Calculus (Frontier 08)
//!
//! Strongly-typed encoding of the nine PLATONIC-IDEAL §5.1 commitments.
//!
//! This module is a narrow waist between the Lex surface language (AST,
//! parser, elaborator, typechecker in the parent crate) and the proof kernel.
//! Each submodule corresponds to one commitment. See
//! `docs/frontier-work/08-lex-core-calculus.md` for the design and
//! `docs/language-reference.md` for the canonical public scope statement.
//!
//! | # | Commitment                             | Module          |
//! |---|----------------------------------------|-----------------|
//! | 1 | Level-polymorphic rules                | [`level`]       |
//! | 2 | 4-tuple monotonicity                   | [`monotone`]    |
//! | 3 | Temporal stratification                | [`temporal`]    |
//! | 4 | Typed discretion holes (HEADLINE)      | [`hole`]        |
//! | 5 | Proof summary                          | [`summary`]     |
//! | 6 | Principle balancing                    | [`principle`]   |
//! | 7 | Open-world closure / oracle            | [`oracle`]      |
//! | 8 | Derivation certificate                 | [`cert`]        |
//! | 9 | Formal scaffold (out-of-tree)          | `formal/`       |
//!
//! The module is **opt-in**: nothing in the existing Lex pipeline depends on
//! it yet. Downstream consumers (kernel crates, proof assistants, agents) may
//! import this module to obtain the strongly-typed narrow waist.
//!
//! Important boundary: typed discretion holes are executable here and in the
//! formal scaffolds, but the shipped admissible checker in `typecheck.rs`
//! still rejects `Term::Hole` and `Term::HoleFill`.

pub(crate) mod digest;
pub mod cert;
pub mod hole;
pub mod level;
pub mod monotone;
pub mod oracle;
pub mod principle;
pub mod summary;
pub mod temporal;

#[cfg(test)]
pub mod tests;

// Re-export the headline primitives for convenience.
pub use cert::{DerivationCertificate, DiscretionStep};
pub use hole::{Authority, Hole, HoleFill, HoleId, PCAuthWitness, ScopeConstraint};
pub use level::{Lt, MetaRule, Rule, RuleLevel};
pub use monotone::{FourTuple, Proof, TribunalCoercion};
pub use oracle::{Horizon, OracleResponse, WitnessSupplyOracle};
pub use principle::{PrincipleBalancing, PrincipleDeadlock, PrincipleId};
pub use summary::{compile_summary, ProofSummary};
pub use temporal::{Asof, FrozenToken, RewriteWitness};
