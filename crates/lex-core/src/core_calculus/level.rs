//! Commitment 1 — Level-polymorphic schema, not ω-limit object.
//!
//! Meta-rules live at one level above the rules they quantify over. Lex
//! terms never quantify over an ω-indexed family of levels. Such
//! quantifications live in the host meta-theory. This module enforces the
//! meta-rule stratification invariant at the Rust type level.
//!
//! The key invariant, from PLATONIC-IDEAL §5.1:
//!
//! > A meta-rule at level ℓ may only quantify over rules at levels strictly
//! > less than ℓ. Self-applying meta-rules are type errors.
//!
//! We encode this using const generics and a sealed `Lt<L>` trait implemented
//! for exactly the levels `0..L`. `MetaRule::<L>::quantify_over::<B>(body)`
//! requires `B: Lt<L>`, so self-application fails at compile time with:
//!
//! ```compile_fail
//! use lex_core::core_calculus::level::{MetaRule, Rule};
//! // A rule at level 2 cannot quantify over itself.
//! let _: MetaRule<2, Rule<2>> = MetaRule::quantify_over(Rule::<2>::placeholder());
//! // ^^^ error[E0277]: the trait `Lt<2>` is not implemented for `Rule<2>`.
//! ```

use crate::ast::Term;
use serde::{Deserialize, Serialize};
use std::marker::PhantomData;

/// The universe level of a rule, carried as a const generic so that the
/// type system enforces level-polymorphic schemas.
///
/// - `Rule<0>` — object-level rules (e.g., "capital requirement").
/// - `Rule<1>` — meta-rules (e.g., "rules enacted by parliament bind
///   regulated entities").
/// - `Rule<2>` — constitutional entrenchment meta-meta-rules.
/// - `Rule<N>` for `N ≥ 3` — higher strata; allowed but rare in practice.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Rule<const LEVEL: u64> {
    /// The underlying term.
    pub term: Term,
    /// Content-addressed digest of the term.
    pub digest: String,
}

impl<const LEVEL: u64> Rule<LEVEL> {
    /// Construct a rule at the declared level.
    pub fn new(term: Term, digest: String) -> Self {
        Self { term, digest }
    }

    /// The level of this rule.
    pub const fn level() -> u64 {
        LEVEL
    }

    /// Placeholder for tests and type-system experiments. The term is an
    /// unresolved constant named `__placeholder__`; do not use in production.
    pub fn placeholder() -> Self {
        use crate::ast::QualIdent;
        Self {
            term: Term::Constant(QualIdent::simple("__placeholder__")),
            digest: format!("placeholder-{}", LEVEL),
        }
    }
}

/// A dynamic level descriptor, for APIs that must accept multiple levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RuleLevel(pub u64);

impl RuleLevel {
    pub const OBJECT: Self = RuleLevel(0);
    pub const META: Self = RuleLevel(1);
    pub const CONSTITUTIONAL: Self = RuleLevel(2);
}

// ---------------------------------------------------------------------------
// Lt<L> — "strictly less than L"
// ---------------------------------------------------------------------------
//
// `Lt<L>` is implemented for a type `T` iff `T` lives at a level strictly
// less than `L`. Because Rust has no const-generic bounds like `where N < L`,
// we emulate the comparison using a private sealed trait and a macro that
// expands to all lawful pairs up to a declared bound.

mod sealed {
    /// Private marker preventing downstream crates from implementing `Lt`.
    pub trait Sealed {}
    impl<const N: u64> Sealed for super::Rule<N> {}
}

/// Types inhabiting `Lt<L>` live at a level strictly less than `L`.
///
/// Only `Rule<N>` for `N < L` implements this trait. Self-application
/// (`Rule<L>: Lt<L>`) is forbidden by the non-instance, producing a
/// compile-time error at any attempt to construct a self-applying meta-rule.
///
/// This trait is sealed; downstream crates cannot add instances.
pub trait Lt<const L: u64>: sealed::Sealed {}

// Macro to generate instances `Rule<N>: Lt<L>` for every pair `N < L` up to
// `MAX_LEVEL`. We provide up to level 8, which covers every level anyone has
// proposed for a real jurisdiction. If a 9th-level meta-rule is ever needed,
// this table extends; doing so is deliberate and auditable.

macro_rules! lt_instances {
    ($($n:literal < $l:literal),* $(,)?) => {
        $(
            impl Lt<$l> for Rule<$n> {}
        )*
    };
}

lt_instances!(
    // Level 0 < L for every L ≥ 1
    0 < 1, 0 < 2, 0 < 3, 0 < 4, 0 < 5, 0 < 6, 0 < 7, 0 < 8,
    // Level 1 < L for every L ≥ 2
    1 < 2, 1 < 3, 1 < 4, 1 < 5, 1 < 6, 1 < 7, 1 < 8,
    // Level 2 < L for every L ≥ 3
    2 < 3, 2 < 4, 2 < 5, 2 < 6, 2 < 7, 2 < 8,
    // Level 3 < L for every L ≥ 4
    3 < 4, 3 < 5, 3 < 6, 3 < 7, 3 < 8,
    // Level 4 < L for every L ≥ 5
    4 < 5, 4 < 6, 4 < 7, 4 < 8,
    // Level 5 < L for every L ≥ 6
    5 < 6, 5 < 7, 5 < 8,
    // Level 6 < L for every L ≥ 7
    6 < 7, 6 < 8,
    // Level 7 < L for every L ≥ 8
    7 < 8,
);

// ---------------------------------------------------------------------------
// MetaRule — quantifies over rules at strictly lower levels
// ---------------------------------------------------------------------------

/// A meta-rule at level `L` that quantifies over a rule of type `B`.
///
/// The constructor [`MetaRule::quantify_over`] requires `B: Lt<L>`, so
/// self-application (e.g., `MetaRule<2>` quantifying over `Rule<2>`) is
/// rejected at compile time. Constitutional entrenchment clauses that refer
/// to themselves are not allowed as `MetaRule`s — they are represented as
/// fixed-point declarations discharged by external witnesses elsewhere.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetaRule<const L: u64, B> {
    body: B,
    _level: PhantomData<fn() -> [(); 0]>,
}

impl<const L: u64, B> MetaRule<L, B>
where
    B: Lt<L>,
{
    /// Construct a meta-rule at level `L` quantifying over `B` (which must
    /// live at a level strictly less than `L`).
    pub fn quantify_over(body: B) -> Self {
        Self {
            body,
            _level: PhantomData,
        }
    }

    /// The quantified-over body.
    pub fn body(&self) -> &B {
        &self.body
    }

    /// The level of this meta-rule.
    pub const fn level() -> u64 {
        L
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rule_level_is_const() {
        assert_eq!(Rule::<0>::level(), 0);
        assert_eq!(Rule::<1>::level(), 1);
        assert_eq!(Rule::<3>::level(), 3);
    }

    #[test]
    fn meta_rule_can_quantify_over_strictly_lower() {
        let object: Rule<0> = Rule::placeholder();
        let meta: MetaRule<1, Rule<0>> = MetaRule::quantify_over(object);
        assert_eq!(MetaRule::<1, Rule<0>>::level(), 1);
        assert_eq!(meta.body().digest, "placeholder-0");
    }

    #[test]
    fn meta_rule_at_level_2_can_quantify_over_level_1() {
        let meta1: Rule<1> = Rule::placeholder();
        let meta2: MetaRule<2, Rule<1>> = MetaRule::quantify_over(meta1);
        assert_eq!(meta2.body().digest, "placeholder-1");
    }

    #[test]
    fn meta_rule_at_level_3_can_quantify_over_level_0() {
        let object: Rule<0> = Rule::placeholder();
        // 0 < 3 by the Lt table
        let _m: MetaRule<3, Rule<0>> = MetaRule::quantify_over(object);
    }

    #[test]
    fn rule_level_marker_types_distinct() {
        // Different const generic values produce different types.
        let _a: Rule<0> = Rule::placeholder();
        let _b: Rule<1> = Rule::placeholder();
        // If these were the same type, the test would be vacuous; they are not.
    }

    // The following tests are COMPILE-TIME guarantees. They are written here
    // as documentation and must be kept in sync with compile_fail tests in
    // the rustdoc at the top of the module.
    //
    // `MetaRule<L, Rule<L>>` — self-application — does NOT compile because
    // `Rule<L>: Lt<L>` is never implemented. This is the enforcement of the
    // forbidden-impredicativity commitment.
}
