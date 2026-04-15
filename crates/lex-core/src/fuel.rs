//! Fuel-typed fibers: bounded iteration budget for Lex rule evaluation.
//!
//! Rules that require runtime bounded iteration declare a `Fuel n` effect in
//! the effect row. At evaluation time, a [`FuelTracker`] enforces the budget:
//! each reduction step consumes fuel, and when the budget is exhausted the
//! evaluation halts with a structured [`Indeterminate`] verdict rather than
//! silently failing or diverging.
//!
//! `Indeterminate` is a typed verdict *distinct* from `Compliant`,
//! `NonCompliant`, and `Pending`. It propagates as a structured error and is
//! queued for re-query at a higher horizon (more fuel, more evidence, or a
//! longer wall-clock window).
//!
//! # Usage
//!
//! ```rust
//! use mez_lex::fuel::{Fuel, FuelTracker, Indeterminate};
//!
//! let budget = Fuel::new(100);
//! let mut tracker = FuelTracker::new(budget);
//!
//! // Each step consumes fuel.
//! tracker.consume(10).unwrap();
//! assert_eq!(tracker.remaining(), 90);
//!
//! // Exceeding the budget yields an Indeterminate verdict.
//! let err = tracker.consume(91).unwrap_err();
//! let verdict = Indeterminate::from_exhaustion(err, "aml_screening_loop");
//! assert_eq!(verdict.remaining_fuel_needed, 1);
//! ```

use serde::{Deserialize, Serialize};
use std::fmt;

// ---------------------------------------------------------------------------
// Fuel — the budget value
// ---------------------------------------------------------------------------

/// A fuel budget for bounded evaluation of a Lex rule.
///
/// Wraps a `u64` representing the maximum number of fuel units available.
/// Corresponds to the `Fuel n` effect declared in the rule's effect row.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Fuel(u64);

impl Fuel {
    /// Create a fuel budget with the given amount.
    pub fn new(amount: u64) -> Self {
        Self(amount)
    }

    /// The fuel amount.
    pub fn amount(&self) -> u64 {
        self.0
    }
}

impl fmt::Display for Fuel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Fuel({})", self.0)
    }
}

// ---------------------------------------------------------------------------
// FuelExhausted — error when fuel runs out
// ---------------------------------------------------------------------------

/// Error returned when a [`FuelTracker`] cannot satisfy a `consume` request.
///
/// Contains diagnostic information about the shortfall: how much was
/// requested, how much remained, and therefore how much additional fuel
/// would be needed to satisfy the request.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FuelExhausted {
    /// The fuel amount that was requested.
    pub requested: u64,
    /// The fuel that remained at the time of the request.
    pub remaining: u64,
    /// The shortfall: `requested - remaining`.
    pub shortfall: u64,
}

impl fmt::Display for FuelExhausted {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "fuel exhausted: requested {} but only {} remaining (shortfall {})",
            self.requested, self.remaining, self.shortfall,
        )
    }
}

impl std::error::Error for FuelExhausted {}

// ---------------------------------------------------------------------------
// FuelTracker — runtime fuel accounting
// ---------------------------------------------------------------------------

/// Tracks fuel consumption during Lex rule evaluation.
///
/// Created from a [`Fuel`] budget. Each call to [`consume`](Self::consume)
/// deducts from the remaining balance. When the balance is insufficient,
/// `consume` returns [`FuelExhausted`] without modifying the tracker — the
/// caller can then construct an [`Indeterminate`] verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuelTracker {
    /// The initial fuel budget.
    initial: u64,
    /// Fuel remaining.
    remaining: u64,
}

impl FuelTracker {
    /// Create a new tracker with the given fuel budget.
    pub fn new(fuel: Fuel) -> Self {
        Self {
            initial: fuel.0,
            remaining: fuel.0,
        }
    }

    /// Attempt to consume `amount` fuel units.
    ///
    /// Returns `Ok(())` if sufficient fuel remains, or `Err(FuelExhausted)`
    /// if the remaining balance is less than `amount`. On error the tracker
    /// state is unchanged — no partial deduction occurs.
    pub fn consume(&mut self, amount: u64) -> Result<(), FuelExhausted> {
        if amount > self.remaining {
            Err(FuelExhausted {
                requested: amount,
                remaining: self.remaining,
                shortfall: amount - self.remaining,
            })
        } else {
            self.remaining -= amount;
            Ok(())
        }
    }

    /// Fuel units remaining in the budget.
    pub fn remaining(&self) -> u64 {
        self.remaining
    }

    /// Fuel units consumed so far.
    pub fn consumed(&self) -> u64 {
        self.initial - self.remaining
    }

    /// The initial fuel budget.
    pub fn initial(&self) -> u64 {
        self.initial
    }
}

// ---------------------------------------------------------------------------
// Indeterminate — typed verdict for fuel-exhausted evaluation
// ---------------------------------------------------------------------------

/// A typed verdict indicating that evaluation was *indeterminate* due to
/// fuel exhaustion.
///
/// `Indeterminate` is distinct from `Compliant`, `NonCompliant`, `Pending`,
/// `Exempt`, and `NotApplicable`. It means: "we ran out of computational
/// budget before reaching a definitive answer." The correct response is to
/// re-query at a higher horizon — either with more fuel, after more evidence
/// has arrived, or at a longer wall-clock window.
///
/// Propagates as a structured error, not as a silent default. The
/// `remaining_fuel_needed` field tells the caller the *minimum* additional
/// fuel that would have been needed to continue past the exhaustion point
/// (though the actual total needed may be higher if further iteration is
/// required).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Indeterminate {
    /// Human-readable reason for indeterminacy.
    pub reason: String,
    /// Minimum additional fuel units needed to continue past the exhaustion
    /// point. The actual total to reach a verdict may be higher.
    pub remaining_fuel_needed: u64,
    /// The rule or fiber identifier that was being evaluated.
    pub rule_id: Option<String>,
}

impl Indeterminate {
    /// Construct an `Indeterminate` verdict from a [`FuelExhausted`] error.
    ///
    /// The `rule_id` is an optional identifier for the rule or fiber that
    /// was being evaluated when fuel ran out.
    pub fn from_exhaustion(err: FuelExhausted, rule_id: &str) -> Self {
        Self {
            reason: format!(
                "fuel exhausted during evaluation of '{}': needed {} more unit(s)",
                rule_id, err.shortfall,
            ),
            remaining_fuel_needed: err.shortfall,
            rule_id: Some(rule_id.to_string()),
        }
    }

    /// Construct an `Indeterminate` verdict with a custom reason.
    pub fn with_reason(reason: impl Into<String>, remaining_fuel_needed: u64) -> Self {
        Self {
            reason: reason.into(),
            remaining_fuel_needed,
            rule_id: None,
        }
    }
}

impl fmt::Display for Indeterminate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Indeterminate: {} (need {} more fuel)",
            self.reason, self.remaining_fuel_needed,
        )
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // ── 1. Basic fuel consumption ──────────────────────────────────────

    #[test]
    fn consume_deducts_fuel() {
        let mut tracker = FuelTracker::new(Fuel::new(100));
        assert_eq!(tracker.remaining(), 100);
        assert_eq!(tracker.consumed(), 0);

        tracker.consume(30).unwrap();
        assert_eq!(tracker.remaining(), 70);
        assert_eq!(tracker.consumed(), 30);

        tracker.consume(70).unwrap();
        assert_eq!(tracker.remaining(), 0);
        assert_eq!(tracker.consumed(), 100);
    }

    // ── 2. Exhaustion returns structured error ─────────────────────────

    #[test]
    fn exhaustion_returns_fuel_exhausted() {
        let mut tracker = FuelTracker::new(Fuel::new(50));
        tracker.consume(30).unwrap();

        let err = tracker.consume(25).unwrap_err();
        assert_eq!(err.requested, 25);
        assert_eq!(err.remaining, 20);
        assert_eq!(err.shortfall, 5);

        // Tracker state unchanged after failed consume.
        assert_eq!(tracker.remaining(), 20);
    }

    // ── 3. Indeterminate verdict from exhaustion ───────────────────────

    #[test]
    fn indeterminate_from_exhaustion() {
        let err = FuelExhausted {
            requested: 10,
            remaining: 3,
            shortfall: 7,
        };
        let verdict = Indeterminate::from_exhaustion(err, "aml_screening_loop");

        assert_eq!(verdict.remaining_fuel_needed, 7);
        assert_eq!(verdict.rule_id, Some("aml_screening_loop".to_string()));
        assert!(verdict.reason.contains("aml_screening_loop"));
        assert!(verdict.reason.contains("7"));
    }

    // ── 4. Zero fuel fails immediately ─────────────────────────────────

    #[test]
    fn zero_fuel_fails_immediately() {
        let mut tracker = FuelTracker::new(Fuel::new(0));
        assert_eq!(tracker.remaining(), 0);

        let err = tracker.consume(1).unwrap_err();
        assert_eq!(err.requested, 1);
        assert_eq!(err.remaining, 0);
        assert_eq!(err.shortfall, 1);
    }

    // ── 5. Large fuel budget succeeds ──────────────────────────────────

    #[test]
    fn large_fuel_succeeds() {
        let mut tracker = FuelTracker::new(Fuel::new(u64::MAX));
        // Consume a large amount — should succeed.
        tracker.consume(u64::MAX / 2).unwrap();
        assert_eq!(tracker.remaining(), u64::MAX - u64::MAX / 2);

        // Consume the rest.
        tracker.consume(tracker.remaining()).unwrap();
        assert_eq!(tracker.remaining(), 0);
    }

    // ── 6. Consume zero is always ok ───────────────────────────────────

    #[test]
    fn consume_zero_always_succeeds() {
        let mut tracker = FuelTracker::new(Fuel::new(0));
        tracker.consume(0).unwrap();
        assert_eq!(tracker.remaining(), 0);

        let mut tracker2 = FuelTracker::new(Fuel::new(100));
        tracker2.consume(0).unwrap();
        assert_eq!(tracker2.remaining(), 100);
    }

    // ── 7. Indeterminate with custom reason ────────────────────────────

    #[test]
    fn indeterminate_with_custom_reason() {
        let verdict = Indeterminate::with_reason(
            "oracle timeout during sanctions screening",
            42,
        );
        assert_eq!(verdict.remaining_fuel_needed, 42);
        assert!(verdict.reason.contains("oracle timeout"));
        assert_eq!(verdict.rule_id, None);
    }

    // ── 8. Serde roundtrip for Fuel ────────────────────────────────────

    #[test]
    fn serde_roundtrip_fuel() {
        let fuel = Fuel::new(1024);
        let json = serde_json::to_string(&fuel).unwrap();
        let deserialized: Fuel = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, fuel);
    }

    // ── 9. Serde roundtrip for FuelExhausted ───────────────────────────

    #[test]
    fn serde_roundtrip_fuel_exhausted() {
        let err = FuelExhausted {
            requested: 100,
            remaining: 30,
            shortfall: 70,
        };
        let json = serde_json::to_string(&err).unwrap();
        let deserialized: FuelExhausted = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, err);
    }

    // ── 10. Serde roundtrip for Indeterminate ──────────────────────────

    #[test]
    fn serde_roundtrip_indeterminate() {
        let verdict = Indeterminate::from_exhaustion(
            FuelExhausted {
                requested: 50,
                remaining: 10,
                shortfall: 40,
            },
            "kyc_reverification",
        );
        let json = serde_json::to_string(&verdict).unwrap();
        let deserialized: Indeterminate = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, verdict);
    }

    // ── 11. Display formatting ─────────────────────────────────────────

    #[test]
    fn display_formatting() {
        let fuel = Fuel::new(500);
        assert_eq!(fuel.to_string(), "Fuel(500)");

        let err = FuelExhausted {
            requested: 10,
            remaining: 3,
            shortfall: 7,
        };
        let display = err.to_string();
        assert!(display.contains("10"));
        assert!(display.contains("3"));
        assert!(display.contains("7"));

        let verdict = Indeterminate::with_reason("test", 99);
        let display = verdict.to_string();
        assert!(display.contains("Indeterminate"));
        assert!(display.contains("99"));
    }

    // ── 12. Multiple sequential consumes ───────────────────────────────

    #[test]
    fn multiple_sequential_consumes() {
        let mut tracker = FuelTracker::new(Fuel::new(100));
        for _ in 0..10 {
            tracker.consume(10).unwrap();
        }
        assert_eq!(tracker.remaining(), 0);
        assert_eq!(tracker.consumed(), 100);

        // Next consume should fail.
        let err = tracker.consume(1).unwrap_err();
        assert_eq!(err.shortfall, 1);
    }

    // ── 13. Initial fuel accessor ──────────────────────────────────────

    #[test]
    fn initial_fuel_accessor() {
        let tracker = FuelTracker::new(Fuel::new(256));
        assert_eq!(tracker.initial(), 256);
        assert_eq!(tracker.remaining(), 256);
        assert_eq!(tracker.consumed(), 0);
    }
}
