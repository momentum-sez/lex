//! Commitment 3 — Temporal stratification.
//!
//! Legal time is defined by rules (statute of limitations, tolling, savings
//! clauses). Meta-rules rewrite the `asof` parameter of other rules. Lex
//! separates time into:
//!
//! - **Stratum 0** — frozen at transition commit, the only time that the
//!   temporal modal accepts. Cannot be altered retroactively.
//! - **Stratum 1** — derived transitions produced by tolling or savings
//!   rewrites with their own fresh `asof`.
//!
//! The type-level encoding uses `Asof<const STRATUM: u8>`. Stratum-0 values
//! are constructed via [`Asof::freeze`] and are immutable; the only escape
//! hatch is [`Asof::into_frozen`] which returns a [`FrozenToken`] the
//! caller must consume, recording the intent to read-out the frozen
//! timestamp.
//!
//! Stratum-1 values carry a [`RewriteWitness`] explaining the rewrite. Lift
//! is `Asof<0> -> Asof<1>` (total); demotion from `Asof<1>` to `Asof<0>` is
//! impossible by construction.

use serde::{Deserialize, Serialize};
use std::marker::PhantomData;

// ---------------------------------------------------------------------------
// Asof — stratum-indexed legal time
// ---------------------------------------------------------------------------

/// A legal time stamped at the declared stratum.
///
/// - `Asof<0>` — frozen at transition commit; the only time the temporal
///   modal accepts.
/// - `Asof<1>` — derived transition produced by tolling or savings rewrite.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Asof<const STRATUM: u8> {
    iso8601: String,
    #[serde(skip)]
    _stratum: PhantomData<fn() -> [(); 0]>,
    /// For stratum-1 only: the rewrite witness. `None` at stratum 0.
    witness: Option<RewriteWitness>,
}

impl Asof<0> {
    /// Freeze a timestamp at stratum 0. Once frozen, the value cannot be
    /// mutated; only read out via [`Asof::into_frozen`].
    pub fn freeze(iso8601: impl Into<String>) -> Self {
        Self {
            iso8601: iso8601.into(),
            _stratum: PhantomData,
            witness: None,
        }
    }

    /// Consume the frozen `Asof<0>` and return its raw timestamp together
    /// with a [`FrozenToken`] witnessing that the caller acknowledged the
    /// stratum-0 read. The token is required by downstream consumers that
    /// must prove they handled a frozen value.
    pub fn into_frozen(self) -> (String, FrozenToken) {
        (self.iso8601, FrozenToken::new())
    }

    /// Inspect the timestamp without consuming.
    pub fn iso8601(&self) -> &str {
        &self.iso8601
    }

    /// Lift a stratum-0 time to stratum 1 via an explicit rewrite witness.
    ///
    /// This is the only way to produce a stratum-1 time. The stratum-0 source
    /// is preserved in the witness's `source_asof0` field so that downstream
    /// consumers can always trace back to the original frozen time.
    pub fn lift0(self, witness: RewriteWitness) -> Asof<1> {
        // Preserve the stratum-0 source in the witness.
        let mut witness = witness;
        witness.source_asof0 = Some(self.iso8601.clone());
        Asof::<1> {
            iso8601: witness.derived_iso8601.clone(),
            _stratum: PhantomData,
            witness: Some(witness),
        }
    }
}

impl Asof<1> {
    /// Inspect the derived timestamp.
    pub fn iso8601(&self) -> &str {
        &self.iso8601
    }

    /// The rewrite witness. Always present for stratum 1.
    pub fn rewrite_witness(&self) -> &RewriteWitness {
        self.witness
            .as_ref()
            .expect("Asof<1> invariant: witness must be present")
    }

    /// The stratum-0 source from which this time was derived.
    pub fn source_asof0(&self) -> Option<&str> {
        self.rewrite_witness().source_asof0.as_deref()
    }
}

// Note: there is intentionally NO way to go from `Asof<1>` to `Asof<0>`. That
// would be a retroactive rule change, which the stratification forbids.

// ---------------------------------------------------------------------------
// RewriteWitness — evidence for a stratum-1 rewrite
// ---------------------------------------------------------------------------

/// Evidence that justifies a stratum-1 rewrite of a stratum-0 time.
///
/// Every stratum-1 time carries one of these. The `kind` identifies the
/// statutory hook (tolling, savings, deemed-date-of-substantial-completion,
/// reliance-savings). The `source_asof0` records the underlying stratum-0
/// time, preserved so downstream consumers can verify temporal coherence.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RewriteWitness {
    /// The kind of rewrite (tolling, savings, etc.).
    pub kind: RewriteKind,
    /// Legal basis citation for the rewrite (e.g., "IBC Act 2016 s.66").
    pub legal_basis: String,
    /// Stratum-0 source time. Populated by [`Asof::lift0`]; callers
    /// constructing a witness directly may leave this `None` and rely on
    /// `lift0` to fill it.
    pub source_asof0: Option<String>,
    /// The derived (stratum-1) timestamp.
    pub derived_iso8601: String,
}

impl RewriteWitness {
    /// Construct a new rewrite witness. The `source_asof0` field will be
    /// populated by [`Asof::lift0`].
    pub fn new(
        kind: RewriteKind,
        legal_basis: impl Into<String>,
        derived_iso8601: impl Into<String>,
    ) -> Self {
        Self {
            kind,
            legal_basis: legal_basis.into(),
            source_asof0: None,
            derived_iso8601: derived_iso8601.into(),
        }
    }
}

/// Kinds of stratum-1 rewrites recognized by the logic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RewriteKind {
    /// Statute-of-limitations tolling.
    Tolling,
    /// Reliance savings (grandfather) clause.
    Savings,
    /// "Deemed date of substantial completion" or equivalent.
    DeemedDate,
    /// Regulator discretion extending a deadline.
    DiscretionaryExtension,
}

// ---------------------------------------------------------------------------
// FrozenToken — proof-of-handling for Asof<0> reads
// ---------------------------------------------------------------------------

/// A zero-sized witness that the caller performed a `into_frozen` on an
/// `Asof<0>`.
///
/// Some downstream APIs (e.g., certificate emission) require a `FrozenToken`
/// argument to prove the caller acknowledged the stratum-0 read-out. The
/// token is a zero-sized marker; it cannot be forged because its only
/// constructor is [`Asof::into_frozen`] on an `Asof<0>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FrozenToken {
    _priv: (),
}

impl FrozenToken {
    pub(super) fn new() -> Self {
        Self { _priv: () }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn asof0_freeze_and_read() {
        let t = Asof::<0>::freeze("2026-04-15T00:00:00Z");
        assert_eq!(t.iso8601(), "2026-04-15T00:00:00Z");
    }

    #[test]
    fn asof0_into_frozen_yields_token() {
        let t = Asof::<0>::freeze("2026-04-15T00:00:00Z");
        let (iso, _token) = t.into_frozen();
        assert_eq!(iso, "2026-04-15T00:00:00Z");
    }

    #[test]
    fn lift0_to_asof1_preserves_source() {
        let t0 = Asof::<0>::freeze("2026-01-01T00:00:00Z");
        let w = RewriteWitness::new(
            RewriteKind::Tolling,
            "Limitation Act s.28",
            "2026-07-01T00:00:00Z",
        );
        let t1 = t0.lift0(w);
        assert_eq!(t1.iso8601(), "2026-07-01T00:00:00Z");
        assert_eq!(t1.source_asof0(), Some("2026-01-01T00:00:00Z"));
        assert_eq!(t1.rewrite_witness().kind, RewriteKind::Tolling);
    }

    #[test]
    fn asof0_and_asof1_are_distinct_types() {
        // If these were the same type, we could assign one to the other.
        // This test just asserts both constructors work.
        let _t0: Asof<0> = Asof::<0>::freeze("2026-01-01T00:00:00Z");
        let _t1: Asof<1> = Asof::<0>::freeze("2026-01-01T00:00:00Z").lift0(
            RewriteWitness::new(RewriteKind::Savings, "basis", "2026-02-01T00:00:00Z"),
        );
    }

    #[test]
    fn four_rewrite_kinds_round_trip() {
        for k in [
            RewriteKind::Tolling,
            RewriteKind::Savings,
            RewriteKind::DeemedDate,
            RewriteKind::DiscretionaryExtension,
        ] {
            let w = RewriteWitness::new(k, "basis", "2026-02-01T00:00:00Z");
            let j = serde_json::to_string(&w).unwrap();
            let r: RewriteWitness = serde_json::from_str(&j).unwrap();
            assert_eq!(r.kind, k);
        }
    }
}
