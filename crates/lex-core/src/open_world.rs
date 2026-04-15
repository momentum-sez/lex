//! Open-world closure discipline for Lex rules.
//!
//! Lex rules that perform existential quantification over unbounded domains
//! (e.g., UBO traversal across ownership chains of unknown depth) cannot be
//! closed under mechanical evaluation alone. The open-world closure discipline
//! separates such queries into two parts:
//!
//! 1. **Mechanical part**: a bounded-depth traversal that the Lex evaluator
//!    can execute within a declared fuel/depth budget.
//! 2. **Discretionary hole**: the residual beyond the horizon, which must be
//!    filled by a declared oracle (a human officer, a sovereign API, or an
//!    attestation service).
//!
//! The [`WitnessSupplyOracle`] declares which oracle is responsible for
//! supplying witnesses beyond the mechanical horizon. The [`OracleEnvelope`]
//! records the oracle's commitment: what it searched, what it excluded, and
//! the digest of the observable universe at query time.
//!
//! [`decompose_query`] splits an [`OpenWorldQuery`] into its mechanical and
//! discretionary parts, enforcing that every open-world quantification carries
//! an explicit oracle declaration.
//!
//! # Usage
//!
//! ```rust
//! use lex_core::open_world::{
//!     WitnessSupplyOracle, OracleEnvelope, OpenWorldQuery,
//!     decompose_query, MechanicalPart, DiscretionaryHole,
//! };
//!
//! let oracle = WitnessSupplyOracle {
//!     oracle_id: "ubo_screening_v3".to_string(),
//!     horizon_k: 5,
//!     query_predicate_hash: "sha256:abc123".to_string(),
//! };
//!
//! let query = OpenWorldQuery {
//!     description: "Traverse ultimate beneficial ownership chain".to_string(),
//!     oracle: oracle.clone(),
//!     quantifier_depth: 8,
//!     predicate_hash: "sha256:abc123".to_string(),
//! };
//!
//! let (mechanical, hole) = decompose_query(&query).unwrap();
//! assert_eq!(mechanical.bounded_depth, 5);
//! assert_eq!(hole.residual_depth, 3);
//! ```

use serde::{Deserialize, Serialize};
use std::fmt;

// ---------------------------------------------------------------------------
// WitnessSupplyOracle — oracle declaration for open-world queries
// ---------------------------------------------------------------------------

/// An oracle declared as the witness supplier for an open-world existential
/// quantification.
///
/// Every open-world query in Lex must declare a `WitnessSupplyOracle`. The
/// oracle is responsible for supplying witnesses (or attesting to their
/// absence) beyond the mechanical horizon `horizon_k`.
///
/// The `query_predicate_hash` binds the oracle declaration to a specific
/// predicate, preventing oracle reuse across unrelated queries.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct WitnessSupplyOracle {
    /// Unique identifier for the oracle (e.g., `"ubo_screening_v3"`).
    pub oracle_id: String,
    /// The depth bound for mechanical traversal. The oracle is responsible
    /// for everything beyond this horizon.
    pub horizon_k: u64,
    /// Hash of the query predicate that the oracle is bound to.
    pub query_predicate_hash: String,
}

impl fmt::Display for WitnessSupplyOracle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "WitnessSupplyOracle({}, horizon={}, predicate={})",
            self.oracle_id, self.horizon_k, self.query_predicate_hash,
        )
    }
}

// ---------------------------------------------------------------------------
// OracleEnvelope — oracle commitment at query time
// ---------------------------------------------------------------------------

/// An oracle's commitment envelope recording what was searched, excluded,
/// and the state of the observable universe at query time.
///
/// When the oracle fills the discretionary hole, it produces an
/// `OracleEnvelope` that the proof kernel binds into the Lex certificate.
/// The `exclusion_set_commitment` is a hash over the entities/paths the
/// oracle determined were not relevant — this makes the oracle's negative
/// claim verifiable.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct OracleEnvelope {
    /// The mechanical depth bound that was used.
    pub horizon_k: u64,
    /// Hash of the query predicate the oracle evaluated.
    pub query_predicate_hash: String,
    /// Commitment (hash) over the exclusion set — the entities/paths the
    /// oracle determined were absent or not matching the predicate.
    pub exclusion_set_commitment: String,
    /// Version of the oracle that produced this envelope.
    pub oracle_version: String,
    /// Digest of the observable universe (registry snapshot, ownership graph
    /// state, etc.) at the time of the oracle query.
    pub observable_universe_digest: String,
}

impl fmt::Display for OracleEnvelope {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "OracleEnvelope(horizon={}, version={}, universe={})",
            self.horizon_k, self.oracle_version, self.observable_universe_digest,
        )
    }
}

// ---------------------------------------------------------------------------
// OpenWorldQuery — an existential quantification with declared oracle
// ---------------------------------------------------------------------------

/// An open-world existential query: "does there exist a witness satisfying
/// predicate P at depth up to N?"
///
/// The `quantifier_depth` is the total depth the query logically requires.
/// The `oracle` declares who is responsible for supplying witnesses beyond
/// the mechanical horizon. The mechanical part handles depths `0..horizon_k`,
/// and the discretionary hole covers `horizon_k..quantifier_depth`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct OpenWorldQuery {
    /// Human-readable description of the query (e.g., "UBO chain traversal").
    pub description: String,
    /// The oracle declared for this query.
    pub oracle: WitnessSupplyOracle,
    /// Total depth of the existential quantification.
    pub quantifier_depth: u64,
    /// Hash of the predicate being searched for.
    pub predicate_hash: String,
}

impl fmt::Display for OpenWorldQuery {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "OpenWorldQuery({}, depth={}, oracle={})",
            self.description, self.quantifier_depth, self.oracle.oracle_id,
        )
    }
}

// ---------------------------------------------------------------------------
// MechanicalPart — bounded-depth traversal that the evaluator handles
// ---------------------------------------------------------------------------

/// The mechanical (bounded-depth) part of a decomposed open-world query.
///
/// This part can be evaluated by the Lex evaluator within the declared
/// fuel budget without oracle involvement.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MechanicalPart {
    /// The bounded depth for mechanical traversal.
    pub bounded_depth: u64,
    /// Hash of the predicate being evaluated mechanically.
    pub predicate_hash: String,
    /// Description inherited from the parent query.
    pub description: String,
}

impl fmt::Display for MechanicalPart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "MechanicalPart(depth={}, predicate={})",
            self.bounded_depth, self.predicate_hash,
        )
    }
}

// ---------------------------------------------------------------------------
// DiscretionaryHole — the residual beyond the horizon
// ---------------------------------------------------------------------------

/// The discretionary hole: the part of the open-world query that lies
/// beyond the mechanical horizon and must be filled by the declared oracle.
///
/// `residual_depth` is the number of additional levels beyond the
/// mechanical horizon (`quantifier_depth - horizon_k`). If `residual_depth`
/// is zero, no discretionary hole exists — the mechanical traversal covers
/// the full query.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DiscretionaryHole {
    /// The oracle responsible for filling this hole.
    pub oracle_id: String,
    /// The depth of the residual beyond the mechanical horizon.
    pub residual_depth: u64,
    /// Hash of the predicate the oracle must evaluate.
    pub predicate_hash: String,
    /// The horizon at which the mechanical part stops.
    pub horizon_k: u64,
}

impl fmt::Display for DiscretionaryHole {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.residual_depth == 0 {
            write!(f, "DiscretionaryHole(none — fully mechanical)")
        } else {
            write!(
                f,
                "DiscretionaryHole(oracle={}, residual_depth={}, from_horizon={})",
                self.oracle_id, self.residual_depth, self.horizon_k,
            )
        }
    }
}

// ---------------------------------------------------------------------------
// DecomposeError — errors in query decomposition
// ---------------------------------------------------------------------------

/// Error returned when an open-world query cannot be decomposed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecomposeError {
    /// The oracle id is empty.
    EmptyOracleId,
    /// The horizon exceeds the quantifier depth (nonsensical — the mechanical
    /// part would exceed the total query depth).
    HorizonExceedsDepth {
        /// The declared horizon.
        horizon_k: u64,
        /// The total quantifier depth.
        quantifier_depth: u64,
    },
    /// The predicate hash on the oracle does not match the query's predicate.
    PredicateMismatch {
        /// The oracle's predicate hash.
        oracle_predicate: String,
        /// The query's predicate hash.
        query_predicate: String,
    },
    /// Zero quantifier depth — the query is vacuous.
    ZeroQuantifierDepth,
}

impl fmt::Display for DecomposeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DecomposeError::EmptyOracleId => write!(f, "oracle_id must not be empty"),
            DecomposeError::HorizonExceedsDepth {
                horizon_k,
                quantifier_depth,
            } => write!(
                f,
                "horizon {} exceeds quantifier depth {}",
                horizon_k, quantifier_depth,
            ),
            DecomposeError::PredicateMismatch {
                oracle_predicate,
                query_predicate,
            } => write!(
                f,
                "predicate mismatch: oracle has {}, query has {}",
                oracle_predicate, query_predicate,
            ),
            DecomposeError::ZeroQuantifierDepth => {
                write!(f, "quantifier depth must be greater than zero")
            }
        }
    }
}

impl std::error::Error for DecomposeError {}

// ---------------------------------------------------------------------------
// decompose_query — split into mechanical part + discretionary hole
// ---------------------------------------------------------------------------

/// Decompose an open-world query into a bounded-depth mechanical traversal
/// and a discretionary hole at the horizon.
///
/// # Errors
///
/// Returns [`DecomposeError`] if:
/// - The oracle id is empty
/// - The horizon exceeds the quantifier depth
/// - The oracle's predicate hash does not match the query's predicate hash
/// - The quantifier depth is zero
pub fn decompose_query(
    query: &OpenWorldQuery,
) -> Result<(MechanicalPart, DiscretionaryHole), DecomposeError> {
    if query.oracle.oracle_id.is_empty() {
        return Err(DecomposeError::EmptyOracleId);
    }

    if query.quantifier_depth == 0 {
        return Err(DecomposeError::ZeroQuantifierDepth);
    }

    if query.oracle.horizon_k > query.quantifier_depth {
        return Err(DecomposeError::HorizonExceedsDepth {
            horizon_k: query.oracle.horizon_k,
            quantifier_depth: query.quantifier_depth,
        });
    }

    if query.oracle.query_predicate_hash != query.predicate_hash {
        return Err(DecomposeError::PredicateMismatch {
            oracle_predicate: query.oracle.query_predicate_hash.clone(),
            query_predicate: query.predicate_hash.clone(),
        });
    }

    let mechanical = MechanicalPart {
        bounded_depth: query.oracle.horizon_k,
        predicate_hash: query.predicate_hash.clone(),
        description: query.description.clone(),
    };

    let residual_depth = query.quantifier_depth - query.oracle.horizon_k;

    let hole = DiscretionaryHole {
        oracle_id: query.oracle.oracle_id.clone(),
        residual_depth,
        predicate_hash: query.predicate_hash.clone(),
        horizon_k: query.oracle.horizon_k,
    };

    Ok((mechanical, hole))
}

// ---------------------------------------------------------------------------
// validate_envelope — check that an oracle envelope is consistent with a query
// ---------------------------------------------------------------------------

/// Validate that an [`OracleEnvelope`] is structurally consistent with an
/// [`OpenWorldQuery`].
///
/// Checks:
/// - Horizon matches the query's oracle horizon
/// - Predicate hash matches the query's predicate
/// - Observable universe digest is non-empty
/// - Oracle version is non-empty
/// - Exclusion set commitment is non-empty
pub fn validate_envelope(
    envelope: &OracleEnvelope,
    query: &OpenWorldQuery,
) -> bool {
    envelope.horizon_k == query.oracle.horizon_k
        && envelope.query_predicate_hash == query.predicate_hash
        && !envelope.observable_universe_digest.is_empty()
        && !envelope.oracle_version.is_empty()
        && !envelope.exclusion_set_commitment.is_empty()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_oracle() -> WitnessSupplyOracle {
        WitnessSupplyOracle {
            oracle_id: "ubo_screening_v3".to_string(),
            horizon_k: 5,
            query_predicate_hash: "sha256:abc123def456".to_string(),
        }
    }

    fn sample_query() -> OpenWorldQuery {
        OpenWorldQuery {
            description: "Traverse ultimate beneficial ownership chain".to_string(),
            oracle: sample_oracle(),
            quantifier_depth: 8,
            predicate_hash: "sha256:abc123def456".to_string(),
        }
    }

    fn sample_envelope() -> OracleEnvelope {
        OracleEnvelope {
            horizon_k: 5,
            query_predicate_hash: "sha256:abc123def456".to_string(),
            exclusion_set_commitment: "sha256:exclusion_commit_789".to_string(),
            oracle_version: "v3.1.0".to_string(),
            observable_universe_digest: "sha256:universe_snap_012".to_string(),
        }
    }

    // -- 1. Successful decomposition ------------------------------------------

    #[test]
    fn decompose_splits_at_horizon() {
        let query = sample_query();
        let (mechanical, hole) = decompose_query(&query).unwrap();

        assert_eq!(mechanical.bounded_depth, 5);
        assert_eq!(mechanical.predicate_hash, "sha256:abc123def456");
        assert_eq!(
            mechanical.description,
            "Traverse ultimate beneficial ownership chain"
        );

        assert_eq!(hole.oracle_id, "ubo_screening_v3");
        assert_eq!(hole.residual_depth, 3);
        assert_eq!(hole.horizon_k, 5);
        assert_eq!(hole.predicate_hash, "sha256:abc123def456");
    }

    // -- 2. Horizon equals depth => zero residual -----------------------------

    #[test]
    fn horizon_equals_depth_yields_zero_residual() {
        let query = OpenWorldQuery {
            description: "Shallow ownership check".to_string(),
            oracle: WitnessSupplyOracle {
                oracle_id: "shallow_oracle".to_string(),
                horizon_k: 3,
                query_predicate_hash: "sha256:pred_a".to_string(),
            },
            quantifier_depth: 3,
            predicate_hash: "sha256:pred_a".to_string(),
        };

        let (mechanical, hole) = decompose_query(&query).unwrap();
        assert_eq!(mechanical.bounded_depth, 3);
        assert_eq!(hole.residual_depth, 0);
        assert!(hole.to_string().contains("fully mechanical"));
    }

    // -- 3. Horizon exceeds depth => error ------------------------------------

    #[test]
    fn horizon_exceeds_depth_rejected() {
        let query = OpenWorldQuery {
            description: "Bad query".to_string(),
            oracle: WitnessSupplyOracle {
                oracle_id: "oracle_x".to_string(),
                horizon_k: 10,
                query_predicate_hash: "sha256:pred_b".to_string(),
            },
            quantifier_depth: 5,
            predicate_hash: "sha256:pred_b".to_string(),
        };

        let err = decompose_query(&query).unwrap_err();
        assert_eq!(
            err,
            DecomposeError::HorizonExceedsDepth {
                horizon_k: 10,
                quantifier_depth: 5,
            }
        );
    }

    // -- 4. Predicate mismatch => error ---------------------------------------

    #[test]
    fn predicate_mismatch_rejected() {
        let query = OpenWorldQuery {
            description: "Mismatched predicates".to_string(),
            oracle: WitnessSupplyOracle {
                oracle_id: "oracle_y".to_string(),
                horizon_k: 3,
                query_predicate_hash: "sha256:oracle_pred".to_string(),
            },
            quantifier_depth: 5,
            predicate_hash: "sha256:query_pred".to_string(),
        };

        let err = decompose_query(&query).unwrap_err();
        match err {
            DecomposeError::PredicateMismatch {
                oracle_predicate,
                query_predicate,
            } => {
                assert_eq!(oracle_predicate, "sha256:oracle_pred");
                assert_eq!(query_predicate, "sha256:query_pred");
            }
            other => panic!("expected PredicateMismatch, got {:?}", other),
        }
    }

    // -- 5. Empty oracle id => error ------------------------------------------

    #[test]
    fn empty_oracle_id_rejected() {
        let query = OpenWorldQuery {
            description: "No oracle".to_string(),
            oracle: WitnessSupplyOracle {
                oracle_id: String::new(),
                horizon_k: 3,
                query_predicate_hash: "sha256:pred_c".to_string(),
            },
            quantifier_depth: 5,
            predicate_hash: "sha256:pred_c".to_string(),
        };

        let err = decompose_query(&query).unwrap_err();
        assert_eq!(err, DecomposeError::EmptyOracleId);
    }

    // -- 6. Zero quantifier depth => error ------------------------------------

    #[test]
    fn zero_quantifier_depth_rejected() {
        let query = OpenWorldQuery {
            description: "Zero-depth query".to_string(),
            oracle: WitnessSupplyOracle {
                oracle_id: "oracle_z".to_string(),
                horizon_k: 0,
                query_predicate_hash: "sha256:pred_d".to_string(),
            },
            quantifier_depth: 0,
            predicate_hash: "sha256:pred_d".to_string(),
        };

        let err = decompose_query(&query).unwrap_err();
        assert_eq!(err, DecomposeError::ZeroQuantifierDepth);
    }

    // -- 7. Envelope validation succeeds for consistent envelope --------------

    #[test]
    fn valid_envelope_passes_validation() {
        let query = sample_query();
        let envelope = sample_envelope();
        assert!(validate_envelope(&envelope, &query));
    }

    // -- 8. Envelope with wrong horizon fails validation ----------------------

    #[test]
    fn envelope_wrong_horizon_fails() {
        let query = sample_query();
        let mut envelope = sample_envelope();
        envelope.horizon_k = 99;
        assert!(!validate_envelope(&envelope, &query));
    }

    // -- 9. Envelope with empty universe digest fails -------------------------

    #[test]
    fn envelope_empty_universe_digest_fails() {
        let query = sample_query();
        let mut envelope = sample_envelope();
        envelope.observable_universe_digest = String::new();
        assert!(!validate_envelope(&envelope, &query));
    }

    // -- 10. Serde roundtrip for all types ------------------------------------

    #[test]
    fn serde_roundtrip() {
        let oracle = sample_oracle();
        let json = serde_json::to_string(&oracle).unwrap();
        let deser: WitnessSupplyOracle = serde_json::from_str(&json).unwrap();
        assert_eq!(deser, oracle);

        let query = sample_query();
        let json = serde_json::to_string(&query).unwrap();
        let deser: OpenWorldQuery = serde_json::from_str(&json).unwrap();
        assert_eq!(deser, query);

        let envelope = sample_envelope();
        let json = serde_json::to_string(&envelope).unwrap();
        let deser: OracleEnvelope = serde_json::from_str(&json).unwrap();
        assert_eq!(deser, envelope);

        // Decomposition results
        let (mech, hole) = decompose_query(&sample_query()).unwrap();
        let json_m = serde_json::to_string(&mech).unwrap();
        let deser_m: MechanicalPart = serde_json::from_str(&json_m).unwrap();
        assert_eq!(deser_m, mech);

        let json_h = serde_json::to_string(&hole).unwrap();
        let deser_h: DiscretionaryHole = serde_json::from_str(&json_h).unwrap();
        assert_eq!(deser_h, hole);
    }

    // -- 11. Display formatting -----------------------------------------------

    #[test]
    fn display_formatting() {
        let oracle = sample_oracle();
        let display = oracle.to_string();
        assert!(display.contains("ubo_screening_v3"));
        assert!(display.contains("horizon=5"));

        let query = sample_query();
        let display = query.to_string();
        assert!(display.contains("depth=8"));
        assert!(display.contains("ubo_screening_v3"));

        let envelope = sample_envelope();
        let display = envelope.to_string();
        assert!(display.contains("horizon=5"));
        assert!(display.contains("v3.1.0"));

        let (mech, hole) = decompose_query(&sample_query()).unwrap();
        assert!(mech.to_string().contains("depth=5"));
        assert!(hole.to_string().contains("residual_depth=3"));

        // DecomposeError display
        let err = DecomposeError::EmptyOracleId;
        assert!(err.to_string().contains("empty"));

        let err = DecomposeError::HorizonExceedsDepth {
            horizon_k: 10,
            quantifier_depth: 5,
        };
        assert!(err.to_string().contains("10"));
        assert!(err.to_string().contains("5"));
    }
}
