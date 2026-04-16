//! Commitment 7 — Open-world closure with witness-supply oracle.
//!
//! Rules whose proof obligations involve existential quantification over
//! entities (UBO, transitive control chains) must declare a witness-supply
//! oracle — a typed interface the proof kernel queries to materialize the
//! bounded-horizon subgraph at proof time. The oracle's response, including
//! a commitment to the exclusion set at the horizon boundary, becomes part
//! of the proof witness.
//!
//! Unbounded reachability queries decompose into mechanical bounded-depth
//! traversal plus a discretionary hole filled by a signed regulator
//! attestation for the beyond-horizon portion.

use super::digest::sha256_hex;
use super::hole::HoleId;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

// ---------------------------------------------------------------------------
// Horizon — depth bound
// ---------------------------------------------------------------------------

/// A depth bound for a bounded-horizon oracle query.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Horizon(pub u32);

impl Horizon {
    pub fn new(depth: u32) -> Self {
        Horizon(depth)
    }
    pub fn depth(self) -> u32 {
        self.0
    }
}

// ---------------------------------------------------------------------------
// OracleResponse — what an oracle returns
// ---------------------------------------------------------------------------

/// Response from a witness-supply oracle.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OracleResponse<W> {
    /// Witnesses supplied by the oracle (up to the horizon).
    pub witnesses: Vec<W>,
    /// Content-addressed commitment to the set of elements the oracle
    /// searched and excluded. Downstream verifiers can check that no
    /// claimed-excluded element was later supplied as a witness.
    pub exclusion_commitment: String,
    /// The horizon actually reached (may be less than requested if the
    /// observable universe is smaller).
    pub horizon_reached: Horizon,
    /// The oracle's identity.
    pub oracle_id: String,
    /// If the query's natural depth exceeds the horizon, the discretionary
    /// hole identifier to fill the residual.
    pub beyond_horizon: Option<HoleId>,
}

impl<W> OracleResponse<W> {
    /// `true` iff the response is complete within the horizon (no residual
    /// hole was emitted).
    pub fn is_complete(&self) -> bool {
        self.beyond_horizon.is_none()
    }
}

/// Compute an exclusion commitment as `sha256` of the sorted set of
/// excluded element identifiers.
pub fn compute_exclusion_commitment(excluded: &BTreeSet<String>) -> String {
    sha256_hex(excluded)
}

// ---------------------------------------------------------------------------
// WitnessSupplyOracle — the trait
// ---------------------------------------------------------------------------

/// An oracle supplying witnesses to bounded-horizon existential quantifiers.
///
/// Implementations must respect the declared horizon — if the query's natural
/// depth exceeds the horizon, the oracle must emit a discretionary hole
/// rather than silently truncate.
pub trait WitnessSupplyOracle {
    /// The type of query this oracle accepts.
    type Query;
    /// The type of witness this oracle returns.
    type Witness;

    /// Oracle identifier (stable, human-readable).
    fn oracle_id(&self) -> &str;

    /// Supply witnesses for `query` up to `horizon`. If the query's natural
    /// depth exceeds the horizon, the response's `beyond_horizon` field
    /// must be populated with a discretionary hole identifier.
    fn supply_bounded_horizon(
        &self,
        query: Self::Query,
        horizon: Horizon,
    ) -> OracleResponse<Self::Witness>;
}

// ---------------------------------------------------------------------------
// Reference implementation — UBO chain oracle
// ---------------------------------------------------------------------------

/// A reference oracle for ultimate beneficial ownership (UBO) chain
/// queries. The query is a root entity; the oracle traverses ownership
/// edges bounded by the declared horizon.
pub struct UBOOracle {
    pub id: String,
    pub edges: BTreeSet<(String, String)>,
}

impl UBOOracle {
    pub fn new(id: impl Into<String>, edges: BTreeSet<(String, String)>) -> Self {
        Self {
            id: id.into(),
            edges,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UBOQuery {
    pub root: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UBOWitness {
    pub parent: String,
    pub child: String,
    pub depth: u32,
}

impl WitnessSupplyOracle for UBOOracle {
    type Query = UBOQuery;
    type Witness = UBOWitness;

    fn oracle_id(&self) -> &str {
        &self.id
    }

    fn supply_bounded_horizon(
        &self,
        query: Self::Query,
        horizon: Horizon,
    ) -> OracleResponse<Self::Witness> {
        let mut witnesses = Vec::new();
        let mut excluded: BTreeSet<String> = BTreeSet::new();
        let mut seen: BTreeSet<String> = BTreeSet::new();
        let mut frontier: Vec<(String, u32)> = vec![(query.root.clone(), 0)];
        let mut natural_depth_exceeds_horizon = false;
        let mut horizon_reached = 0u32;

        seen.insert(query.root.clone());

        while let Some((node, depth)) = frontier.pop() {
            if depth >= horizon.depth() {
                // Check if there are children beyond the horizon.
                if self.edges.iter().any(|(p, _)| p == &node) {
                    natural_depth_exceeds_horizon = true;
                    // Record the node as an excluded-at-horizon element.
                    excluded.insert(format!("beyond:{}", node));
                }
                continue;
            }
            horizon_reached = horizon_reached.max(depth);
            for (p, c) in &self.edges {
                if p == &node {
                    witnesses.push(UBOWitness {
                        parent: p.clone(),
                        child: c.clone(),
                        depth: depth + 1,
                    });
                    if seen.insert(c.clone()) {
                        frontier.push((c.clone(), depth + 1));
                    }
                } else if c == &node {
                    // Children encountered but not followed (not a parent hop).
                    excluded.insert(format!("sibling:{}:{}", p, c));
                }
            }
        }

        let beyond_horizon = if natural_depth_exceeds_horizon {
            let scope = super::hole::ScopeConstraint {
                jurisdiction: None,
                entity_class: Some("UBO-residual".into()),
                corridor: None,
                time_window: None,
            };
            Some(HoleId::derive(
                &format!("ubo-residual:{}", query.root),
                &scope,
            ))
        } else {
            None
        };

        OracleResponse {
            witnesses,
            exclusion_commitment: compute_exclusion_commitment(&excluded),
            horizon_reached: Horizon(horizon_reached),
            oracle_id: self.id.clone(),
            beyond_horizon,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn edges(pairs: &[(&str, &str)]) -> BTreeSet<(String, String)> {
        pairs
            .iter()
            .map(|(a, b)| (a.to_string(), b.to_string()))
            .collect()
    }

    #[test]
    fn horizon_zero_returns_no_witnesses() {
        let o = UBOOracle::new("ubo-v1", edges(&[("a", "b")]));
        let r = o.supply_bounded_horizon(UBOQuery { root: "a".into() }, Horizon(0));
        assert!(r.witnesses.is_empty());
        assert!(r.beyond_horizon.is_some());
    }

    #[test]
    fn small_tree_within_horizon() {
        let o = UBOOracle::new(
            "ubo-v1",
            edges(&[("root", "a"), ("root", "b"), ("a", "c")]),
        );
        let r = o.supply_bounded_horizon(UBOQuery { root: "root".into() }, Horizon(5));
        assert_eq!(r.witnesses.len(), 3);
        assert!(r.is_complete());
    }

    #[test]
    fn deep_chain_emits_beyond_horizon_hole() {
        let o = UBOOracle::new(
            "ubo-v1",
            edges(&[("a", "b"), ("b", "c"), ("c", "d"), ("d", "e")]),
        );
        let r = o.supply_bounded_horizon(UBOQuery { root: "a".into() }, Horizon(2));
        // At horizon 2 we can emit at most 2 edges.
        assert!(r.witnesses.len() <= 2);
        assert!(!r.is_complete());
        assert!(r.beyond_horizon.is_some());
    }

    #[test]
    fn exclusion_commitment_is_deterministic() {
        let e1: BTreeSet<String> = ["x", "y", "z"].iter().map(|s| s.to_string()).collect();
        let e2 = e1.clone();
        assert_eq!(
            compute_exclusion_commitment(&e1),
            compute_exclusion_commitment(&e2)
        );
    }

    #[test]
    fn exclusion_commitment_is_sensitive() {
        let e1: BTreeSet<String> = ["x"].iter().map(|s| s.to_string()).collect();
        let e2: BTreeSet<String> = ["y"].iter().map(|s| s.to_string()).collect();
        assert_ne!(
            compute_exclusion_commitment(&e1),
            compute_exclusion_commitment(&e2)
        );
    }

    #[test]
    fn beyond_horizon_hole_id_is_deterministic() {
        let o = UBOOracle::new("ubo-v1", edges(&[("a", "b"), ("b", "c"), ("c", "d")]));
        let r1 = o.supply_bounded_horizon(UBOQuery { root: "a".into() }, Horizon(1));
        let r2 = o.supply_bounded_horizon(UBOQuery { root: "a".into() }, Horizon(1));
        assert_eq!(r1.beyond_horizon, r2.beyond_horizon);
    }

    #[test]
    fn horizon_zero_oracle_id_preserved() {
        let o = UBOOracle::new("ubo-v1", edges(&[("a", "b")]));
        let r = o.supply_bounded_horizon(UBOQuery { root: "a".into() }, Horizon(0));
        assert_eq!(r.oracle_id, "ubo-v1");
    }
}
