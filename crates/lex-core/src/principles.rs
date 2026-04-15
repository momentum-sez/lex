//! Principle Conflict Calculus for the Lex proof kernel.
//!
//! Legal principles (protect life, protect property, fulfill contract, preserve
//! public order, maqasid al-shariah) conflict in hard cases. When two cited
//! principles yield contradictory verdicts on the same transition, the proof
//! term must carry a `PrincipleBalancingStep` with explicit reference to
//! precedents.
//!
//! This module implements:
//! - `PrincipleId` — enumeration of legal principles
//! - `CaseCategory` — the categories of transitions where conflicts arise
//! - `BalancingStep` — a first-class balancing step with precedent citations
//! - `PrincipleDeadlock` — the fail-closed error when conflicts are unresolved
//! - `check_acyclicity` — verifies the priority DAG is acyclic on the full
//!   product graph `PrincipleId x CaseCategory`
//!
//! The principle conflict DAG per jurisdiction must be acyclic at fiber-compile
//! time on the full product graph, not its projection. Unresolved collisions
//! fail-closed as `PrincipleDeadlock`.

use std::collections::HashMap;
use std::fmt;

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// PrincipleId — legal principles
// ---------------------------------------------------------------------------

/// A legal principle that may participate in balancing.
///
/// The named variants cover the core principles cited in constitutional,
/// common-law, and Islamic jurisprudence. `Custom` allows jurisdictions to
/// register additional principles.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PrincipleId {
    /// Protection of life and bodily integrity.
    ProtectLife,
    /// Protection of property rights.
    ProtectProperty,
    /// Pacta sunt servanda — contractual obligations must be honored.
    FulfillContract,
    /// Preservation of public order and safety.
    PreservePublicOrder,
    /// Maqasid al-shariah — objectives of Islamic law (preservation of
    /// religion, life, intellect, lineage, wealth).
    MaqasidAlShariah,
    /// A jurisdiction-specific or domain-specific principle.
    Custom(String),
}

impl fmt::Display for PrincipleId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ProtectLife => write!(f, "ProtectLife"),
            Self::ProtectProperty => write!(f, "ProtectProperty"),
            Self::FulfillContract => write!(f, "FulfillContract"),
            Self::PreservePublicOrder => write!(f, "PreservePublicOrder"),
            Self::MaqasidAlShariah => write!(f, "MaqasidAlShariah"),
            Self::Custom(name) => write!(f, "Custom({name})"),
        }
    }
}

// ---------------------------------------------------------------------------
// CaseCategory — transition categories where conflicts arise
// ---------------------------------------------------------------------------

/// The category of case/transition where a principle conflict may arise.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CaseCategory {
    /// Entity formation (incorporation, registration).
    EntityFormation,
    /// Transfer of ownership (shares, assets).
    OwnershipTransfer,
    /// Treasury operations (payments, disbursements).
    TreasuryAction,
    /// Cross-jurisdiction corridor crossing.
    CorridorCrossing,
    /// Compliance evaluation (tensor computation).
    ComplianceEvaluation,
    /// Dispute resolution (arbitration, tribunal).
    DisputeResolution,
    /// A jurisdiction-specific or domain-specific case category.
    Custom(String),
}

impl fmt::Display for CaseCategory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EntityFormation => write!(f, "EntityFormation"),
            Self::OwnershipTransfer => write!(f, "OwnershipTransfer"),
            Self::TreasuryAction => write!(f, "TreasuryAction"),
            Self::CorridorCrossing => write!(f, "CorridorCrossing"),
            Self::ComplianceEvaluation => write!(f, "ComplianceEvaluation"),
            Self::DisputeResolution => write!(f, "DisputeResolution"),
            Self::Custom(name) => write!(f, "Custom({name})"),
        }
    }
}

// ---------------------------------------------------------------------------
// PrincipleEdge — a directed edge in the priority DAG
// ---------------------------------------------------------------------------

/// A directed edge in the principle priority DAG: `winner` prevails over
/// `loser` in the given `case_category`.
///
/// Each edge represents a jurisdiction's settled priority ordering for a
/// specific (principle, case_category) pair.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PrincipleEdge {
    /// The principle that prevails.
    pub winner: PrincipleId,
    /// The case category in which this priority applies.
    pub case_category: CaseCategory,
    /// The principle that yields.
    pub loser: PrincipleId,
}

// ---------------------------------------------------------------------------
// BalancingStep — a first-class principle balancing step
// ---------------------------------------------------------------------------

/// A principle balancing step with explicit precedent citations.
///
/// When two principles yield contradictory verdicts on the same transition,
/// the proof term must carry a `BalancingStep`. Balancing steps are first-class
/// Lex terms.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BalancingStep {
    /// The first principle in the conflict.
    pub principle_a: PrincipleId,
    /// The second principle in the conflict.
    pub principle_b: PrincipleId,
    /// Which principle prevails in this balancing.
    pub resolution: PrincipleId,
    /// Precedent citations justifying the resolution.
    pub precedent_citations: Vec<String>,
    /// The jurisdiction in which this balancing applies.
    pub jurisdiction: String,
    /// The case category where this balancing was required.
    pub case_category: CaseCategory,
}

// ---------------------------------------------------------------------------
// PrincipleDeadlock — fail-closed error for unresolved collisions
// ---------------------------------------------------------------------------

/// Error produced when the principle priority DAG contains a cycle on the
/// full product graph `PrincipleId x CaseCategory`, or when conflicting
/// principles have no settled ordering.
///
/// Unresolved collisions fail-closed: the fiber cannot compile.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrincipleDeadlock {
    /// The principles involved in the cycle or conflict.
    pub conflicting_principles: Vec<PrincipleId>,
    /// The case category in which the deadlock was detected.
    pub case_category: CaseCategory,
    /// The jurisdiction where the deadlock occurs.
    pub jurisdiction: String,
}

impl fmt::Display for PrincipleDeadlock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let principles: Vec<String> = self
            .conflicting_principles
            .iter()
            .map(|p| p.to_string())
            .collect();
        write!(
            f,
            "PrincipleDeadlock in {} for {}: cycle among [{}]",
            self.jurisdiction,
            self.case_category,
            principles.join(" -> ")
        )
    }
}

impl std::error::Error for PrincipleDeadlock {}

// ---------------------------------------------------------------------------
// check_acyclicity — DAG acyclicity on the full product graph
// ---------------------------------------------------------------------------

/// Verify that the principle priority DAG is acyclic on the full product
/// graph `PrincipleId x CaseCategory`.
///
/// The input is a slice of `PrincipleEdge` values, each encoding a directed
/// priority: `winner` prevails over `loser` in the given `case_category`.
/// The check groups edges by case category and runs cycle detection on each
/// per-category sub-graph independently.
///
/// Returns `Ok(())` if acyclic, or `Err(PrincipleDeadlock)` with the first
/// detected cycle. The cycle is reported on the full product graph — not its
/// projection — as required by the Platonic Ideal specification.
pub fn check_acyclicity(
    edges: &[PrincipleEdge],
    jurisdiction: &str,
) -> Result<(), PrincipleDeadlock> {
    // Group edges by case category.
    let mut by_category: HashMap<&CaseCategory, Vec<(&PrincipleId, &PrincipleId)>> =
        HashMap::new();
    for edge in edges {
        by_category
            .entry(&edge.case_category)
            .or_default()
            .push((&edge.winner, &edge.loser));
    }

    // Check each per-category sub-graph for cycles via DFS.
    for (category, category_edges) in &by_category {
        if let Some(cycle) = detect_cycle(category_edges) {
            return Err(PrincipleDeadlock {
                conflicting_principles: cycle,
                case_category: (*category).clone(),
                jurisdiction: jurisdiction.to_string(),
            });
        }
    }

    Ok(())
}

/// DFS-based cycle detection on a directed graph of `PrincipleId` nodes.
///
/// Returns `Some(cycle)` with the principles forming the cycle, or `None`
/// if the graph is acyclic.
fn detect_cycle(edges: &[(&PrincipleId, &PrincipleId)]) -> Option<Vec<PrincipleId>> {
    // Build adjacency list with integer indices for efficient traversal.
    let mut node_to_idx: HashMap<&PrincipleId, usize> = HashMap::new();
    let mut idx_to_node: Vec<&PrincipleId> = Vec::new();

    for (winner, loser) in edges {
        for node in [*winner, *loser] {
            if !node_to_idx.contains_key(node) {
                let idx = idx_to_node.len();
                node_to_idx.insert(node, idx);
                idx_to_node.push(node);
            }
        }
    }

    let n = idx_to_node.len();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (winner, loser) in edges {
        let from = node_to_idx[winner];
        let to = node_to_idx[loser];
        adj[from].push(to);
    }

    // Standard 3-color DFS for cycle detection.
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Color {
        White,
        Gray,
        Black,
    }

    let mut color = vec![Color::White; n];
    let mut parent = vec![usize::MAX; n];

    for start in 0..n {
        if color[start] != Color::White {
            continue;
        }

        let mut stack: Vec<(usize, usize)> = vec![(start, 0)];
        color[start] = Color::Gray;

        while let Some((node, edge_idx)) = stack.last_mut() {
            if *edge_idx < adj[*node].len() {
                let neighbor = adj[*node][*edge_idx];
                *edge_idx += 1;

                match color[neighbor] {
                    Color::White => {
                        color[neighbor] = Color::Gray;
                        parent[neighbor] = *node;
                        stack.push((neighbor, 0));
                    }
                    Color::Gray => {
                        // Cycle found. Reconstruct cycle path.
                        let cycle_end = neighbor;
                        let mut cycle = vec![idx_to_node[cycle_end].clone()];
                        let mut current = *node;
                        while current != cycle_end {
                            cycle.push(idx_to_node[current].clone());
                            current = parent[current];
                        }
                        cycle.push(idx_to_node[cycle_end].clone());
                        cycle.reverse();
                        return Some(cycle);
                    }
                    Color::Black => {}
                }
            } else {
                color[*node] = Color::Black;
                stack.pop();
            }
        }
    }

    None
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn edge(winner: PrincipleId, category: CaseCategory, loser: PrincipleId) -> PrincipleEdge {
        PrincipleEdge {
            winner,
            case_category: category,
            loser,
        }
    }

    // -- Test 1: Acyclic DAG passes -------------------------------------------

    #[test]
    fn acyclic_dag_passes() {
        // ProtectLife > FulfillContract > ProtectProperty (linear chain)
        let edges = vec![
            edge(
                PrincipleId::ProtectLife,
                CaseCategory::EntityFormation,
                PrincipleId::FulfillContract,
            ),
            edge(
                PrincipleId::FulfillContract,
                CaseCategory::EntityFormation,
                PrincipleId::ProtectProperty,
            ),
        ];

        let result = check_acyclicity(&edges, "SC");
        assert!(result.is_ok(), "linear DAG should be acyclic");
    }

    // -- Test 2: Cycle detected -----------------------------------------------

    #[test]
    fn cycle_detected_within_same_category() {
        // A > B > C > A in TreasuryAction — a clear cycle.
        let edges = vec![
            edge(
                PrincipleId::ProtectLife,
                CaseCategory::TreasuryAction,
                PrincipleId::FulfillContract,
            ),
            edge(
                PrincipleId::FulfillContract,
                CaseCategory::TreasuryAction,
                PrincipleId::PreservePublicOrder,
            ),
            edge(
                PrincipleId::PreservePublicOrder,
                CaseCategory::TreasuryAction,
                PrincipleId::ProtectLife,
            ),
        ];

        let result = check_acyclicity(&edges, "ADGM");
        assert!(result.is_err(), "cycle should be detected");

        let deadlock = result.unwrap_err();
        assert_eq!(deadlock.case_category, CaseCategory::TreasuryAction);
        assert_eq!(deadlock.jurisdiction, "ADGM");
        assert!(
            deadlock.conflicting_principles.len() >= 3,
            "cycle should contain at least the 3 conflicting principles"
        );
    }

    // -- Test 3: Deadlock on self-loop ----------------------------------------

    #[test]
    fn self_loop_detected_as_cycle() {
        // A principle that beats itself is a degenerate cycle.
        let edges = vec![edge(
            PrincipleId::MaqasidAlShariah,
            CaseCategory::DisputeResolution,
            PrincipleId::MaqasidAlShariah,
        )];

        let result = check_acyclicity(&edges, "PK");
        assert!(result.is_err(), "self-loop should be detected as cycle");

        let deadlock = result.unwrap_err();
        assert_eq!(deadlock.case_category, CaseCategory::DisputeResolution);
        assert!(deadlock
            .conflicting_principles
            .contains(&PrincipleId::MaqasidAlShariah));
    }

    // -- Test 4: Different categories are independent -------------------------

    #[test]
    fn different_categories_are_independent() {
        // A > B in EntityFormation, B > A in CorridorCrossing — no cycle
        // because these are separate sub-graphs on the product graph.
        let edges = vec![
            edge(
                PrincipleId::ProtectLife,
                CaseCategory::EntityFormation,
                PrincipleId::FulfillContract,
            ),
            edge(
                PrincipleId::FulfillContract,
                CaseCategory::CorridorCrossing,
                PrincipleId::ProtectLife,
            ),
        ];

        let result = check_acyclicity(&edges, "SG");
        assert!(
            result.is_ok(),
            "opposite orderings in different categories are not a cycle"
        );
    }

    // -- Test 5: Empty DAG passes ---------------------------------------------

    #[test]
    fn empty_dag_passes() {
        let result = check_acyclicity(&[], "SC");
        assert!(result.is_ok(), "empty DAG is trivially acyclic");
    }

    // -- Test 6: Balancing step construction and serde -------------------------

    #[test]
    fn balancing_step_serde_roundtrip() {
        let step = BalancingStep {
            principle_a: PrincipleId::ProtectLife,
            principle_b: PrincipleId::FulfillContract,
            resolution: PrincipleId::ProtectLife,
            precedent_citations: vec![
                "R v Dudley & Stephens [1884] UKHL 7".to_string(),
                "Riggs v Palmer, 115 NY 506 (1889)".to_string(),
            ],
            jurisdiction: "SC".to_string(),
            case_category: CaseCategory::TreasuryAction,
        };

        let json = serde_json::to_string(&step).expect("serialize");
        let deserialized: BalancingStep = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(deserialized.principle_a, PrincipleId::ProtectLife);
        assert_eq!(deserialized.principle_b, PrincipleId::FulfillContract);
        assert_eq!(deserialized.resolution, PrincipleId::ProtectLife);
        assert_eq!(deserialized.precedent_citations.len(), 2);
        assert_eq!(deserialized.jurisdiction, "SC");
        assert_eq!(deserialized.case_category, CaseCategory::TreasuryAction);
    }

    // -- Test 7: PrincipleDeadlock display ------------------------------------

    #[test]
    fn principle_deadlock_display() {
        let deadlock = PrincipleDeadlock {
            conflicting_principles: vec![
                PrincipleId::ProtectLife,
                PrincipleId::FulfillContract,
                PrincipleId::ProtectLife,
            ],
            case_category: CaseCategory::OwnershipTransfer,
            jurisdiction: "ADGM".to_string(),
        };

        let display = deadlock.to_string();
        assert!(display.contains("PrincipleDeadlock"));
        assert!(display.contains("ADGM"));
        assert!(display.contains("OwnershipTransfer"));
        assert!(display.contains("ProtectLife"));
        assert!(display.contains("FulfillContract"));
    }

    // -- Test 8: Custom principle and category --------------------------------

    #[test]
    fn custom_principle_and_category_in_dag() {
        let sharia_compliance = PrincipleId::Custom("ShariahBoardApproval".to_string());
        let sukuk_issuance = CaseCategory::Custom("SukukIssuance".to_string());

        let edges = vec![
            edge(
                PrincipleId::MaqasidAlShariah,
                sukuk_issuance.clone(),
                sharia_compliance.clone(),
            ),
            edge(
                sharia_compliance.clone(),
                sukuk_issuance.clone(),
                PrincipleId::FulfillContract,
            ),
        ];

        let result = check_acyclicity(&edges, "BH");
        assert!(result.is_ok(), "linear custom DAG should be acyclic");
    }

    // -- Test 9: Diamond DAG (no cycle) passes --------------------------------

    #[test]
    fn diamond_dag_without_cycle_passes() {
        // A > B, A > C, B > D, C > D — diamond, no cycle.
        let cat = CaseCategory::ComplianceEvaluation;
        let edges = vec![
            edge(PrincipleId::ProtectLife, cat.clone(), PrincipleId::ProtectProperty),
            edge(PrincipleId::ProtectLife, cat.clone(), PrincipleId::FulfillContract),
            edge(PrincipleId::ProtectProperty, cat.clone(), PrincipleId::PreservePublicOrder),
            edge(PrincipleId::FulfillContract, cat.clone(), PrincipleId::PreservePublicOrder),
        ];

        let result = check_acyclicity(&edges, "LU");
        assert!(result.is_ok(), "diamond DAG without back-edge is acyclic");
    }

    // -- Test 10: Multi-category cycle detected in one, not the other ---------

    #[test]
    fn cycle_in_one_category_detected_despite_acyclic_other() {
        // EntityFormation: A > B (acyclic)
        // TreasuryAction: X > Y > X (cycle)
        let edges = vec![
            edge(
                PrincipleId::ProtectLife,
                CaseCategory::EntityFormation,
                PrincipleId::FulfillContract,
            ),
            edge(
                PrincipleId::ProtectProperty,
                CaseCategory::TreasuryAction,
                PrincipleId::PreservePublicOrder,
            ),
            edge(
                PrincipleId::PreservePublicOrder,
                CaseCategory::TreasuryAction,
                PrincipleId::ProtectProperty,
            ),
        ];

        let result = check_acyclicity(&edges, "KY");
        assert!(result.is_err(), "cycle in TreasuryAction should be detected");

        let deadlock = result.unwrap_err();
        assert_eq!(deadlock.case_category, CaseCategory::TreasuryAction);
    }
}
