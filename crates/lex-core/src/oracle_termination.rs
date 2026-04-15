//! Oracle-witnessed termination for Lex rules.
//!
//! Rules that invoke oracles (external decision procedures, sovereign APIs,
//! or off-chain attestation services) cannot be structurally proven to
//! terminate by the Lex type checker alone. Instead, the rule author declares
//! a termination bound: `terminates_by oracle O: depth <= k`. At proof-kernel
//! time, the obligation is discharged by presenting a signed
//! [`OracleAttestation`] — a claim from the oracle operator that the oracle
//! terminates within the declared depth bound.
//!
//! The runtime then checks actual execution depth against the declared bound
//! via [`check_oracle_termination`], producing an [`OracleTerminationProof`]
//! that records whether the bound was respected.
//!
//! # Usage
//!
//! ```rust
//! use lex_core::oracle_termination::{
//!     OracleTerminationDecl, OracleAttestation,
//!     verify_oracle_attestation, check_oracle_termination,
//! };
//!
//! let decl = OracleTerminationDecl {
//!     oracle_id: "sanctions_screening_v2".to_string(),
//!     depth_bound: 100,
//!     signed_attestation: Some("sig-abc123".to_string()),
//! };
//!
//! let attestation = OracleAttestation {
//!     oracle_id: "sanctions_screening_v2".to_string(),
//!     depth_bound: 100,
//!     signature: "sig-abc123".to_string(),
//!     timestamp: "2026-04-15T12:00:00Z".to_string(),
//! };
//!
//! assert!(verify_oracle_attestation(&attestation));
//!
//! let proof = check_oracle_termination(&decl, 42);
//! assert!(proof.within_bound);
//! assert_eq!(proof.actual_depth, 42);
//! ```

use serde::{Deserialize, Serialize};
use std::fmt;

// ---------------------------------------------------------------------------
// OracleTerminationDecl — rule-level declaration
// ---------------------------------------------------------------------------

/// A rule-level declaration that an oracle terminates within a depth bound.
///
/// Corresponds to the Lex syntax:
/// ```text
/// terminates_by oracle O: depth <= k
/// ```
///
/// The `signed_attestation` field, when present, carries the oracle operator's
/// signature string for proof-kernel discharge. If absent, the obligation
/// remains undischarged and the rule cannot be certified.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct OracleTerminationDecl {
    /// Unique identifier for the oracle (e.g., `"sanctions_screening_v2"`).
    pub oracle_id: String,
    /// The declared upper bound on oracle evaluation depth.
    pub depth_bound: u64,
    /// Optional signed attestation from the oracle operator.
    pub signed_attestation: Option<String>,
}

impl fmt::Display for OracleTerminationDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "terminates_by oracle {}: depth <= {}",
            self.oracle_id, self.depth_bound,
        )
    }
}

// ---------------------------------------------------------------------------
// OracleAttestation — signed claim from oracle operator
// ---------------------------------------------------------------------------

/// A signed attestation from an oracle operator claiming that the oracle
/// terminates within a declared depth bound.
///
/// The proof kernel uses this to discharge the termination obligation for
/// rules that invoke the oracle. Verification checks structural validity
/// (non-empty fields, positive depth bound); cryptographic signature
/// verification is deferred to the signing layer (`mez-crypto`).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct OracleAttestation {
    /// The oracle this attestation covers.
    pub oracle_id: String,
    /// The depth bound the oracle operator attests to.
    pub depth_bound: u64,
    /// The operator's signature over (oracle_id, depth_bound, timestamp).
    pub signature: String,
    /// ISO 8601 timestamp of when the attestation was produced.
    pub timestamp: String,
}

impl fmt::Display for OracleAttestation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "OracleAttestation({}, depth <= {}, at {})",
            self.oracle_id, self.depth_bound, self.timestamp,
        )
    }
}

// ---------------------------------------------------------------------------
// verify_oracle_attestation — structural validity check
// ---------------------------------------------------------------------------

/// Verify the structural validity of an [`OracleAttestation`].
///
/// Returns `true` if all of the following hold:
/// - `oracle_id` is non-empty
/// - `depth_bound` is greater than zero
/// - `signature` is non-empty
/// - `timestamp` is non-empty
///
/// This is a structural check only. Cryptographic signature verification
/// is performed at the `mez-crypto` layer when the attestation is bound
/// into a Lex certificate.
pub fn verify_oracle_attestation(attestation: &OracleAttestation) -> bool {
    !attestation.oracle_id.is_empty()
        && attestation.depth_bound > 0
        && !attestation.signature.is_empty()
        && !attestation.timestamp.is_empty()
}

// ---------------------------------------------------------------------------
// OracleTerminationProof — runtime termination evidence
// ---------------------------------------------------------------------------

/// Proof that an oracle invocation terminated within (or exceeded) the
/// declared depth bound.
///
/// Produced by [`check_oracle_termination`] after the oracle has actually
/// executed. The `within_bound` field is `true` if `actual_depth <= depth_bound`
/// and `actual_depth > 0`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct OracleTerminationProof {
    /// The oracle that was invoked.
    pub oracle_id: String,
    /// The depth actually consumed during oracle evaluation.
    pub actual_depth: u64,
    /// Whether the actual depth was within the declared bound.
    pub within_bound: bool,
}

impl fmt::Display for OracleTerminationProof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.within_bound {
            write!(
                f,
                "oracle {} terminated at depth {} (within bound)",
                self.oracle_id, self.actual_depth,
            )
        } else {
            write!(
                f,
                "oracle {} exceeded bound at depth {}",
                self.oracle_id, self.actual_depth,
            )
        }
    }
}

// ---------------------------------------------------------------------------
// check_oracle_termination — runtime bound check
// ---------------------------------------------------------------------------

/// Check whether an oracle invocation terminated within its declared depth
/// bound.
///
/// Returns an [`OracleTerminationProof`] recording the oracle id, actual
/// depth, and whether the bound was respected. The bound is considered
/// respected when `actual_depth <= decl.depth_bound` and `actual_depth > 0`.
/// Zero actual depth is rejected as it indicates the oracle did not execute.
pub fn check_oracle_termination(
    decl: &OracleTerminationDecl,
    actual_depth: u64,
) -> OracleTerminationProof {
    let within_bound = actual_depth > 0 && actual_depth <= decl.depth_bound;
    OracleTerminationProof {
        oracle_id: decl.oracle_id.clone(),
        actual_depth,
        within_bound,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_attestation() -> OracleAttestation {
        OracleAttestation {
            oracle_id: "sanctions_screening_v2".to_string(),
            depth_bound: 100,
            signature: "ed25519:abcdef0123456789".to_string(),
            timestamp: "2026-04-15T12:00:00Z".to_string(),
        }
    }

    fn sample_decl() -> OracleTerminationDecl {
        OracleTerminationDecl {
            oracle_id: "sanctions_screening_v2".to_string(),
            depth_bound: 100,
            signed_attestation: Some("ed25519:abcdef0123456789".to_string()),
        }
    }

    // -- 1. Valid attestation passes verification --------------------------

    #[test]
    fn valid_attestation_passes_verification() {
        let attestation = sample_attestation();
        assert!(verify_oracle_attestation(&attestation));
    }

    // -- 2. Missing signature rejected ------------------------------------

    #[test]
    fn missing_signature_rejected() {
        let attestation = OracleAttestation {
            oracle_id: "oracle_a".to_string(),
            depth_bound: 50,
            signature: String::new(),
            timestamp: "2026-04-15T12:00:00Z".to_string(),
        };
        assert!(!verify_oracle_attestation(&attestation));
    }

    // -- 3. Depth exceeded produces within_bound = false ------------------

    #[test]
    fn depth_exceeded_produces_false() {
        let decl = sample_decl();
        let proof = check_oracle_termination(&decl, 101);
        assert!(!proof.within_bound);
        assert_eq!(proof.actual_depth, 101);
        assert_eq!(proof.oracle_id, "sanctions_screening_v2");
    }

    // -- 4. Depth within bound produces within_bound = true ---------------

    #[test]
    fn depth_within_bound_produces_true() {
        let decl = sample_decl();
        let proof = check_oracle_termination(&decl, 42);
        assert!(proof.within_bound);
        assert_eq!(proof.actual_depth, 42);
    }

    // -- 5. Zero actual depth rejected ------------------------------------

    #[test]
    fn zero_actual_depth_rejected() {
        let decl = sample_decl();
        let proof = check_oracle_termination(&decl, 0);
        assert!(!proof.within_bound);
        assert_eq!(proof.actual_depth, 0);
    }

    // -- 6. Attestation serde roundtrip -----------------------------------

    #[test]
    fn attestation_serde_roundtrip() {
        let attestation = sample_attestation();
        let json = serde_json::to_string(&attestation).unwrap();
        let deserialized: OracleAttestation = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, attestation);
    }

    // -- 7. Decl serde roundtrip ------------------------------------------

    #[test]
    fn decl_serde_roundtrip() {
        let decl = sample_decl();
        let json = serde_json::to_string(&decl).unwrap();
        let deserialized: OracleTerminationDecl = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, decl);
    }

    // -- 8. Proof serde roundtrip -----------------------------------------

    #[test]
    fn proof_serde_roundtrip() {
        let decl = sample_decl();
        let proof = check_oracle_termination(&decl, 75);
        let json = serde_json::to_string(&proof).unwrap();
        let deserialized: OracleTerminationProof = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, proof);
    }

    // -- 9. Empty oracle_id rejected --------------------------------------

    #[test]
    fn empty_oracle_id_rejected() {
        let attestation = OracleAttestation {
            oracle_id: String::new(),
            depth_bound: 50,
            signature: "sig".to_string(),
            timestamp: "2026-04-15T12:00:00Z".to_string(),
        };
        assert!(!verify_oracle_attestation(&attestation));
    }

    // -- 10. Zero depth_bound in attestation rejected ---------------------

    #[test]
    fn zero_depth_bound_in_attestation_rejected() {
        let attestation = OracleAttestation {
            oracle_id: "oracle_b".to_string(),
            depth_bound: 0,
            signature: "sig".to_string(),
            timestamp: "2026-04-15T12:00:00Z".to_string(),
        };
        assert!(!verify_oracle_attestation(&attestation));
    }

    // -- 11. Exact depth bound is within bound ----------------------------

    #[test]
    fn exact_depth_bound_is_within_bound() {
        let decl = sample_decl();
        let proof = check_oracle_termination(&decl, 100);
        assert!(proof.within_bound);
        assert_eq!(proof.actual_depth, 100);
    }

    // -- 12. Display formatting -------------------------------------------

    #[test]
    fn display_formatting() {
        let decl = sample_decl();
        assert!(decl.to_string().contains("sanctions_screening_v2"));
        assert!(decl.to_string().contains("depth <= 100"));

        let attestation = sample_attestation();
        assert!(attestation.to_string().contains("sanctions_screening_v2"));
        assert!(attestation.to_string().contains("depth <= 100"));

        let proof_ok = check_oracle_termination(&decl, 50);
        assert!(proof_ok.to_string().contains("within bound"));

        let proof_exceeded = check_oracle_termination(&decl, 200);
        assert!(proof_exceeded.to_string().contains("exceeded bound"));
    }

    // -- 13. Empty timestamp rejected -------------------------------------

    #[test]
    fn empty_timestamp_rejected() {
        let attestation = OracleAttestation {
            oracle_id: "oracle_c".to_string(),
            depth_bound: 10,
            signature: "sig".to_string(),
            timestamp: String::new(),
        };
        assert!(!verify_oracle_attestation(&attestation));
    }
}
