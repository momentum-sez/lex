//! Commitment 2 — Curry-Howard monotonicity scoped to the (time, jurisdiction,
//! version, tribunal) 4-tuple.
//!
//! Two tribunals applying the same rule text under divergent interpretive
//! canons construct proof terms inhabiting different propositions even within
//! the same (time, jurisdiction, version) triple. Monotonicity holds only
//! within a fixed 4-tuple; composition across tribunal boundaries requires
//! explicit coercion witnesses that return `None` when canons diverge.
//!
//! We encode the 4-tuple as phantom type parameters on [`Proof`]. Composition
//! is only well-typed at a fixed 4-tuple. Cross-tribunal composition is
//! mediated by the [`TribunalCoercion`] trait whose `coerce` method returns
//! `Option<Proof<_, _, _, To>>` — `None` is the honest answer when canons
//! diverge.
//!
//! ```rust
//! use lex_core::core_calculus::monotone::{FourTuple, Proof};
//!
//! // Phantom jurisdictions/tribunals/versions are zero-sized markers.
//! struct ADGM; struct FSRA;
//! struct V3;
//! #[derive(Debug, Clone, Copy)]
//! struct T2026;
//!
//! let p: Proof<T2026, ADGM, V3, FSRA, ()> = Proof::axiom(());
//! let q: Proof<T2026, ADGM, V3, FSRA, ()> = Proof::axiom(());
//! let r = p.and(q);  // Same 4-tuple: composes.
//! assert_eq!(r.witness(), &((), ()));
//! ```

use serde::{Deserialize, Serialize};
use std::marker::PhantomData;

// ---------------------------------------------------------------------------
// FourTuple — runtime descriptor of (time, jurisdiction, version, tribunal)
// ---------------------------------------------------------------------------

/// Runtime descriptor of the (time, jurisdiction, version, tribunal) 4-tuple.
///
/// This is the value-level counterpart to the phantom-type 4-tuple on
/// [`Proof`]. Diagnostics and certificates embed the runtime descriptor so
/// downstream consumers can inspect the scope of a proof without needing the
/// underlying Rust types.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FourTuple {
    /// Stratum-0 time at which the proof was constructed (ISO 8601).
    pub time: String,
    /// Jurisdiction identifier (e.g., "ADGM", "Seychelles").
    pub jurisdiction: String,
    /// Rule-set version vector (e.g., "v2026.04.15").
    pub version: String,
    /// Tribunal identifier (e.g., "ADGM-FSRA").
    pub tribunal: String,
}

// ---------------------------------------------------------------------------
// Proof — phantom-typed 4-tuple proof term
// ---------------------------------------------------------------------------

/// A proof whose scope is the 4-tuple `(T, J, V, Tr)` encoded in phantom
/// parameters.
///
/// The `W` parameter is the *witness* — the concrete Rust value the proof
/// carries (a term digest, a certificate handle, etc.). Different witnesses
/// at the same 4-tuple compose via the [`Proof::and`] method; composition
/// across different 4-tuples is only possible via explicit coercion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proof<T, J, V, Tr, W = ()> {
    witness: W,
    _scope: PhantomData<(T, J, V, Tr)>,
}

impl<T, J, V, Tr, W> Proof<T, J, V, Tr, W> {
    /// Introduce a proof by axiom (e.g., a signed PCAuth attestation).
    pub fn axiom(witness: W) -> Self {
        Self {
            witness,
            _scope: PhantomData,
        }
    }

    /// The witness carried by this proof.
    pub fn witness(&self) -> &W {
        &self.witness
    }

    /// Consume the proof and return its witness.
    pub fn into_witness(self) -> W {
        self.witness
    }

    /// Compose two proofs at the same 4-tuple. The resulting proof carries
    /// the pair of witnesses.
    pub fn and<W2>(self, other: Proof<T, J, V, Tr, W2>) -> Proof<T, J, V, Tr, (W, W2)> {
        Proof {
            witness: (self.witness, other.witness),
            _scope: PhantomData,
        }
    }

    /// Weaken the witness (functoriality of the scope).
    pub fn map<W2, F: FnOnce(W) -> W2>(self, f: F) -> Proof<T, J, V, Tr, W2> {
        Proof {
            witness: f(self.witness),
            _scope: PhantomData,
        }
    }
}

// ---------------------------------------------------------------------------
// TribunalCoercion — cross-tribunal composition witness
// ---------------------------------------------------------------------------

/// A tribunal coercion witness.
///
/// `TribunalCoercion<From, To>` is a witness that some content under
/// tribunal `From` can be lawfully recognized under tribunal `To` via a
/// canon bridge. The `coerce` method returns `None` when the canons
/// diverge — this is the honest answer. Unlike type-level subsumption
/// which is total, tribunal coercion is partial by design.
///
/// The witness `C` carries the concrete evidence of the bridge (e.g., a
/// Mutual Recognition Agreement digest, a comity order, a reciprocity
/// treaty). Downstream consumers can inspect the witness.
pub trait TribunalCoercion<From, To> {
    /// The kind of evidence the bridge carries (e.g., an MRA digest).
    type BridgeEvidence;

    /// Coerce a proof from tribunal `From` to tribunal `To`.
    ///
    /// Returns `None` when the canons diverge; this is the honest answer
    /// that the platonic ideal requires.
    fn coerce<T, J, V, W>(
        &self,
        proof: Proof<T, J, V, From, W>,
    ) -> Option<Proof<T, J, V, To, (W, Self::BridgeEvidence)>>;
}

/// A trivial self-coercion (every tribunal recognizes its own output).
pub struct IdentityCoercion;

impl<Tr> TribunalCoercion<Tr, Tr> for IdentityCoercion {
    type BridgeEvidence = ();

    fn coerce<T, J, V, W>(
        &self,
        proof: Proof<T, J, V, Tr, W>,
    ) -> Option<Proof<T, J, V, Tr, (W, ())>> {
        Some(proof.map(|w| (w, ())))
    }
}

/// A null coercion — the canons diverge and no bridge exists.
///
/// This is the ordinary case for unrelated tribunals; any attempt to coerce
/// returns `None`. Present as a named type so that diagnostics can attribute
/// the divergence to an explicit ``NoBridge'' witness.
pub struct NoBridge;

impl<From, To> TribunalCoercion<From, To> for NoBridge {
    type BridgeEvidence = std::convert::Infallible;

    fn coerce<T, J, V, W>(
        &self,
        _proof: Proof<T, J, V, From, W>,
    ) -> Option<Proof<T, J, V, To, (W, Self::BridgeEvidence)>> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct ADGM;
    struct SCHL;
    struct V1;
    struct T2026;
    struct FSRA;
    struct FSA;

    #[test]
    fn proof_composes_within_four_tuple() {
        let p: Proof<T2026, ADGM, V1, FSRA, u32> = Proof::axiom(3);
        let q: Proof<T2026, ADGM, V1, FSRA, u32> = Proof::axiom(4);
        let r = p.and(q);
        assert_eq!(r.witness(), &(3, 4));
    }

    #[test]
    fn identity_coercion_roundtrips() {
        let p: Proof<T2026, ADGM, V1, FSRA, u32> = Proof::axiom(42);
        let c = IdentityCoercion;
        let q = c.coerce(p).expect("identity coercion never None");
        assert_eq!(q.witness().0, 42);
    }

    #[test]
    fn no_bridge_always_returns_none() {
        let p: Proof<T2026, ADGM, V1, FSRA, u32> = Proof::axiom(7);
        let c = NoBridge;
        let q: Option<Proof<T2026, ADGM, V1, FSA, _>> = c.coerce(p);
        assert!(q.is_none());
    }

    #[test]
    fn witness_is_preserved_by_map() {
        let p: Proof<T2026, ADGM, V1, FSRA, u32> = Proof::axiom(10);
        let q = p.map(|w| w * 2);
        assert_eq!(q.witness(), &20);
    }

    #[test]
    fn four_tuple_descriptor_hashable() {
        let ft = FourTuple {
            time: "2026-04-15T00:00:00Z".into(),
            jurisdiction: "ADGM".into(),
            version: "v2026.04.15".into(),
            tribunal: "ADGM-FSRA".into(),
        };
        let mut set = std::collections::HashSet::new();
        set.insert(ft.clone());
        assert!(set.contains(&ft));
    }
}
