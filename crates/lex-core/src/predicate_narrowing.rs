//! Caveat narrowing for Lex capability attenuation.
//!
//! At every attenuation step, the child capability's caveat list must be
//! **at least as narrow** as the parent's: every request the child
//! authorises must also be authorised by the parent. This is the
//! subsumption relation `c' ⊑ c` discussed in
//! the public Lex caveat semantics.
//!
//! # Semantics
//!
//! For caveat lists `prev` (parent) and `next` (child), [`caveats_narrow`]
//! returns `Ok(true)` iff for **every** context that satisfies `next`, the
//! same context also satisfies `prev`. Equivalently:
//!
//! ```text
//! ∀ ctx. ⋀(next) ⊨ ⋀(prev)
//! ```
//!
//! # Strategy
//!
//! The runtime predicate fragment (see [`crate::predicate_runtime`]) is
//! small: conjunction, disjunction, negation, equality, ordering,
//! finite-set membership. Narrowing in this fragment is decidable.
//!
//! We implement two decision procedures, chosen per caveat kind:
//!
//! 1. **Structural subsumption** — for the caveat kinds with direct monotone
//!    rules (Monetary, Temporal, Operation, Domain,
//!    Rate, Mcp, Jurisdiction): recognise the canonical predicate shape
//!    and compare numerically / by set inclusion.
//! 2. **Propositional fallback** — for `Custom` caveats and anything the
//!    structural path doesn't recognise, fall through to a generic
//!    finite-ctx SAT: every predicate in our fragment reduces to a
//!    boolean combination of literal constraints, and attr narrowing can
//!    be checked by enumerating the finite set of "relevant" contexts
//!    (each distinct literal in parent ∪ child gives a candidate value
//!    per attribute). This is sound and complete for the fragment and
//!    cheap in practice — capability chains carry at most a handful of
//!    caveats.
//!
//! We intentionally do **not** require the full SMT module here: the caveat
//! fragment this module handles is strictly less expressive than the full
//! Lex logic and the dedicated decision procedure is more predictable in
//! latency (no SMT solver tail).

use std::collections::{BTreeMap, BTreeSet};

use rust_decimal::Decimal;
use thiserror::Error;

use crate::predicate_runtime::{
    evaluate, CaveatKind, EvalContext, EvalError, LexCaveat, LexProposition, LexValue,
};

// ---------------------------------------------------------------------------
// NarrowingError
// ---------------------------------------------------------------------------

/// Errors returned by [`caveats_narrow`].
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum NarrowingError {
    /// Parent has a caveat kind the child does not — child is broader
    /// than parent for that kind.
    #[error("child caveat list is missing kind {0:?} present in parent")]
    MissingKind(CaveatKind),

    /// Structural subsumption failed for a caveat kind with a dedicated
    /// rule. `reason` captures the numeric failure.
    #[error("child caveat (kind {kind:?}) does not narrow parent: {reason}")]
    NotNarrower {
        /// Caveat kind that failed.
        kind: CaveatKind,
        /// Human description of the failure.
        reason: String,
    },

    /// The propositional narrowing check found a witness context that
    /// satisfies the child caveats but not the parent. This is the
    /// definitive refutation of narrowing.
    #[error("propositional narrowing refuted: counterexample context exists")]
    Refuted,

    /// Evaluation failed on a candidate context (e.g., referenced an
    /// attribute with no finite candidate literal). Means the caveat
    /// fragment exceeds what this checker supports; a higher-fidelity
    /// (SMT) check is required.
    #[error("propositional narrowing could not be decided: {0}")]
    Undecidable(String),

    /// Underlying evaluation error surfaced to the caller.
    #[error("evaluation error during narrowing: {0}")]
    Eval(#[from] EvalError),
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Check that `next` (child) narrows `prev` (parent).
///
/// Returns:
/// - `Ok(true)` when every context satisfying the conjunction of `next`
///   caveats also satisfies the conjunction of `prev` caveats.
/// - `Ok(false)` is never returned — instead, this function returns an
///   error. The `Result<bool, _>` return shape is kept to match the
///   task interface, and `Ok(true)` is the only positive verdict.
///
/// When the caveats are structurally comparable, a [`NarrowingError::NotNarrower`]
/// is returned. When only the propositional path applies and a
/// counterexample context exists, a [`NarrowingError::Refuted`] is returned.
pub fn caveats_narrow(prev: &[LexCaveat], next: &[LexCaveat]) -> Result<bool, NarrowingError> {
    // Group caveats by kind.
    let prev_by_kind = group_by_kind(prev);
    let next_by_kind = group_by_kind(next);

    // Every kind present in parent must have a matching narrower kind in child.
    for (kind, p_cavs) in &prev_by_kind {
        let Some(c_cavs) = next_by_kind.get(kind) else {
            return Err(NarrowingError::MissingKind(*kind));
        };
        for p_cav in p_cavs {
            // At least one child caveat of this kind must narrow this
            // parent caveat. The per-kind structural rule decides.
            let mut any_narrower = false;
            for c_cav in c_cavs {
                if structural_narrows(*kind, &c_cav.predicate, &p_cav.predicate)? {
                    any_narrower = true;
                    break;
                }
            }
            if !any_narrower {
                // Fall back to propositional narrowing over the whole
                // child list: even if no single child caveat of this
                // kind dominates structurally, the conjunction may.
                if !propositional_narrows(next, &p_cav.predicate)? {
                    return Err(NarrowingError::NotNarrower {
                        kind: *kind,
                        reason: "no child caveat of the same kind is narrower".to_string(),
                    });
                }
            }
        }
    }

    // Custom caveats: the child adds a constraint — always narrowing.
    // Child is allowed to add kinds not present in parent; adding a
    // caveat can only narrow the authorised surface.
    Ok(true)
}

// ---------------------------------------------------------------------------
// Structural narrowing rules per caveat kind
// ---------------------------------------------------------------------------

fn structural_narrows(
    kind: CaveatKind,
    child: &LexProposition,
    parent: &LexProposition,
) -> Result<bool, NarrowingError> {
    match kind {
        CaveatKind::Monetary => Ok(structural_monetary(child, parent).unwrap_or(false)),
        CaveatKind::Temporal => Ok(structural_temporal(child, parent).unwrap_or(false)),
        CaveatKind::Rate => Ok(structural_rate(child, parent).unwrap_or(false)),
        CaveatKind::Operation
        | CaveatKind::Domain
        | CaveatKind::Mcp
        | CaveatKind::Resource
        | CaveatKind::Counterparty
        | CaveatKind::Subject
        | CaveatKind::Jurisdiction => Ok(structural_set(child, parent).unwrap_or(false)),
        CaveatKind::Discretion => Ok(structural_exact(child, parent)),
        CaveatKind::Custom => Ok(false),
    }
}

/// Monetary: child amount-cap is narrower iff its ceiling ≤ parent's.
/// Canonical shape: `Le { attr: "amount", value: Number(N) }`.
fn structural_monetary(child: &LexProposition, parent: &LexProposition) -> Option<bool> {
    let (cattr, cval) = le_number(child)?;
    let (pattr, pval) = le_number(parent)?;
    if cattr != pattr {
        return Some(false);
    }
    Some(cval <= pval)
}

/// Temporal: child window `[a', b']` narrower iff `a ≤ a' ∧ b' ≤ b`.
/// Canonical shape: `And(Ge { now, not_before }, Le { now, not_after })`.
fn structural_temporal(child: &LexProposition, parent: &LexProposition) -> Option<bool> {
    let (c_attr, c_nb, c_na) = temporal_window(child)?;
    let (p_attr, p_nb, p_na) = temporal_window(parent)?;
    if c_attr != p_attr {
        return Some(false);
    }
    // Child is narrower if its window is contained in parent's window.
    Some(p_nb <= c_nb && c_na <= p_na)
}

/// Rate: child rate-limit (max_calls, window) narrower iff
/// `max' ≤ max ∧ window' ≤ window`. We encode rate caveats as
/// `And(Le { max_calls, N }, Le { window_secs, W })`.
fn structural_rate(child: &LexProposition, parent: &LexProposition) -> Option<bool> {
    let (cm, cw) = rate_bounds(child)?;
    let (pm, pw) = rate_bounds(parent)?;
    Some(cm <= pm && cw <= pw)
}

/// Membership / set caveat: child `attr ∈ S'` narrower iff `S' ⊆ S`.
/// Canonical shape: `In { attr, values }`.
fn structural_set(child: &LexProposition, parent: &LexProposition) -> Option<bool> {
    let (cattr, cset) = in_set(child)?;
    let (pattr, pset) = in_set(parent)?;
    if cattr != pattr {
        return Some(false);
    }
    Some(cset.is_subset(pset))
}

/// Discretion: exact equality.
fn structural_exact(child: &LexProposition, parent: &LexProposition) -> bool {
    child == parent
}

// ---------------------------------------------------------------------------
// Recognisers
// ---------------------------------------------------------------------------

fn le_number(prop: &LexProposition) -> Option<(&str, &Decimal)> {
    if let LexProposition::Le {
        attr,
        value: LexValue::Number(n),
    } = prop
    {
        return Some((attr.as_str(), n));
    }
    None
}

fn temporal_window(
    prop: &LexProposition,
) -> Option<(
    &str,
    &chrono::DateTime<chrono::Utc>,
    &chrono::DateTime<chrono::Utc>,
)> {
    // Expect `And(Ge { attr, not_before }, Le { attr, not_after })`.
    let LexProposition::And(a, b) = prop else {
        return None;
    };
    let (a_attr, a_ts) = ge_timestamp(a).or_else(|| le_timestamp_swap(a))?;
    let (b_attr, b_ts) = le_timestamp(b).or_else(|| ge_timestamp_swap(b))?;
    if a_attr != b_attr {
        return None;
    }
    Some((a_attr, a_ts, b_ts))
}

fn ge_timestamp(prop: &LexProposition) -> Option<(&str, &chrono::DateTime<chrono::Utc>)> {
    if let LexProposition::Ge {
        attr,
        value: LexValue::Timestamp(t),
    } = prop
    {
        return Some((attr.as_str(), t));
    }
    None
}

fn le_timestamp(prop: &LexProposition) -> Option<(&str, &chrono::DateTime<chrono::Utc>)> {
    if let LexProposition::Le {
        attr,
        value: LexValue::Timestamp(t),
    } = prop
    {
        return Some((attr.as_str(), t));
    }
    None
}

/// If the temporal window was built with the `Le` conjunct first, try
/// matching it as the lower bound of an inverted window. Used for
/// tolerance during structural recognition.
fn le_timestamp_swap(prop: &LexProposition) -> Option<(&str, &chrono::DateTime<chrono::Utc>)> {
    le_timestamp(prop)
}
fn ge_timestamp_swap(prop: &LexProposition) -> Option<(&str, &chrono::DateTime<chrono::Utc>)> {
    ge_timestamp(prop)
}

fn rate_bounds(prop: &LexProposition) -> Option<(&Decimal, &Decimal)> {
    let LexProposition::And(a, b) = prop else {
        return None;
    };
    let (_, am) = match a.as_ref() {
        LexProposition::Le {
            attr,
            value: LexValue::Number(n),
        } if attr == "max_calls" => (attr.as_str(), n),
        _ => return None,
    };
    let (_, bw) = match b.as_ref() {
        LexProposition::Le {
            attr,
            value: LexValue::Number(n),
        } if attr == "window_secs" => (attr.as_str(), n),
        _ => return None,
    };
    Some((am, bw))
}

fn in_set(prop: &LexProposition) -> Option<(&str, &BTreeSet<LexValue>)> {
    if let LexProposition::In { attr, values } = prop {
        return Some((attr.as_str(), values));
    }
    None
}

// ---------------------------------------------------------------------------
// Propositional fallback: finite-ctx SAT
// ---------------------------------------------------------------------------

/// Return `Ok(true)` iff every context that satisfies the `child` caveats
/// also satisfies `parent_pred`.
///
/// Strategy: the evaluator's predicates mention only attribute bindings
/// compared against literal values. For each attribute mentioned in child
/// ∪ parent, enumerate the literal values that actually appear. For
/// ordering comparisons add one *witness* value per operator to exercise
/// the boundary. Then try every combination; if any assignment satisfies
/// `child` but not `parent_pred`, the narrowing is refuted.
///
/// For the caveat fragment this is sound and complete (all literals are
/// constants and the fragment has no quantifiers or arithmetic over
/// attributes other than literal-comparison). It scales with the product
/// of candidate-value counts, which is small in practice (a handful of
/// caveats, each contributing a few literals).
fn propositional_narrows(
    child_caveats: &[LexCaveat],
    parent_pred: &LexProposition,
) -> Result<bool, NarrowingError> {
    // Collect the set of referenced attributes and candidate values.
    let mut candidates: BTreeMap<String, BTreeSet<LexValue>> = BTreeMap::new();
    for cav in child_caveats {
        collect_literals(&cav.predicate, &mut candidates);
    }
    collect_literals(parent_pred, &mut candidates);

    // If there are attributes with no literal candidates (e.g., pure
    // Bool() or literal-free predicates), propositional narrowing reduces
    // to evaluating in the empty context.
    let attrs: Vec<String> = candidates.keys().cloned().collect();

    // Each attribute gets a vector of candidate values. For numeric or
    // timestamp attributes, append +/- epsilon boundary witnesses so
    // ordering corners are exercised.
    let mut per_attr_candidates: Vec<(String, Vec<LexValue>)> = Vec::new();
    for a in &attrs {
        let mut v: Vec<LexValue> = candidates
            .get(a)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .collect();
        // Extend numeric candidates by ±1 to cover strict ordering corners.
        let mut extras = Vec::new();
        for val in &v {
            if let LexValue::Number(n) = val {
                extras.push(LexValue::Number(*n - Decimal::from(1i64)));
                extras.push(LexValue::Number(*n + Decimal::from(1i64)));
            }
            if let LexValue::Timestamp(t) = val {
                extras.push(LexValue::Timestamp(*t + chrono::Duration::seconds(1)));
                extras.push(LexValue::Timestamp(*t - chrono::Duration::seconds(1)));
            }
        }
        v.extend(extras);
        if v.is_empty() {
            // Skip attributes with no candidates — an attribute the child
            // predicate never references cannot affect narrowing.
            continue;
        }
        per_attr_candidates.push((a.clone(), v));
    }

    // Cartesian product. Guard against explosion.
    let count = per_attr_candidates
        .iter()
        .map(|(_, v)| v.len())
        .product::<usize>();
    if count > 100_000 {
        return Err(NarrowingError::Undecidable(format!(
            "propositional search space too large ({count} candidates)"
        )));
    }

    let combos = cartesian(&per_attr_candidates);
    for combo in combos {
        let ctx = combo.clone();
        // Evaluate child conjunction: every caveat must hold.
        let mut child_holds = true;
        for cav in child_caveats {
            match evaluate(&cav.predicate, &ctx) {
                Ok(true) => {}
                Ok(false) => {
                    child_holds = false;
                    break;
                }
                Err(_) => {
                    // If evaluation of the child fails on this candidate
                    // assignment, skip it — the context doesn't model a
                    // real request under this caveat.
                    child_holds = false;
                    break;
                }
            }
        }
        if !child_holds {
            continue;
        }
        // Child holds on this context. Parent must also hold.
        match evaluate(parent_pred, &ctx) {
            Ok(true) => continue,
            Ok(false) => return Err(NarrowingError::Refuted),
            Err(_) => {
                return Err(NarrowingError::Undecidable(
                    "parent predicate not decidable on candidate context".to_string(),
                ));
            }
        }
    }
    Ok(true)
}

/// Build every context assignment from `per_attr`.
fn cartesian(per_attr: &[(String, Vec<LexValue>)]) -> Vec<EvalContext> {
    let mut out = vec![EvalContext::new()];
    for (attr, vals) in per_attr {
        let mut next: Vec<EvalContext> = Vec::with_capacity(out.len() * vals.len());
        for ctx in &out {
            for v in vals {
                let mut c = ctx.clone();
                c.insert(attr.clone(), v.clone());
                next.push(c);
            }
        }
        out = next;
    }
    out
}

/// Collect every `(attr, literal)` pair appearing in `prop` into
/// `candidates`.
fn collect_literals(prop: &LexProposition, candidates: &mut BTreeMap<String, BTreeSet<LexValue>>) {
    match prop {
        LexProposition::Bool(_) => {}
        LexProposition::And(a, b) | LexProposition::Or(a, b) => {
            collect_literals(a, candidates);
            collect_literals(b, candidates);
        }
        LexProposition::Not(p) => collect_literals(p, candidates),
        LexProposition::Eq { attr, value }
        | LexProposition::NotEq { attr, value }
        | LexProposition::Lt { attr, value }
        | LexProposition::Le { attr, value }
        | LexProposition::Gt { attr, value }
        | LexProposition::Ge { attr, value } => {
            candidates
                .entry(attr.clone())
                .or_default()
                .insert(value.clone());
        }
        LexProposition::In { attr, values } => {
            let set = candidates.entry(attr.clone()).or_default();
            for v in values {
                set.insert(v.clone());
            }
        }
        LexProposition::InCtx { .. } => {
            // InCtx references a set living in the context; we cannot
            // enumerate without inlining. The caller should avoid this
            // shape in caveat narrowing — InCtx is meant for runtime,
            // not narrowing proofs.
        }
    }
}

// ---------------------------------------------------------------------------
// grouping helper
// ---------------------------------------------------------------------------

fn group_by_kind(caveats: &[LexCaveat]) -> BTreeMap<CaveatKind, Vec<&LexCaveat>> {
    let mut out: BTreeMap<CaveatKind, Vec<&LexCaveat>> = BTreeMap::new();
    for c in caveats {
        out.entry(c.kind).or_default().push(c);
    }
    out
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use chrono::{DateTime, Utc};
    use std::str::FromStr;

    fn num(s: &str) -> LexValue {
        LexValue::Number(Decimal::from_str(s).unwrap())
    }

    fn ts(s: &str) -> LexValue {
        LexValue::Timestamp(DateTime::parse_from_rfc3339(s).unwrap().with_timezone(&Utc))
    }

    fn monetary_le(attr: &str, n: &str) -> LexCaveat {
        LexCaveat::new(
            CaveatKind::Monetary,
            LexProposition::Le {
                attr: attr.into(),
                value: num(n),
            },
        )
    }

    fn op_in(ops: &[&str]) -> LexCaveat {
        let values: BTreeSet<LexValue> =
            ops.iter().map(|s| LexValue::String((*s).into())).collect();
        LexCaveat::new(
            CaveatKind::Operation,
            LexProposition::In {
                attr: "op_type".into(),
                values,
            },
        )
    }

    fn temporal(not_before: &str, not_after: &str) -> LexCaveat {
        LexCaveat::new(
            CaveatKind::Temporal,
            LexProposition::And(
                Box::new(LexProposition::Ge {
                    attr: "now".into(),
                    value: ts(not_before),
                }),
                Box::new(LexProposition::Le {
                    attr: "now".into(),
                    value: ts(not_after),
                }),
            ),
        )
    }

    #[test]
    fn monetary_narrower_passes() {
        let parent = vec![monetary_le("amount", "10000")];
        let child = vec![monetary_le("amount", "5000")];
        assert_eq!(caveats_narrow(&parent, &child), Ok(true));
    }

    #[test]
    fn monetary_broader_fails() {
        let parent = vec![monetary_le("amount", "5000")];
        let child = vec![monetary_le("amount", "10000")];
        assert!(matches!(
            caveats_narrow(&parent, &child),
            Err(NarrowingError::NotNarrower { .. }) | Err(NarrowingError::Refuted)
        ));
    }

    #[test]
    fn monetary_equal_passes() {
        let parent = vec![monetary_le("amount", "5000")];
        let child = vec![monetary_le("amount", "5000")];
        assert_eq!(caveats_narrow(&parent, &child), Ok(true));
    }

    #[test]
    fn operation_subset_passes() {
        let parent = op_in(&["payment.create", "payment.cancel", "payment.refund"]);
        let child = op_in(&["payment.create", "payment.cancel"]);
        assert_eq!(caveats_narrow(&[parent], &[child]), Ok(true));
    }

    #[test]
    fn operation_superset_fails() {
        let parent = op_in(&["payment.create"]);
        let child = op_in(&["payment.create", "payment.refund"]);
        assert!(matches!(
            caveats_narrow(&[parent], &[child]),
            Err(NarrowingError::NotNarrower { .. }) | Err(NarrowingError::Refuted)
        ));
    }

    #[test]
    fn temporal_narrower_window_passes() {
        let parent = temporal("2026-01-01T00:00:00Z", "2026-12-31T23:59:59Z");
        let child = temporal("2026-03-01T00:00:00Z", "2026-06-30T00:00:00Z");
        assert_eq!(caveats_narrow(&[parent], &[child]), Ok(true));
    }

    #[test]
    fn temporal_broader_window_fails() {
        let parent = temporal("2026-03-01T00:00:00Z", "2026-06-30T00:00:00Z");
        let child = temporal("2026-01-01T00:00:00Z", "2026-12-31T23:59:59Z");
        assert!(matches!(
            caveats_narrow(&[parent], &[child]),
            Err(NarrowingError::NotNarrower { .. }) | Err(NarrowingError::Refuted)
        ));
    }

    #[test]
    fn a_and_b_is_narrower_than_a() {
        // Child = A ∧ B, Parent = A. The addition of B further constrains,
        // so child narrows parent.
        let caveat_a = monetary_le("amount", "1000");
        let caveat_b = op_in(&["payment.create"]);
        let parent = vec![caveat_a.clone()];
        let child = vec![caveat_a, caveat_b];
        assert_eq!(caveats_narrow(&parent, &child), Ok(true));
    }

    #[test]
    fn a_is_not_narrower_than_a_and_b() {
        // Parent = A ∧ B, Child = A. Child is broader — missing the B kind.
        let caveat_a = monetary_le("amount", "1000");
        let caveat_b = op_in(&["payment.create"]);
        let parent = vec![caveat_a.clone(), caveat_b];
        let child = vec![caveat_a];
        // Missing Operation kind in child — fail.
        assert!(matches!(
            caveats_narrow(&parent, &child),
            Err(NarrowingError::MissingKind(CaveatKind::Operation))
        ));
    }

    #[test]
    fn adding_unrelated_caveat_is_still_narrower() {
        // Parent = Monetary(10000). Child = Monetary(10000) ∧ Operation(...).
        let p = vec![monetary_le("amount", "10000")];
        let c = vec![monetary_le("amount", "10000"), op_in(&["payment.create"])];
        assert_eq!(caveats_narrow(&p, &c), Ok(true));
    }

    #[test]
    fn empty_parent_trivially_satisfied() {
        let c = vec![monetary_le("amount", "10000")];
        assert_eq!(caveats_narrow(&[], &c), Ok(true));
    }

    #[test]
    fn propositional_fallback_custom_kind() {
        // Custom caveats fall into the propositional finite-ctx SAT path.
        // Parent: x ≤ 100. Child: x ≤ 50.
        let parent = LexCaveat::new(
            CaveatKind::Custom,
            LexProposition::Le {
                attr: "x".into(),
                value: num("100"),
            },
        );
        let child = LexCaveat::new(
            CaveatKind::Custom,
            LexProposition::Le {
                attr: "x".into(),
                value: num("50"),
            },
        );
        assert_eq!(caveats_narrow(&[parent], &[child]), Ok(true));
    }

    #[test]
    fn propositional_fallback_custom_refuted() {
        // Parent: x ≤ 50. Child: x ≤ 100 (broader). Should be refuted.
        let parent = LexCaveat::new(
            CaveatKind::Custom,
            LexProposition::Le {
                attr: "x".into(),
                value: num("50"),
            },
        );
        let child = LexCaveat::new(
            CaveatKind::Custom,
            LexProposition::Le {
                attr: "x".into(),
                value: num("100"),
            },
        );
        assert!(matches!(
            caveats_narrow(&[parent], &[child]),
            Err(NarrowingError::Refuted)
        ));
    }

    #[test]
    fn self_narrowing_trivially_true() {
        let caveats = vec![
            monetary_le("amount", "1000"),
            op_in(&["payment.create"]),
            temporal("2026-01-01T00:00:00Z", "2026-12-31T23:59:59Z"),
        ];
        assert_eq!(caveats_narrow(&caveats, &caveats), Ok(true));
    }

    // -----------------------------------------------------------------
    // Subject narrowing — set-inclusion semantics on `subject_entity_id`.
    // Subject is the principal-side allowlist (which entities the bearer
    // may act on behalf of); narrower set = narrower authority.
    // -----------------------------------------------------------------

    fn subject_in(ids: &[&str]) -> LexCaveat {
        let values: BTreeSet<LexValue> =
            ids.iter().map(|s| LexValue::String((*s).into())).collect();
        LexCaveat::new(
            CaveatKind::Subject,
            LexProposition::In {
                attr: "subject_entity_id".into(),
                values,
            },
        )
    }

    /// Parent `{a, b}` → child `{a}`: the child's allowed-subject set
    /// is a strict subset, so narrowing succeeds.
    #[test]
    fn subject_subset_narrows() {
        let parent = subject_in(&["a", "b"]);
        let child = subject_in(&["a"]);
        assert_eq!(caveats_narrow(&[parent], &[child]), Ok(true));
    }

    /// Parent `{a, b}` → child `{a, b}`: equal sets are admitted
    /// (non-strict containment).
    #[test]
    fn subject_equal_narrows() {
        let parent = subject_in(&["a", "b"]);
        let child = subject_in(&["a", "b"]);
        assert_eq!(caveats_narrow(&[parent], &[child]), Ok(true));
    }

    /// Parent `{a}` → child `{a, b}`: the child WIDENS authority by
    /// adding `b`. Must be rejected — attenuation cannot grant new
    /// principal-side authority.
    #[test]
    fn subject_superset_rejected() {
        let parent = subject_in(&["a"]);
        let child = subject_in(&["a", "b"]);
        assert!(matches!(
            caveats_narrow(&[parent], &[child]),
            Err(NarrowingError::NotNarrower { .. }) | Err(NarrowingError::Refuted)
        ));
    }

    /// Parent `{a}` → child `{b}`: disjoint sets — child names
    /// authority parent never granted. Reject.
    #[test]
    fn subject_disjoint_rejected() {
        let parent = subject_in(&["a"]);
        let child = subject_in(&["b"]);
        assert!(matches!(
            caveats_narrow(&[parent], &[child]),
            Err(NarrowingError::NotNarrower { .. }) | Err(NarrowingError::Refuted)
        ));
    }

    /// Parent has Subject; child drops Subject entirely. Per the
    /// general "missing kind in child = child is broader" rule, this
    /// must be rejected — dropping the Subject narrower would let the
    /// holder act on behalf of any entity.
    #[test]
    fn subject_missing_in_child_rejected() {
        let parent = subject_in(&["a"]);
        let child: Vec<LexCaveat> = vec![];
        assert!(matches!(
            caveats_narrow(&[parent], &child),
            Err(NarrowingError::MissingKind(CaveatKind::Subject))
        ));
    }

    /// Empty Subject in child (`{}`) is strictly narrower than any
    /// non-empty parent: deny-all is the tightest possible Subject.
    #[test]
    fn subject_empty_child_narrows_nonempty_parent() {
        let parent = subject_in(&["a", "b"]);
        let child = subject_in(&[]);
        assert_eq!(caveats_narrow(&[parent], &[child]), Ok(true));
    }
}
