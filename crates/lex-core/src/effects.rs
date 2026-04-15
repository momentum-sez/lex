//! Effect row algebra for Core Lex.
//!
//! Implements the path-indexed effect system specified in
//! `docs/architecture/LEX-CORE-GRAMMAR.md` §3.1. Effect rows are first-class
//! types at sort `Type₀` and form a bounded semilattice under `⊕` (join) with
//! `∅` (the empty/pure row) as unit.
//!
//! # Lattice Structure
//!
//! The effect lattice is ordered by *subsumption*: `a ⊑ b` iff every effect
//! in `a` appears in `b`. This models *effect weakening* — a pure function
//! can be used where an effectful one is expected, but not the reverse.
//!
//! - **Join** (`⊕`): union of effects (semilattice join).
//! - **Meet** (`⊓`): intersection of effects.
//! - **Bottom** (`∅`): the empty row (pure).
//! - **Top**: the row containing all possible effects (not explicitly
//!   represented — we work with finite sets).
//!
//! # Distinguished Effects
//!
//! - `sanctions_query`: per the grammar, this is a *distinguished* effect
//!   that triggers additional compliance obligations. Its presence must be
//!   detectable at type-checking time.
//! - `⟨branch_sensitive⟩`: a privilege-creep marker wrapping a row whose
//!   join would raise the privilege level. Requires an explicit `unlock`
//!   eliminator at the branch head.

use std::collections::BTreeSet;
use std::fmt;

// ---------------------------------------------------------------------------
// Effect — individual effect labels
// ---------------------------------------------------------------------------

/// A single effect label as specified in the grammar's `<effect>` production.
///
/// Effects are *structurally* compared: two `Write` effects with different
/// scopes are distinct, two `Attest` effects with different authorities are
/// distinct, etc.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Effect {
    /// `read` — pure observation of state.
    Read,
    /// `write(scope)` — mutation of `scope`. The scope string is the
    /// serialized term (not yet a full AST node since `ast` is pending).
    Write(String),
    /// `attest(authority)` — assertion under an authority.
    Attest(String),
    /// `authority(ref)` — exercise of an authority role.
    Authority(String),
    /// `oracle(ref)` — query to an external oracle.
    Oracle(String),
    /// `fuel(level, amount)` — gas/fuel consumption.
    Fuel(u32, u64),
    /// `sanctions_query` — distinguished effect per the grammar; triggers
    /// additional compliance obligations.
    SanctionsQuery,
    /// `discretion(authority)` — exercise of discretionary judgment.
    Discretion(String),
}

impl fmt::Display for Effect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Effect::Read => write!(f, "read"),
            Effect::Write(scope) => write!(f, "write({})", scope),
            Effect::Attest(auth) => write!(f, "attest({})", auth),
            Effect::Authority(auth) => write!(f, "authority({})", auth),
            Effect::Oracle(oref) => write!(f, "oracle({})", oref),
            Effect::Fuel(level, amount) => write!(f, "fuel({}, {})", level, amount),
            Effect::SanctionsQuery => write!(f, "sanctions_query"),
            Effect::Discretion(auth) => write!(f, "discretion({})", auth),
        }
    }
}

// ---------------------------------------------------------------------------
// EffectRow — a set of effects with optional branch_sensitive marker
// ---------------------------------------------------------------------------

/// An effect row as specified in the grammar's `<effect-row>` production.
///
/// Internally represented as a sorted set of [`Effect`] labels. The sorted
/// representation provides canonical (normalized) equality: two rows with the
/// same effects in different insertion order are identical.
///
/// The `branch_sensitive` flag corresponds to the `⟨branch_sensitive⟩`
/// wrapper in the grammar. When set, the row requires an explicit `unlock`
/// eliminator at the branch head before the enclosed effects may be used.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectRow {
    /// The set of individual effect labels, kept in sorted (canonical) order
    /// via `BTreeSet`.
    effects: BTreeSet<Effect>,
    /// Whether this row is wrapped in `⟨branch_sensitive⟩`.
    branch_sensitive: bool,
}

impl EffectRow {
    /// The empty effect row (`∅`). This is the unit of `⊕` and represents
    /// a pure computation.
    pub fn empty() -> Self {
        Self {
            effects: BTreeSet::new(),
            branch_sensitive: false,
        }
    }

    /// Create an effect row from an iterator of effects.
    pub fn from_effects(effects: impl IntoIterator<Item = Effect>) -> Self {
        Self {
            effects: effects.into_iter().collect(),
            branch_sensitive: false,
        }
    }

    /// Create an effect row with the `⟨branch_sensitive⟩` marker set.
    pub fn branch_sensitive(effects: impl IntoIterator<Item = Effect>) -> Self {
        Self {
            effects: effects.into_iter().collect(),
            branch_sensitive: true,
        }
    }

    /// Returns the number of individual effects in this row.
    pub fn len(&self) -> usize {
        self.effects.len()
    }

    /// Returns `true` if the row contains no effects (may still be
    /// `branch_sensitive`, which is a separate concern).
    pub fn is_empty(&self) -> bool {
        self.effects.is_empty()
    }

    /// Returns `true` if this row is marked `⟨branch_sensitive⟩`.
    pub fn is_branch_sensitive(&self) -> bool {
        self.branch_sensitive
    }

    /// Iterate over the effects in canonical (sorted) order.
    pub fn iter(&self) -> impl Iterator<Item = &Effect> {
        self.effects.iter()
    }

    /// Returns `true` if this row contains the given effect.
    pub fn contains(&self, effect: &Effect) -> bool {
        self.effects.contains(effect)
    }

    /// Insert an effect into this row.
    pub fn insert(&mut self, effect: Effect) {
        self.effects.insert(effect);
    }

    /// Mark this row as `⟨branch_sensitive⟩`.
    pub fn set_branch_sensitive(&mut self, sensitive: bool) {
        self.branch_sensitive = sensitive;
    }
}

impl fmt::Display for EffectRow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.branch_sensitive {
            write!(f, "⟨branch_sensitive⟩ ")?;
        }
        if self.effects.is_empty() {
            write!(f, "∅")
        } else {
            let parts: Vec<String> = self.effects.iter().map(|e| e.to_string()).collect();
            write!(f, "{}", parts.join(", "))
        }
    }
}

// ---------------------------------------------------------------------------
// EffectError — subsumption and well-formedness errors
// ---------------------------------------------------------------------------

/// Errors arising from effect row operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EffectError {
    /// Subsumption check failed: `sub` is not a subset of `sup`.
    /// Contains the effects present in `sub` but absent from `sup`.
    SubsumptionFailure {
        /// Effects in the subtype row that are not in the supertype row.
        missing: Vec<Effect>,
        /// The subtype row that was being checked.
        sub: EffectRow,
        /// The supertype row that was expected.
        sup: EffectRow,
    },
    /// A `⟨branch_sensitive⟩` row was used without an explicit `unlock`.
    BranchSensitiveWithoutUnlock {
        /// The branch-sensitive row that requires unlocking.
        row: EffectRow,
    },
}

impl fmt::Display for EffectError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EffectError::SubsumptionFailure { missing, sub, sup } => {
                write!(
                    f,
                    "effect subsumption failure: [{}] not subsumed by [{}]; missing effects: [{}]",
                    sub,
                    sup,
                    missing
                        .iter()
                        .map(|e| e.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            EffectError::BranchSensitiveWithoutUnlock { row } => {
                write!(
                    f,
                    "branch-sensitive effect row [{}] requires explicit unlock",
                    row
                )
            }
        }
    }
}

impl std::error::Error for EffectError {}

// ---------------------------------------------------------------------------
// Effect row algebra operations
// ---------------------------------------------------------------------------

/// Check if `sub`'s effects are a subset of `sup`'s effects (effect weakening).
///
/// Returns `true` iff every effect in `sub` is also present in `sup`.
/// The empty row (`∅`) is subsumed by every row, and every row is subsumed
/// by itself. The `branch_sensitive` flag is propagated: a branch-sensitive
/// sub-row is only subsumed by a branch-sensitive super-row (or if the
/// sub-row has no effects).
///
/// This implements the standard substructural weakening rule:
/// ```text
///   Γ ⊢ e : τ [ε₁]    ε₁ ⊆ ε₂
///   ─────────────────────────────
///         Γ ⊢ e : τ [ε₂]
/// ```
pub fn effect_subsumes(sub: &EffectRow, sup: &EffectRow) -> bool {
    // A branch-sensitive sub-row can only be subsumed if the super-row is
    // also branch-sensitive (or the sub-row is effectively empty).
    if sub.branch_sensitive && !sup.branch_sensitive && !sub.effects.is_empty() {
        return false;
    }
    sub.effects.is_subset(&sup.effects)
}

/// Compute the path-indexed join of two effect rows (semilattice join).
///
/// The join (`⊕`) is the union of both effect sets. The empty row is
/// the unit: `a ⊕ ∅ = ∅ ⊕ a = a`.
///
/// If either row is `⟨branch_sensitive⟩`, the result is also marked
/// `⟨branch_sensitive⟩` — privilege markers propagate upward through joins.
///
/// ```text
///   ε₁ ⊕ ε₂ = { e | e ∈ ε₁ ∨ e ∈ ε₂ }
/// ```
pub fn effect_join(a: &EffectRow, b: &EffectRow) -> EffectRow {
    let effects: BTreeSet<Effect> = a.effects.union(&b.effects).cloned().collect();
    EffectRow {
        effects,
        branch_sensitive: a.branch_sensitive || b.branch_sensitive,
    }
}

/// Compute the meet (intersection) of two effect rows.
///
/// The meet (`⊓`) retains only effects present in both rows.
///
/// The `branch_sensitive` flag is set only if both rows are
/// `branch_sensitive` — it is the *meet* of the sensitivity markers.
///
/// ```text
///   ε₁ ⊓ ε₂ = { e | e ∈ ε₁ ∧ e ∈ ε₂ }
/// ```
pub fn effect_meet(a: &EffectRow, b: &EffectRow) -> EffectRow {
    let effects: BTreeSet<Effect> = a.effects.intersection(&b.effects).cloned().collect();
    EffectRow {
        effects,
        branch_sensitive: a.branch_sensitive && b.branch_sensitive,
    }
}

/// Check if the effect row is `∅` (no effects, not branch-sensitive).
///
/// A pure row has zero effects and no privilege markers. This is the
/// bottom of the effect lattice and the unit of join.
pub fn is_pure(row: &EffectRow) -> bool {
    row.effects.is_empty() && !row.branch_sensitive
}

/// Check if the effect row contains `⟨branch_sensitive⟩` markers that
/// require an explicit `unlock` eliminator at the branch head.
///
/// Per the grammar: "Joins that would raise the privilege level are wrapped
/// in `⟨branch_sensitive⟩` and require an explicit `unlock` eliminator at
/// the branch head."
pub fn check_branch_sensitivity(row: &EffectRow) -> bool {
    row.branch_sensitive
}

/// Check if the `sanctions_query` effect is present.
///
/// Per the grammar, `sanctions_query` is a *distinguished* effect that
/// triggers additional compliance obligations in the type checker and
/// the runtime. This function enables fast detection without iterating
/// the full row.
pub fn sanctions_effect_present(row: &EffectRow) -> bool {
    row.effects.contains(&Effect::SanctionsQuery)
}

/// Attempt effect subsumption, returning an [`EffectError`] on failure.
///
/// This is the checked version of [`effect_subsumes`] that produces
/// a diagnostic error with the specific missing effects.
pub fn require_subsumption(sub: &EffectRow, sup: &EffectRow) -> Result<(), EffectError> {
    if effect_subsumes(sub, sup) {
        Ok(())
    } else {
        let missing: Vec<Effect> = sub.effects.difference(&sup.effects).cloned().collect();
        Err(EffectError::SubsumptionFailure {
            missing,
            sub: sub.clone(),
            sup: sup.clone(),
        })
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // ── Helper constructors ─────────────────────────────────────────

    fn empty() -> EffectRow {
        EffectRow::empty()
    }

    fn read_row() -> EffectRow {
        EffectRow::from_effects(vec![Effect::Read])
    }

    fn write_row(scope: &str) -> EffectRow {
        EffectRow::from_effects(vec![Effect::Write(scope.to_string())])
    }

    fn read_write_row(scope: &str) -> EffectRow {
        EffectRow::from_effects(vec![Effect::Read, Effect::Write(scope.to_string())])
    }

    fn sanctions_row() -> EffectRow {
        EffectRow::from_effects(vec![Effect::SanctionsQuery])
    }

    fn complex_row() -> EffectRow {
        EffectRow::from_effects(vec![
            Effect::Read,
            Effect::Write("entities".to_string()),
            Effect::Attest("zone_authority".to_string()),
            Effect::SanctionsQuery,
        ])
    }

    // ── 1. Empty is pure ────────────────────────────────────────────

    #[test]
    fn empty_is_pure() {
        assert!(is_pure(&empty()));
        assert!(empty().is_empty());
        assert_eq!(empty().len(), 0);
    }

    // ── 2. Non-empty is not pure ────────────────────────────────────

    #[test]
    fn non_empty_is_not_pure() {
        assert!(!is_pure(&read_row()));
        assert!(!is_pure(&sanctions_row()));
        assert!(!is_pure(&complex_row()));
    }

    // ── 3. Read subsumes empty ──────────────────────────────────────

    #[test]
    fn read_subsumes_empty() {
        // ∅ ⊑ {read}  — pure can be used where read is expected
        assert!(effect_subsumes(&empty(), &read_row()));
    }

    // ── 4. Write subsumes read ──────────────────────────────────────

    #[test]
    fn write_subsumes_read() {
        // {read} ⊑ {read, write(x)} — a reader can be used where a
        // reader+writer is expected
        let rw = read_write_row("x");
        assert!(effect_subsumes(&read_row(), &rw));
        // But not the reverse
        assert!(!effect_subsumes(&rw, &read_row()));
    }

    // ── 5. Join commutativity ───────────────────────────────────────

    #[test]
    fn join_commutativity() {
        let a = read_row();
        let b = sanctions_row();
        assert_eq!(effect_join(&a, &b), effect_join(&b, &a));
    }

    // ── 6. Join with empty is identity ──────────────────────────────

    #[test]
    fn join_with_empty_is_identity() {
        let r = read_row();
        assert_eq!(effect_join(&r, &empty()), r);
        assert_eq!(effect_join(&empty(), &r), r);

        let c = complex_row();
        assert_eq!(effect_join(&c, &empty()), c);
        assert_eq!(effect_join(&empty(), &c), c);
    }

    // ── 7. Join associativity ───────────────────────────────────────

    #[test]
    fn join_associativity() {
        let a = read_row();
        let b = sanctions_row();
        let c = write_row("t");

        let ab_c = effect_join(&effect_join(&a, &b), &c);
        let a_bc = effect_join(&a, &effect_join(&b, &c));
        assert_eq!(ab_c, a_bc);
    }

    // ── 8. Meet commutativity ───────────────────────────────────────

    #[test]
    fn meet_commutativity() {
        let a = EffectRow::from_effects(vec![Effect::Read, Effect::SanctionsQuery]);
        let b = EffectRow::from_effects(vec![Effect::Read, Effect::Write("x".to_string())]);
        assert_eq!(effect_meet(&a, &b), effect_meet(&b, &a));
    }

    // ── 9. Meet semantics ───────────────────────────────────────────

    #[test]
    fn meet_is_intersection() {
        let a = EffectRow::from_effects(vec![
            Effect::Read,
            Effect::SanctionsQuery,
            Effect::Attest("z".to_string()),
        ]);
        let b = EffectRow::from_effects(vec![
            Effect::Read,
            Effect::Write("x".to_string()),
            Effect::Attest("z".to_string()),
        ]);
        let m = effect_meet(&a, &b);
        assert_eq!(m.len(), 2);
        assert!(m.contains(&Effect::Read));
        assert!(m.contains(&Effect::Attest("z".to_string())));
        assert!(!m.contains(&Effect::SanctionsQuery));
        assert!(!m.contains(&Effect::Write("x".to_string())));
    }

    // ── 10. Sanctions detection ─────────────────────────────────────

    #[test]
    fn sanctions_detection() {
        assert!(sanctions_effect_present(&sanctions_row()));
        assert!(sanctions_effect_present(&complex_row()));
        assert!(!sanctions_effect_present(&read_row()));
        assert!(!sanctions_effect_present(&empty()));
    }

    // ── 11. Branch sensitivity detection ────────────────────────────

    #[test]
    fn branch_sensitivity_detection() {
        let sensitive = EffectRow::branch_sensitive(vec![Effect::Read]);
        assert!(check_branch_sensitivity(&sensitive));
        assert!(!check_branch_sensitivity(&read_row()));
        assert!(!check_branch_sensitivity(&empty()));
    }

    // ── 12. Branch-sensitive is not pure ────────────────────────────

    #[test]
    fn branch_sensitive_empty_is_not_pure() {
        // An empty row with branch_sensitive flag is NOT pure —
        // it still requires an unlock.
        let bs_empty = EffectRow::branch_sensitive(vec![]);
        assert!(!is_pure(&bs_empty));
        assert!(bs_empty.is_empty()); // effects are empty, but row is not "pure"
    }

    // ── 13. Complex row subsumption ─────────────────────────────────

    #[test]
    fn complex_row_subsumption() {
        let sub =
            EffectRow::from_effects(vec![Effect::Read, Effect::Write("entities".to_string())]);
        let sup = complex_row(); // read, write(entities), attest(zone_authority), sanctions_query
        assert!(effect_subsumes(&sub, &sup));

        // Reverse should fail
        assert!(!effect_subsumes(&sup, &sub));
    }

    // ── 14. Effect equality after normalization ─────────────────────

    #[test]
    fn effect_equality_after_normalization() {
        // Insertion order should not matter — BTreeSet normalizes.
        let a = EffectRow::from_effects(vec![
            Effect::Write("x".to_string()),
            Effect::Read,
            Effect::SanctionsQuery,
        ]);
        let b = EffectRow::from_effects(vec![
            Effect::SanctionsQuery,
            Effect::Read,
            Effect::Write("x".to_string()),
        ]);
        assert_eq!(a, b);
    }

    // ── 15. require_subsumption error ───────────────────────────────

    #[test]
    fn require_subsumption_error() {
        let sub = read_write_row("x");
        let sup = read_row();
        let err = require_subsumption(&sub, &sup).unwrap_err();
        match err {
            EffectError::SubsumptionFailure { missing, .. } => {
                assert_eq!(missing.len(), 1);
                assert_eq!(missing[0], Effect::Write("x".to_string()));
            }
            _ => panic!("expected SubsumptionFailure"),
        }
    }

    // ── 16. require_subsumption success ─────────────────────────────

    #[test]
    fn require_subsumption_success() {
        assert!(require_subsumption(&empty(), &read_row()).is_ok());
        assert!(require_subsumption(&read_row(), &read_row()).is_ok());
    }

    // ── 17. Join propagates branch_sensitive ────────────────────────

    #[test]
    fn join_propagates_branch_sensitivity() {
        let normal = read_row();
        let sensitive = EffectRow::branch_sensitive(vec![Effect::SanctionsQuery]);

        let joined = effect_join(&normal, &sensitive);
        assert!(check_branch_sensitivity(&joined));
        assert!(joined.contains(&Effect::Read));
        assert!(joined.contains(&Effect::SanctionsQuery));
    }

    // ── 18. Meet requires both branch_sensitive ─────────────────────

    #[test]
    fn meet_branch_sensitivity() {
        let a = EffectRow::branch_sensitive(vec![Effect::Read]);
        let b = EffectRow::from_effects(vec![Effect::Read]);
        let m = effect_meet(&a, &b);
        // Only a is branch_sensitive, so meet should not be
        assert!(!check_branch_sensitivity(&m));
        assert!(m.contains(&Effect::Read));

        let c = EffectRow::branch_sensitive(vec![Effect::Read]);
        let m2 = effect_meet(&a, &c);
        assert!(check_branch_sensitivity(&m2));
    }

    // ── 19. Branch-sensitive subsumption ────────────────────────────

    #[test]
    fn branch_sensitive_subsumption_requires_matching_flag() {
        let sensitive = EffectRow::branch_sensitive(vec![Effect::Read]);
        let normal = EffectRow::from_effects(vec![Effect::Read, Effect::SanctionsQuery]);

        // A branch-sensitive row with effects should NOT be subsumed by
        // a normal row (even if the effects are a subset).
        assert!(!effect_subsumes(&sensitive, &normal));

        // But a branch-sensitive row IS subsumed by another branch-sensitive row.
        let sensitive_sup = EffectRow::branch_sensitive(vec![Effect::Read, Effect::SanctionsQuery]);
        assert!(effect_subsumes(&sensitive, &sensitive_sup));
    }

    // ── 20. Display formatting ──────────────────────────────────────

    #[test]
    fn display_formatting() {
        assert_eq!(empty().to_string(), "∅");
        assert_eq!(read_row().to_string(), "read");
        assert!(complex_row().to_string().contains("sanctions_query"));

        let sensitive = EffectRow::branch_sensitive(vec![Effect::Read]);
        assert!(sensitive.to_string().starts_with("⟨branch_sensitive⟩"));
    }

    // ── 21. Join idempotency ────────────────────────────────────────

    #[test]
    fn join_idempotency() {
        let r = complex_row();
        assert_eq!(effect_join(&r, &r), r);
    }

    // ── 22. Meet with empty is empty ────────────────────────────────

    #[test]
    fn meet_with_empty_is_empty() {
        let r = complex_row();
        let m = effect_meet(&r, &empty());
        assert!(is_pure(&m));
    }

    // ── 23. Self-subsumption ────────────────────────────────────────

    #[test]
    fn self_subsumption() {
        let r = complex_row();
        assert!(effect_subsumes(&r, &r));
        assert!(effect_subsumes(&empty(), &empty()));
    }

    // ── 24. Fuel effect distinctness ────────────────────────────────

    #[test]
    fn fuel_effects_distinct_by_params() {
        let a = EffectRow::from_effects(vec![Effect::Fuel(1, 100)]);
        let b = EffectRow::from_effects(vec![Effect::Fuel(1, 200)]);
        let c = EffectRow::from_effects(vec![Effect::Fuel(2, 100)]);

        // Different fuel params are different effects
        assert_ne!(a, b);
        assert_ne!(a, c);
        assert_ne!(b, c);

        // Join produces a row with all three
        let joined = effect_join(&effect_join(&a, &b), &c);
        assert_eq!(joined.len(), 3);
    }

    // ── 25. Write scope distinctness ────────────────────────────────

    #[test]
    fn write_scopes_are_distinct() {
        let a = write_row("entities");
        let b = write_row("treasury");
        let joined = effect_join(&a, &b);
        assert_eq!(joined.len(), 2);
        assert!(!effect_subsumes(&a, &b));
        assert!(!effect_subsumes(&b, &a));
    }
}
