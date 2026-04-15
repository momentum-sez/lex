//! Temporal stratification enforcement for the Lex core language.
//!
//! Per `docs/architecture/LEX-CORE-GRAMMAR.md` §4 and the PLATONIC-IDEAL §5.1
//! ("Temporal stratification"), Lex separates **Time₀** (frozen at transition
//! commit) from **Time₁** (derived transitions from tolling/savings/statute
//! rewrites). These are syntactically distinct sorts. A term that mixes them
//! without an explicit `lift₀` or `derive₁` coercion is ill-typed.
//!
//! This module implements:
//! - `TemporalSort` — the two temporal strata plus a non-temporal marker
//! - `TemporalError` — diagnostic error with location and description
//! - `infer_temporal_sort` — infers whether a `TimeTerm` is Time₀ or Time₁
//! - `check_temporal_stratification` — verifies no illegal mixing in a `Term`
//!
//! # Key invariant (I-11)
//!
//! There is **no** coercion from Time₁ to Time₀. Retroactive rewrites cannot
//! reach frozen time. This is a hard syntactic property enforced here.

use std::fmt;

use crate::ast::{Term, TimeTerm};

/// Maximum recursion depth for temporal stratification checking.
const MAX_DEPTH: usize = 256;

// ---------------------------------------------------------------------------
// TemporalSort — the two strata
// ---------------------------------------------------------------------------

/// The temporal sort of a Lex term.
///
/// `Time0` is frozen historical time (stratum 0). `Time1` is derived time
/// produced by rewrites (stratum 1). `NonTemporal` marks terms that do not
/// participate in the temporal stratification (e.g. pure type constructors,
/// literals, witnesses).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TemporalSort {
    /// Stratum 0 — frozen at transition commit.
    Time0,
    /// Stratum 1 — derived by tolling/savings/statute rewrites.
    Time1,
    /// The term is not temporal (a witness, literal, type, etc.).
    NonTemporal,
}

impl fmt::Display for TemporalSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TemporalSort::Time0 => write!(f, "Time₀"),
            TemporalSort::Time1 => write!(f, "Time₁"),
            TemporalSort::NonTemporal => write!(f, "non-temporal"),
        }
    }
}

// ---------------------------------------------------------------------------
// TemporalError — stratification violation diagnostic
// ---------------------------------------------------------------------------

/// An error produced by temporal stratification checking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TemporalError {
    /// A human-readable location description (e.g. "in lift₀ argument",
    /// "in let binding body").
    pub location: String,
    /// A description of the stratification violation.
    pub description: String,
}

impl TemporalError {
    /// Construct a new temporal error.
    pub fn new(location: impl Into<String>, description: impl Into<String>) -> Self {
        Self {
            location: location.into(),
            description: description.into(),
        }
    }
}

impl fmt::Display for TemporalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "temporal stratification error at {}: {}",
            self.location, self.description
        )
    }
}

impl std::error::Error for TemporalError {}

// ---------------------------------------------------------------------------
// infer_temporal_sort — sort inference on TimeTerm
// ---------------------------------------------------------------------------

/// Infer the temporal sort of a `TimeTerm`.
///
/// # Rules
///
/// | Constructor              | Sort       | Constraint                          |
/// |--------------------------|------------|-------------------------------------|
/// | `AsOf0(transition)`      | `Time₀`   | transition is a core term           |
/// | `AsOf1(transition)`      | `Time₁`   | transition is a core term           |
/// | `Lift0(time_term)`       | `Time₁`   | inner must be `Time₀`               |
/// | `Derive1 { time, .. }`   | `Time₁`   | `time` must be `Time₀`             |
/// | `Literal(_)`             | `NonTemporal` | time literals need annotation    |
/// | `Var { .. }`             | `NonTemporal` | variables need context           |
pub fn infer_temporal_sort(term: &TimeTerm) -> Result<TemporalSort, TemporalError> {
    match term {
        // asof₀(transition) → Time₀
        TimeTerm::AsOf0(_) => Ok(TemporalSort::Time0),

        // asof₁(transition) → Time₁
        TimeTerm::AsOf1(_) => Ok(TemporalSort::Time1),

        // lift₀(t) → Time₁, but inner must be Time₀
        TimeTerm::Lift0(inner) => {
            let inner_sort = infer_temporal_sort(inner)?;
            match inner_sort {
                TemporalSort::Time0 => Ok(TemporalSort::Time1),
                TemporalSort::Time1 => Err(TemporalError::new(
                    "in lift₀ argument",
                    "lift₀ expects a Time₀ term, but the argument is already Time₁; \
                     there is no coercion from Time₁ to Time₀",
                )),
                TemporalSort::NonTemporal => Err(TemporalError::new(
                    "in lift₀ argument",
                    "lift₀ expects a Time₀ term, but the argument is non-temporal",
                )),
            }
        }

        // derive₁(time, witness) → Time₁, time must be Time₀
        TimeTerm::Derive1 { time, .. } => {
            let inner_sort = infer_temporal_sort(time)?;
            match inner_sort {
                TemporalSort::Time0 => Ok(TemporalSort::Time1),
                TemporalSort::Time1 => Err(TemporalError::new(
                    "in derive₁ first argument",
                    "derive₁ expects a Time₀ term as its first argument, \
                     but received a Time₁ term; retroactive rewrites cannot \
                     reach frozen time",
                )),
                TemporalSort::NonTemporal => Err(TemporalError::new(
                    "in derive₁ first argument",
                    "derive₁ expects a Time₀ term as its first argument, \
                     but received a non-temporal term",
                )),
            }
        }

        // Time literals and variables are non-temporal until annotated.
        TimeTerm::Literal(_) | TimeTerm::Var { .. } => Ok(TemporalSort::NonTemporal),
    }
}

/// Unify two temporal sorts, yielding an error if they conflict.
fn unify_sorts(
    s1: TemporalSort,
    s2: TemporalSort,
    location: &str,
) -> Result<TemporalSort, TemporalError> {
    match (s1, s2) {
        (TemporalSort::Time0, TemporalSort::Time0) => Ok(TemporalSort::Time0),
        (TemporalSort::Time1, TemporalSort::Time1) => Ok(TemporalSort::Time1),
        (TemporalSort::NonTemporal, TemporalSort::NonTemporal) => Ok(TemporalSort::NonTemporal),
        (TemporalSort::NonTemporal, other) | (other, TemporalSort::NonTemporal) => Ok(other),
        (TemporalSort::Time0, TemporalSort::Time1) | (TemporalSort::Time1, TemporalSort::Time0) => {
            Err(TemporalError::new(
                location,
                format!(
                    "cannot mix {} and {} without explicit coercion (lift₀ or derive₁)",
                    s1, s2
                ),
            ))
        }
    }
}

// ---------------------------------------------------------------------------
// infer_term_temporal_sort — sort inference on Term
// ---------------------------------------------------------------------------

/// Infer the temporal sort of a `Term`.
///
/// Most core terms are non-temporal. Temporal sort arises from:
/// - `Term::Lift0` (produces Time₁ from a Time₀ sub-term)
/// - `Term::Derive1` (produces Time₁ from a Time₀ sub-term + witness)
/// - `Term::ModalAt` / `ModalEventually` / `ModalAlways` (inherit from `TimeTerm`)
/// - Composition: `Lambda` body, `Let` body, `App` function
pub fn infer_term_temporal_sort(term: &Term) -> Result<TemporalSort, TemporalError> {
    match term {
        // Temporal coercions at the term level.
        Term::Lift0 { time } => {
            let inner_sort = infer_term_temporal_sort(time)?;
            match inner_sort {
                TemporalSort::Time0 => Ok(TemporalSort::Time1),
                TemporalSort::Time1 => Err(TemporalError::new(
                    "in lift₀ argument",
                    "lift₀ expects a Time₀ term, but the argument is already Time₁; \
                     there is no coercion from Time₁ to Time₀",
                )),
                TemporalSort::NonTemporal => Err(TemporalError::new(
                    "in lift₀ argument",
                    "lift₀ expects a Time₀ term, but the argument is non-temporal",
                )),
            }
        }

        Term::Derive1 { time, .. } => {
            let inner_sort = infer_term_temporal_sort(time)?;
            match inner_sort {
                TemporalSort::Time0 => Ok(TemporalSort::Time1),
                TemporalSort::Time1 => Err(TemporalError::new(
                    "in derive₁ first argument",
                    "derive₁ expects a Time₀ term as its first argument, \
                     but received a Time₁ term; retroactive rewrites cannot \
                     reach frozen time",
                )),
                TemporalSort::NonTemporal => Err(TemporalError::new(
                    "in derive₁ first argument",
                    "derive₁ expects a Time₀ term, but received a non-temporal term",
                )),
            }
        }

        // Modal terms inherit from their time sub-term.
        Term::ModalAt { time, .. } => infer_temporal_sort(time),
        Term::ModalEventually { time, .. } => infer_temporal_sort(time),
        Term::ModalAlways { from, to, .. } => {
            let s1 = infer_temporal_sort(from)?;
            let s2 = infer_temporal_sort(to)?;
            unify_sorts(s1, s2, "in □ interval bounds")
        }

        // Lambda body propagates.
        Term::Lambda { body, .. } => infer_term_temporal_sort(body),

        // Let body propagates.
        Term::Let { body, .. } => infer_term_temporal_sort(body),

        // Application: result from function.
        Term::App { func, .. } => infer_term_temporal_sort(func),

        // Pi types are non-temporal (type-level).
        Term::Pi { .. } => Ok(TemporalSort::NonTemporal),

        // Everything else is non-temporal.
        _ => Ok(TemporalSort::NonTemporal),
    }
}

// ---------------------------------------------------------------------------
// check_temporal_stratification — full recursive check on Term
// ---------------------------------------------------------------------------

/// Verify that a `Term` respects the temporal stratification invariant.
///
/// This walks the entire term tree and checks that:
/// 1. `lift₀` is only applied to Time₀ terms
/// 2. `derive₁` first argument is Time₀
/// 3. Time₀ and Time₁ are never mixed in the same expression without coercion
/// 4. There is no retraction from Time₁ to Time₀
/// 5. Temporal consistency is maintained in binders, let bodies, and modalities
///
/// Returns `Ok(())` if the term is well-stratified, or a `TemporalError`
/// describing the first violation found.
pub fn check_temporal_stratification(term: &Term) -> Result<(), TemporalError> {
    check_term_recursive(term, "top-level", 0)
}

fn check_time_term_recursive(
    tt: &TimeTerm,
    _context: &str,
    depth: usize,
) -> Result<(), TemporalError> {
    if depth > MAX_DEPTH {
        return Err(TemporalError::new(
            _context,
            format!("recursion depth limit exceeded ({MAX_DEPTH}); term is too deeply nested"),
        ));
    }
    match tt {
        TimeTerm::AsOf0(inner) => check_term_recursive(inner, "in asof₀ argument", depth + 1),
        TimeTerm::AsOf1(inner) => check_term_recursive(inner, "in asof₁ argument", depth + 1),
        TimeTerm::Lift0(inner) => {
            check_time_term_recursive(inner, "in lift₀ argument", depth + 1)?;
            let inner_sort = infer_temporal_sort(inner)?;
            if inner_sort == TemporalSort::Time1 {
                return Err(TemporalError::new(
                    "in lift₀ argument",
                    "lift₀ expects a Time₀ term, but the argument is Time₁; \
                     there is no retraction from Time₁ to Time₀",
                ));
            }
            if inner_sort == TemporalSort::NonTemporal {
                return Err(TemporalError::new(
                    "in lift₀ argument",
                    "lift₀ expects a Time₀ term, but the argument is non-temporal",
                ));
            }
            Ok(())
        }
        TimeTerm::Derive1 { time, witness } => {
            check_time_term_recursive(time, "in derive₁ first argument", depth + 1)?;
            check_term_recursive(&witness.term, "in derive₁ witness", depth + 1)?;
            let time_sort = infer_temporal_sort(time)?;
            if time_sort == TemporalSort::Time1 {
                return Err(TemporalError::new(
                    "in derive₁ first argument",
                    "derive₁ expects a Time₀ term, but received Time₁; \
                     retroactive rewrites cannot reach frozen time",
                ));
            }
            if time_sort == TemporalSort::NonTemporal {
                return Err(TemporalError::new(
                    "in derive₁ first argument",
                    "derive₁ expects a Time₀ term, but received a non-temporal term",
                ));
            }
            Ok(())
        }
        TimeTerm::Literal(_) | TimeTerm::Var { .. } => Ok(()),
    }
}

fn check_term_recursive(term: &Term, context: &str, depth: usize) -> Result<(), TemporalError> {
    if depth > MAX_DEPTH {
        return Err(TemporalError::new(
            context,
            format!("recursion depth limit exceeded ({MAX_DEPTH}); term is too deeply nested"),
        ));
    }
    match term {
        // Temporal coercions at the term level.
        Term::Lift0 { time } => {
            check_term_recursive(time, "in lift₀ argument", depth + 1)?;
            let inner_sort = infer_term_temporal_sort(time)?;
            if inner_sort == TemporalSort::Time1 {
                return Err(TemporalError::new(
                    "in lift₀ argument",
                    "lift₀ expects a Time₀ term, but the argument is Time₁; \
                     there is no retraction from Time₁ to Time₀",
                ));
            }
            if inner_sort == TemporalSort::NonTemporal {
                return Err(TemporalError::new(
                    "in lift₀ argument",
                    "lift₀ expects a Time₀ term, but the argument is non-temporal",
                ));
            }
            Ok(())
        }

        Term::Derive1 { time, witness } => {
            check_term_recursive(time, "in derive₁ first argument", depth + 1)?;
            check_term_recursive(witness, "in derive₁ witness", depth + 1)?;
            let time_sort = infer_term_temporal_sort(time)?;
            if time_sort == TemporalSort::Time1 {
                return Err(TemporalError::new(
                    "in derive₁ first argument",
                    "derive₁ expects a Time₀ term, but received Time₁; \
                     retroactive rewrites cannot reach frozen time",
                ));
            }
            if time_sort == TemporalSort::NonTemporal {
                return Err(TemporalError::new(
                    "in derive₁ first argument",
                    "derive₁ expects a Time₀ term, but received a non-temporal term",
                ));
            }
            Ok(())
        }

        // Modal terms: check time sub-terms and body.
        Term::ModalAt { time, body } => {
            check_time_term_recursive(time, "in @ time argument", depth + 1)?;
            check_term_recursive(body, "in @ body", depth + 1)
        }

        Term::ModalEventually { time, body } => {
            check_time_term_recursive(time, "in ◇ time argument", depth + 1)?;
            check_term_recursive(body, "in ◇ body", depth + 1)
        }

        Term::ModalAlways { from, to, body } => {
            check_time_term_recursive(from, "in □ interval start", depth + 1)?;
            check_time_term_recursive(to, "in □ interval end", depth + 1)?;
            check_term_recursive(body, "in □ body", depth + 1)?;
            let s1 = infer_temporal_sort(from)?;
            let s2 = infer_temporal_sort(to)?;
            unify_sorts(s1, s2, "in □ interval bounds")?;
            Ok(())
        }

        // Pi: domain and codomain must be compatible if both temporal.
        Term::Pi {
            domain, codomain, ..
        } => {
            check_term_recursive(domain, "in Π domain", depth + 1)?;
            check_term_recursive(codomain, "in Π codomain", depth + 1)?;
            let ds = infer_term_temporal_sort(domain)?;
            let cs = infer_term_temporal_sort(codomain)?;
            unify_sorts(ds, cs, &format!("in Π type ({context})"))?;
            Ok(())
        }

        // Lambda.
        Term::Lambda { domain, body, .. } => {
            check_term_recursive(domain, "in λ domain", depth + 1)?;
            check_term_recursive(body, "in λ body", depth + 1)
        }

        // Let: value and body must have compatible temporal sorts.
        Term::Let {
            ty,
            val,
            body,
            binder,
            ..
        } => {
            check_term_recursive(
                ty,
                &format!("in let {} type annotation", binder.name),
                depth + 1,
            )?;
            check_term_recursive(val, &format!("in let {} value", binder.name), depth + 1)?;
            check_term_recursive(body, &format!("in let {} body", binder.name), depth + 1)?;
            let vs = infer_term_temporal_sort(val)?;
            let bs = infer_term_temporal_sort(body)?;
            unify_sorts(vs, bs, &format!("in let {} binding", binder.name))?;
            Ok(())
        }

        // Application: function and argument must be compatible.
        Term::App { func, arg } => {
            check_term_recursive(
                func,
                &format!("in application function ({context})"),
                depth + 1,
            )?;
            check_term_recursive(
                arg,
                &format!("in application argument ({context})"),
                depth + 1,
            )?;
            let fs = infer_term_temporal_sort(func)?;
            let as_ = infer_term_temporal_sort(arg)?;
            unify_sorts(fs, as_, &format!("in application ({context})"))?;
            Ok(())
        }

        // Sigma.
        Term::Sigma { fst_ty, snd_ty, .. } => {
            check_term_recursive(fst_ty, "in Σ first type", depth + 1)?;
            check_term_recursive(snd_ty, "in Σ second type", depth + 1)
        }

        // Pair.
        Term::Pair { fst, snd } => {
            check_term_recursive(fst, "in pair first", depth + 1)?;
            check_term_recursive(snd, "in pair second", depth + 1)
        }

        // Projection.
        Term::Proj { pair, .. } => check_term_recursive(pair, "in projection", depth + 1),

        // Annotation.
        Term::Annot { term: inner, ty } => {
            check_term_recursive(inner, "in annotation term", depth + 1)?;
            check_term_recursive(ty, "in annotation type", depth + 1)
        }

        // Match.
        Term::Match {
            scrutinee,
            return_ty,
            branches,
        } => {
            check_term_recursive(scrutinee, "in match scrutinee", depth + 1)?;
            check_term_recursive(return_ty, "in match return type", depth + 1)?;
            for br in branches {
                check_term_recursive(&br.body, "in match branch body", depth + 1)?;
            }
            Ok(())
        }

        // Rec.
        Term::Rec { ty, body, .. } => {
            check_term_recursive(ty, "in fix type", depth + 1)?;
            check_term_recursive(body, "in fix body", depth + 1)
        }

        // Inductive intro.
        Term::InductiveIntro { args, .. } => {
            for arg in args {
                check_term_recursive(arg, "in constructor argument", depth + 1)?;
            }
            Ok(())
        }

        // Modal intro/elim (tribunal).
        Term::ModalIntro { body, .. } => check_term_recursive(body, "in ⟦T⟧ body", depth + 1),
        Term::ModalElim {
            term: inner,
            witness,
            ..
        } => {
            check_term_recursive(inner, "in coerce term", depth + 1)?;
            check_term_recursive(witness, "in coerce witness", depth + 1)
        }

        // Sanctions dominance.
        Term::SanctionsDominance { proof } => {
            check_term_recursive(proof, "in sanctions-dominance proof", depth + 1)
        }

        // Defeasible.
        Term::Defeasible(rule) => {
            check_term_recursive(&rule.base_body, "in defeasible body", depth + 1)?;
            for exc in &rule.exceptions {
                check_term_recursive(&exc.guard, "in exception guard", depth + 1)?;
                check_term_recursive(&exc.body, "in exception body", depth + 1)?;
            }
            Ok(())
        }

        // Defeat.
        Term::DefeatElim { rule } => check_term_recursive(rule, "in defeat rule", depth + 1),

        // Hole.
        Term::Hole(hole) => check_term_recursive(&hole.ty, "in hole type", depth + 1),

        // Hole fill.
        Term::HoleFill { filler, pcauth, .. } => {
            check_term_recursive(filler, "in fill filler", depth + 1)?;
            check_term_recursive(pcauth, "in fill pcauth", depth + 1)
        }

        // Unlock.
        Term::Unlock { effect_row, body } => {
            check_term_recursive(effect_row, "in unlock effect", depth + 1)?;
            check_term_recursive(body, "in unlock body", depth + 1)
        }

        // Principle balance.
        Term::PrincipleBalance(step) => {
            check_term_recursive(&step.verdict, "in principle balance verdict", depth + 1)?;
            check_term_recursive(&step.rationale, "in principle balance rationale", depth + 1)
        }

        // Leaves with no sub-terms.
        Term::Var { .. }
        | Term::Sort(_)
        | Term::Constant(_)
        | Term::AxiomUse { .. }
        | Term::ContentRefTerm(_)
        | Term::IntLit(_)
        | Term::RatLit(_, _)
        | Term::StringLit(_) => Ok(()),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Ident, RewriteWitness};

    // Helpers for concise term construction.

    fn ident(name: &str) -> Ident {
        Ident {
            name: name.to_string(),
        }
    }

    fn var_term(name: &str) -> Term {
        Term::Var {
            name: ident(name),
            index: 0,
        }
    }

    fn sort_prop() -> Term {
        Term::Sort(crate::ast::Sort::Prop)
    }

    fn time_asof0(t: Term) -> TimeTerm {
        TimeTerm::AsOf0(Box::new(t))
    }

    fn time_asof1(t: Term) -> TimeTerm {
        TimeTerm::AsOf1(Box::new(t))
    }

    fn time_lift0(tt: TimeTerm) -> TimeTerm {
        TimeTerm::Lift0(Box::new(tt))
    }

    fn time_derive1(tt: TimeTerm, w: Term) -> TimeTerm {
        TimeTerm::Derive1 {
            time: Box::new(tt),
            witness: RewriteWitness { term: Box::new(w) },
        }
    }

    fn term_lift0(t: Term) -> Term {
        Term::Lift0 { time: Box::new(t) }
    }

    fn term_derive1(t: Term, w: Term) -> Term {
        Term::Derive1 {
            time: Box::new(t),
            witness: Box::new(w),
        }
    }

    fn term_modal_at(tt: TimeTerm, body: Term) -> Term {
        Term::ModalAt {
            time: tt,
            body: Box::new(body),
        }
    }

    fn term_modal_always(from: TimeTerm, to: TimeTerm, body: Term) -> Term {
        Term::ModalAlways {
            from,
            to,
            body: Box::new(body),
        }
    }

    fn term_modal_eventually(tt: TimeTerm, body: Term) -> Term {
        Term::ModalEventually {
            time: tt,
            body: Box::new(body),
        }
    }

    fn term_pi(name: &str, dom: Term, cod: Term) -> Term {
        Term::Pi {
            binder: ident(name),
            domain: Box::new(dom),
            effect_row: None,
            codomain: Box::new(cod),
        }
    }

    fn term_lambda(name: &str, dom: Term, body: Term) -> Term {
        Term::Lambda {
            binder: ident(name),
            domain: Box::new(dom),
            body: Box::new(body),
        }
    }

    fn term_let(name: &str, ty: Term, val: Term, body: Term) -> Term {
        Term::Let {
            binder: ident(name),
            ty: Box::new(ty),
            val: Box::new(val),
            body: Box::new(body),
        }
    }

    fn term_app(f: Term, a: Term) -> Term {
        Term::App {
            func: Box::new(f),
            arg: Box::new(a),
        }
    }

    // ── Test 1: asof₀ is Time₀ ──────────────────────────────────────────

    #[test]
    fn asof0_is_time0() {
        let tt = time_asof0(var_term("transition"));
        assert_eq!(infer_temporal_sort(&tt).unwrap(), TemporalSort::Time0);
    }

    // ── Test 2: lift₀ coerces Time₀ to Time₁ ────────────────────────────

    #[test]
    fn lift0_coerces_to_time1() {
        let tt = time_lift0(time_asof0(var_term("t")));
        assert_eq!(infer_temporal_sort(&tt).unwrap(), TemporalSort::Time1);
    }

    // ── Test 3: derive₁ produces Time₁ ──────────────────────────────────

    #[test]
    fn derive1_produces_time1() {
        let tt = time_derive1(time_asof0(var_term("t")), var_term("witness"));
        assert_eq!(infer_temporal_sort(&tt).unwrap(), TemporalSort::Time1);
    }

    // ── Test 4: mixing Time₀ and Time₁ without coercion is an error ─────

    #[test]
    fn mixing_time0_and_time1_without_coercion_is_error() {
        // ModalAt with Time₀ applied to a term, then ModalAt with Time₁
        // — mixing via application.
        let t0_modal = term_modal_at(time_asof0(var_term("a")), var_term("phi"));
        let t1_modal = term_modal_at(time_asof1(var_term("b")), var_term("psi"));
        let mixed = term_app(t0_modal, t1_modal);
        let err = check_temporal_stratification(&mixed).unwrap_err();
        assert!(
            err.description.contains("cannot mix"),
            "expected mixing error, got: {}",
            err
        );
    }

    // ── Test 5: no retraction from Time₁ to Time₀ ───────────────────────

    #[test]
    fn no_retraction_time1_to_time0() {
        // lift₀ applied to asof₁ — Time₁ cannot be coerced back to Time₀.
        let tt = time_lift0(time_asof1(var_term("t")));
        let err = infer_temporal_sort(&tt).unwrap_err();
        assert!(
            err.description.contains("Time₁"),
            "expected retraction error, got: {}",
            err
        );
    }

    // ── Test 6: lift₀ inside derive₁ is valid ───────────────────────────

    #[test]
    fn lift0_inside_derive1_is_valid() {
        // derive₁(asof₀(t), lift₀(asof₀(t2)).term as witness)
        // The witness is a separate path; derive₁ only checks the first arg.
        let tt = time_derive1(time_asof0(var_term("t")), var_term("some_witness"));
        assert_eq!(infer_temporal_sort(&tt).unwrap(), TemporalSort::Time1);

        // Also check: a well-formed term with lift₀ as the witness proof.
        let term = term_derive1(
            term_modal_at(time_asof0(var_term("t")), var_term("phi")),
            term_lift0(term_modal_at(time_asof0(var_term("t2")), var_term("psi"))),
        );
        // This should pass check (the term-level derive₁ with Time₀ first arg
        // and a witness that is independently well-formed).
        assert!(check_temporal_stratification(&term).is_ok());
    }

    // ── Test 7: nested lifts ─────────────────────────────────────────────

    #[test]
    fn nested_lift0_is_error() {
        // lift₀(lift₀(asof₀(t))) — the outer lift₀ receives Time₁, illegal.
        let inner = time_lift0(time_asof0(var_term("t")));
        let outer = time_lift0(inner);
        let err = infer_temporal_sort(&outer).unwrap_err();
        assert!(
            err.description.contains("Time₁"),
            "expected nested lift error, got: {}",
            err
        );
    }

    // ── Test 8: temporal sort in Pi domain vs codomain ───────────────────

    #[test]
    fn pi_domain_time0_codomain_time1_is_error() {
        let term = term_pi(
            "x",
            term_modal_at(time_asof0(var_term("t")), var_term("phi")),
            term_modal_at(time_asof1(var_term("t_prime")), var_term("psi")),
        );
        let err = check_temporal_stratification(&term).unwrap_err();
        assert!(
            err.description.contains("cannot mix"),
            "expected mixing error in Π, got: {}",
            err
        );
    }

    #[test]
    fn pi_both_time0_is_ok() {
        let term = term_pi(
            "x",
            term_modal_at(time_asof0(var_term("t")), var_term("phi")),
            term_modal_at(time_asof0(var_term("t_prime")), var_term("psi")),
        );
        assert!(check_temporal_stratification(&term).is_ok());
    }

    #[test]
    fn pi_domain_time0_codomain_lifted_still_mixes() {
        // Π(x : @asof₀(t) φ) . @lift₀(asof₀(t')) ψ
        // Domain is Time₀, codomain is Time₁ via lift₀ — mixing in the Pi.
        let term = term_pi(
            "x",
            term_modal_at(time_asof0(var_term("t")), var_term("phi")),
            term_modal_at(time_lift0(time_asof0(var_term("t_prime"))), var_term("psi")),
        );
        let err = check_temporal_stratification(&term).unwrap_err();
        assert!(err.description.contains("cannot mix"));
    }

    // ── Test 9: temporal consistency in let binding ──────────────────────

    #[test]
    fn let_binding_value_time0_body_time1_is_error() {
        let term = term_let(
            "x",
            sort_prop(),
            term_modal_at(time_asof0(var_term("a")), var_term("phi")),
            term_modal_at(time_asof1(var_term("b")), var_term("psi")),
        );
        let err = check_temporal_stratification(&term).unwrap_err();
        assert!(
            err.description.contains("cannot mix"),
            "expected mixing error in let, got: {}",
            err
        );
    }

    #[test]
    fn let_binding_consistent_sorts_is_ok() {
        let term = term_let(
            "x",
            sort_prop(),
            term_modal_at(time_asof0(var_term("a")), var_term("phi")),
            term_modal_at(time_asof0(var_term("b")), var_term("psi")),
        );
        assert!(check_temporal_stratification(&term).is_ok());
    }

    // ── Test 10: check_temporal_stratification accepts well-sorted terms ─

    #[test]
    fn well_sorted_complex_term_passes() {
        // let t0 : Prop := @lift₀(asof₀(transition)) φ in
        //   derive₁(@asof₀(other) ψ, witness)
        // Both value and body are Time₁.
        let term = term_let(
            "t0",
            sort_prop(),
            term_modal_at(
                time_lift0(time_asof0(var_term("transition"))),
                var_term("phi"),
            ),
            term_derive1(
                term_modal_at(time_asof0(var_term("other")), var_term("psi")),
                var_term("witness"),
            ),
        );
        assert!(check_temporal_stratification(&term).is_ok());
    }

    // ── Test 11: check_temporal_stratification rejects ill-sorted terms ──

    #[test]
    fn ill_sorted_derive1_with_time1_input_rejected() {
        // derive₁(@asof₁(t) φ, w) — first argument is Time₁, illegal.
        let term = term_derive1(
            term_modal_at(time_asof1(var_term("t")), var_term("phi")),
            var_term("w"),
        );
        let err = check_temporal_stratification(&term).unwrap_err();
        assert!(
            err.description.contains("Time₁") || err.description.contains("retroactive"),
            "expected derive₁ rejection, got: {}",
            err
        );
    }

    // ── Test 12: asof₁ is Time₁ ─────────────────────────────────────────

    #[test]
    fn asof1_is_time1() {
        let tt = time_asof1(var_term("rewrite_transition"));
        assert_eq!(infer_temporal_sort(&tt).unwrap(), TemporalSort::Time1);
    }

    // ── Test 13: non-temporal terms pass stratification ──────────────────

    #[test]
    fn non_temporal_terms_pass() {
        let term = term_app(var_term("f"), var_term("x"));
        assert!(check_temporal_stratification(&term).is_ok());
        assert_eq!(
            infer_term_temporal_sort(&term).unwrap(),
            TemporalSort::NonTemporal
        );
    }

    // ── Test 14: temporal modality @ preserves sort ──────────────────────

    #[test]
    fn at_modality_preserves_sort() {
        let t0_modal = term_modal_at(time_asof0(var_term("t")), var_term("phi"));
        assert_eq!(
            infer_term_temporal_sort(&t0_modal).unwrap(),
            TemporalSort::Time0
        );

        let t1_modal = term_modal_at(time_asof1(var_term("t")), var_term("phi"));
        assert_eq!(
            infer_term_temporal_sort(&t1_modal).unwrap(),
            TemporalSort::Time1
        );
    }

    // ── Test 15: □ interval bounds must agree ────────────────────────────

    #[test]
    fn box_interval_bounds_must_agree() {
        let term = term_modal_always(
            time_asof0(var_term("a")),
            time_asof1(var_term("b")),
            var_term("body"),
        );
        let err = check_temporal_stratification(&term).unwrap_err();
        assert!(err.description.contains("cannot mix"));
    }

    #[test]
    fn box_homogeneous_bounds_ok() {
        let term = term_modal_always(
            time_asof0(var_term("a")),
            time_asof0(var_term("b")),
            var_term("body"),
        );
        assert!(check_temporal_stratification(&term).is_ok());
    }

    // ── Test 16: diamond modality sort ───────────────────────────────────

    #[test]
    fn diamond_modality_sort() {
        let term = term_modal_eventually(time_lift0(time_asof0(var_term("t"))), var_term("phi"));
        assert_eq!(
            infer_term_temporal_sort(&term).unwrap(),
            TemporalSort::Time1
        );
    }

    // ── Test 17: lambda body temporal sort propagation ───────────────────

    #[test]
    fn lambda_body_sort_propagates() {
        let term = term_lambda(
            "x",
            sort_prop(),
            term_modal_at(time_asof0(var_term("t")), var_term("phi")),
        );
        assert_eq!(
            infer_term_temporal_sort(&term).unwrap(),
            TemporalSort::Time0
        );
    }

    // ── Test 18: TemporalError display ───────────────────────────────────

    #[test]
    fn temporal_error_display() {
        let err = TemporalError::new("in lift₀", "bad sort");
        let msg = err.to_string();
        assert!(msg.contains("in lift₀"));
        assert!(msg.contains("bad sort"));
        assert!(msg.contains("temporal stratification error"));
    }

    // ── Test 19: TemporalSort display ────────────────────────────────────

    #[test]
    fn temporal_sort_display() {
        assert_eq!(TemporalSort::Time0.to_string(), "Time₀");
        assert_eq!(TemporalSort::Time1.to_string(), "Time₁");
        assert_eq!(TemporalSort::NonTemporal.to_string(), "non-temporal");
    }

    // ── Test 20: lift₀ of non-temporal TimeTerm is error ─────────────────

    #[test]
    fn lift0_of_non_temporal_is_error() {
        let tt = time_lift0(TimeTerm::Var {
            name: ident("x"),
            index: 0,
        });
        let err = infer_temporal_sort(&tt).unwrap_err();
        assert!(err.description.contains("non-temporal"));
    }

    // ── Test 21: derive₁ of non-temporal TimeTerm is error ───────────────

    #[test]
    fn derive1_of_non_temporal_is_error() {
        let tt = time_derive1(
            TimeTerm::Var {
                name: ident("x"),
                index: 0,
            },
            var_term("w"),
        );
        let err = infer_temporal_sort(&tt).unwrap_err();
        assert!(err.description.contains("non-temporal"));
    }
}
