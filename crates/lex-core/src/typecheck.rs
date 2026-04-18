#![allow(clippy::result_large_err)]

//! Bidirectional type checker for the Core Lex **admissible fragment**.
//!
//! Implements the typing judgments and executable admissibility boundary
//! documented in `docs/language-reference.md`.
//!
//! The checker operates on [`crate::ast::Term`] with De Bruijn indices and uses
//! a bidirectional discipline: [`infer`] synthesizes a type, [`check`] verifies
//! a term against a known type. Conversion is up to α-equivalence (structural
//! for De Bruijn terms) and β/ζ-reduction.
//!
//! # Admissible Fragment
//!
//! Terms outside the admissible fragment are rejected with
//! [`TypeError::Admissibility`]. The conservatively rejected constructs are:
//! - `Rec` (fix — structural recursion checker not yet wired)
//! - `Hole` (surface discretion-hole syntax is parsed and elaborated, but not
//!   admitted by the checker)
//! - `Sigma`, `Pair`, `Proj` (require inductive type metadata)
//! - `Match` on non-prelude types (prelude-type matches are admissible)
//! - `AxiomUse` (requires axiom metadata)
//! - `InductiveIntro`, `HoleFill`, `DefeatElim` (not yet supported in the
//!   executable admissible checker)
//! - All modal forms (`ModalAt`, `ModalEventually`, `ModalAlways`,
//!   `ModalIntro`, `ModalElim`, `SanctionsDominance`)
//! - `PrincipleBalance`, `Unlock`, `Lift0`, `Derive1`, `ContentRefTerm`
//! - Unresolved level variables in `Sort`
//!
//! The admissible core checked here: `Var`, `Sort`, `Lambda`, `Pi` (pure),
//! `App`, `Annot`, `Let`, `Defeasible` (when all sub-terms are admissible),
//! `Match` on prelude constructor types (`ComplianceVerdict`, `ComplianceTag`,
//! `Bool`, `Nat`, `SanctionsResult`), and `Constant` when the enclosing
//! [`Context`] provides a global signature entry for the name.

use std::collections::HashMap;

use crate::ast::{EffectRow, Level, Pattern, QualIdent, Sort, Term};
use crate::prelude::is_prelude_constructor;

/// Maximum recursion depth for type-checking functions (shift, subst, whnf,
/// conv_eq, infer, check, check_admissibility). Prevents stack overflow on
/// deeply nested terms (e.g. a 256-deep Pi chain).
const MAX_DEPTH: usize = 192;

/// Maximum number of beta-reduction / zeta-reduction steps allowed in a single
/// WHNF evaluation chain. This is a *fuel* counter that decrements on each
/// reduction step, preventing wide computation (many sequential reductions at
/// shallow depth). Complementary to `MAX_DEPTH` which prevents deep recursion.
///
/// A chain of `(lam.id)(lam.id)...(Type_0)` consumes one fuel per step.
/// Normal terms (lambdas, Pi, sorts) never need more than a handful of steps.
const MAX_WHNF_FUEL: usize = 4096;

/// Maximum number of AST nodes allowed in a substitution result. Prevents
/// exponential blowup from nested let/application chains where each
/// substitution duplicates a growing term.
const MAX_SUBST_NODES: usize = 100_000;

// ---------------------------------------------------------------------------
// Typing context
// ---------------------------------------------------------------------------

/// Typing context Γ — a local binder stack plus a global constant signature.
///
/// De Bruijn index 0 refers to the most recently pushed entry (`entries.last()`).
/// Global constants are stable across local extensions. This is the
/// *checker's* context — lighter than `ast::Context` which carries a full
/// `ScopeFrame`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Context {
    /// Entries from outermost (index 0 in the Vec) to innermost (last).
    entries: Vec<Term>,
    /// Global constant signature available to the checker.
    globals: HashMap<QualIdent, Term>,
}

impl Context {
    /// The empty context.
    pub fn empty() -> Self {
        Self {
            entries: Vec::new(),
            globals: HashMap::new(),
        }
    }

    /// Extend the context with a new binding, returning a new context.
    pub fn extend(&self, ty: Term) -> Self {
        let mut entries = self.entries.clone();
        entries.push(ty);
        Self {
            entries,
            globals: self.globals.clone(),
        }
    }

    /// Look up a De Bruijn index. Returns `None` if out of range.
    pub fn lookup(&self, idx: u32) -> Option<&Term> {
        let len = self.entries.len();
        if (idx as usize) < len {
            Some(&self.entries[len - 1 - idx as usize])
        } else {
            None
        }
    }

    /// Number of bindings in the context.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the context is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Register a global constant in the signature, returning a new context.
    pub fn with_constant(&self, name: QualIdent, ty: Term) -> Self {
        let mut globals = self.globals.clone();
        globals.insert(name, ty);
        Self {
            entries: self.entries.clone(),
            globals,
        }
    }

    /// Register a simple single-segment global constant.
    pub fn with_named_constant(&self, name: &str, ty: Term) -> Self {
        self.with_constant(QualIdent::simple(name), ty)
    }

    /// Look up a global constant by qualified identifier.
    pub fn lookup_constant(&self, name: &QualIdent) -> Option<&Term> {
        self.globals.get(name)
    }

    /// Look up a simple single-segment global constant.
    pub fn lookup_named_constant(&self, name: &str) -> Option<&Term> {
        self.lookup_constant(&QualIdent::simple(name))
    }

    /// Whether a simple single-segment global constant is present.
    pub fn contains_named_constant(&self, name: &str) -> bool {
        self.lookup_named_constant(name).is_some()
    }

    /// Number of registered global constants.
    pub fn global_len(&self) -> usize {
        self.globals.len()
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Admissibility violation — the term is well-typed in full Core Lex but not
/// in the admissible fragment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdmissibilityViolation {
    /// `fix`/`Rec` without a verified structural recursion witness.
    RecNotSupported,
    /// Unfilled discretion hole.
    UnfilledHole,
    /// `Sigma` types require inductive type metadata.
    SigmaNotSupported,
    /// `Match` expression with a pattern on a non-prelude constructor type.
    MatchOnNonPreludeType {
        /// The constructor name that is not a prelude constructor.
        constructor_name: String,
    },
    /// `Match` scrutinee could not be resolved to a known prelude datatype.
    ///
    /// The scrutinee must either be a prelude constructor (e.g. `Compliant`,
    /// whose datatype is `ComplianceVerdict`) or a term whose inferred type
    /// is a named prelude datatype. Until the admissibility check is
    /// extended to run full type inference on the scrutinee, only the
    /// constructor-form is supported.
    MatchScrutineeDatatypeUnresolved,
    /// `Match` branch constructor does not belong to the scrutinee's
    /// datatype.
    ///
    /// e.g. scrutinee is a `ComplianceVerdict` but a branch matches `True`
    /// (constructor of `Bool`).
    MatchBranchConstructorMismatch {
        /// Datatype of the scrutinee.
        scrutinee_datatype: String,
        /// Constructor that does not belong to `scrutinee_datatype`.
        branch_constructor: String,
        /// Datatype the branch constructor actually belongs to, if known.
        branch_constructor_datatype: Option<String>,
    },
    /// `Match` expression is not exhaustive: not every constructor of the
    /// scrutinee's datatype is covered, and no wildcard branch is present.
    MatchNonExhaustive {
        /// Datatype of the scrutinee.
        scrutinee_datatype: String,
        /// Constructors that are missing from the branch set.
        missing_constructors: Vec<String>,
    },
    /// `Pair` introduction not yet supported.
    PairNotSupported,
    /// `Proj` projection not yet supported.
    ProjectionNotSupported,
    /// `Constant` requires a global signature.
    ConstantNotSupported,
    /// `AxiomUse` requires a global signature.
    AxiomNotSupported,
    /// `InductiveIntro` requires inductive type metadata.
    InductiveIntroNotSupported,
    /// `HoleFill` not yet supported.
    HoleFillNotSupported,
    /// `Defeasible` rule not yet supported.
    DefeasibleNotSupported,
    /// `DefeatElim` not yet supported.
    DefeatElimNotSupported,
    /// Modal terms not yet supported.
    ModalNotSupported,
    /// `SanctionsDominance` not yet supported.
    SanctionsDominanceNotSupported,
    /// `PrincipleBalance` not yet supported.
    PrincipleBalanceNotSupported,
    /// `Unlock` not yet supported.
    UnlockNotSupported,
    /// `Lift0`/`Derive1` temporal coercions not yet supported.
    TemporalCoercionNotSupported,
    /// `ContentRefTerm` requires resolution.
    ContentRefNotSupported,
    /// Literals are not yet supported in the admissible fragment.
    LiteralNotSupported,
    /// Unresolved level variable in a `Sort`.
    UnresolvedLevelVar(u32),
    /// Pi type with non-trivial effect row.
    EffectfulPiNotSupported,
}

impl std::fmt::Display for AdmissibilityViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::RecNotSupported => {
                write!(f, "fix/Rec requires structural recursion verification")
            }
            Self::UnfilledHole => write!(f, "unfilled discretion hole"),
            Self::SigmaNotSupported => write!(f, "Sigma-types not yet supported"),
            Self::MatchOnNonPreludeType { constructor_name } => write!(
                f,
                "match on non-prelude constructor type: '{}'",
                constructor_name
            ),
            Self::MatchScrutineeDatatypeUnresolved => write!(
                f,
                "match scrutinee datatype could not be resolved to a known prelude type"
            ),
            Self::MatchBranchConstructorMismatch {
                scrutinee_datatype,
                branch_constructor,
                branch_constructor_datatype,
            } => match branch_constructor_datatype {
                Some(dt) => write!(
                    f,
                    "match branch constructor '{}' (of datatype '{}') does not belong to the scrutinee datatype '{}'",
                    branch_constructor, dt, scrutinee_datatype
                ),
                None => write!(
                    f,
                    "match branch constructor '{}' does not belong to the scrutinee datatype '{}'",
                    branch_constructor, scrutinee_datatype
                ),
            },
            Self::MatchNonExhaustive {
                scrutinee_datatype,
                missing_constructors,
            } => write!(
                f,
                "match on '{}' is not exhaustive; missing constructors: [{}]; add a wildcard branch or cover the remaining cases",
                scrutinee_datatype,
                missing_constructors.join(", ")
            ),
            Self::PairNotSupported => write!(f, "pair introduction not yet supported"),
            Self::ProjectionNotSupported => write!(f, "projections not yet supported"),
            Self::ConstantNotSupported => write!(f, "constants require a global signature"),
            Self::AxiomNotSupported => write!(f, "axiom use requires a global signature"),
            Self::InductiveIntroNotSupported => {
                write!(f, "inductive introductions not yet supported")
            }
            Self::HoleFillNotSupported => write!(f, "hole filling not yet supported"),
            Self::DefeasibleNotSupported => write!(f, "defeasible rules not yet supported"),
            Self::DefeatElimNotSupported => write!(f, "defeat elimination not yet supported"),
            Self::ModalNotSupported => write!(f, "modal terms not yet supported"),
            Self::SanctionsDominanceNotSupported => {
                write!(f, "sanctions dominance not yet supported")
            }
            Self::PrincipleBalanceNotSupported => {
                write!(f, "principle balancing not yet supported")
            }
            Self::UnlockNotSupported => write!(f, "unlock not yet supported"),
            Self::TemporalCoercionNotSupported => {
                write!(f, "temporal coercions not yet supported")
            }
            Self::ContentRefNotSupported => {
                write!(f, "content-addressed references require resolution")
            }
            Self::LiteralNotSupported => write!(f, "literals not yet supported"),
            Self::UnresolvedLevelVar(idx) => {
                write!(f, "unresolved level variable l{}", idx)
            }
            Self::EffectfulPiNotSupported => {
                write!(f, "Pi types with effect rows not yet supported in checker")
            }
        }
    }
}

/// Type errors produced during bidirectional type checking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    /// Type mismatch: expected one type, found another.
    Mismatch {
        /// The context depth at the error site.
        ctx_len: usize,
        /// The term that failed to check.
        term: Term,
        /// The expected type.
        expected: Term,
        /// The inferred/found type.
        found: Term,
    },

    /// Unbound variable — De Bruijn index exceeds context depth.
    UnboundVar {
        /// The variable name.
        name: String,
        /// The De Bruijn index.
        index: u32,
        /// Context depth.
        ctx_len: usize,
    },

    /// Expected a Pi-type (function type) but found something else.
    NotAFunction { term: Term, found_type: Term },

    /// Expected a `Sort` but found something else.
    NotASort { term: Term, found: Term },

    /// A term that cannot be inferred (e.g., bare lambda without annotation).
    CannotInfer { term: Term },

    /// The term is outside the admissible fragment.
    Admissibility {
        violation: AdmissibilityViolation,
        term: Term,
    },

    /// Universe level overflow — level exceeds the omega limit or u64 range.
    LevelOverflow,

    /// Recursion limit exceeded — the term is too deeply nested.
    RecursionLimitExceeded,

    /// Beta-reduction fuel exhausted — the term requires too many reduction
    /// steps (likely a pathological application chain or substitution bomb).
    ReductionLimitExceeded,

    /// Substitution produced a term exceeding the maximum node count — likely
    /// an exponential blowup from nested let/application chains.
    SubstitutionBlowup {
        /// Number of AST nodes in the result that triggered the limit.
        node_count: usize,
    },
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Mismatch {
                expected, found, ..
            } => write!(
                f,
                "type mismatch: expected {:?}, found {:?}",
                expected, found
            ),
            Self::UnboundVar {
                name,
                index,
                ctx_len,
            } => write!(
                f,
                "unbound variable '{}' (index {}) in context of depth {}",
                name, index, ctx_len
            ),
            Self::NotAFunction { found_type, .. } => {
                write!(f, "expected function type, found {:?}", found_type)
            }
            Self::NotASort { found, .. } => {
                write!(f, "expected sort, found {:?}", found)
            }
            Self::CannotInfer { term } => {
                write!(f, "cannot infer type for {:?}", term)
            }
            Self::Admissibility { violation, .. } => {
                write!(f, "admissibility violation: {}", violation)
            }
            Self::LevelOverflow => {
                write!(f, "universe level overflow: level exceeds omega limit")
            }
            Self::RecursionLimitExceeded => {
                write!(
                    f,
                    "recursion limit exceeded: term nesting depth exceeds {}",
                    MAX_DEPTH
                )
            }
            Self::ReductionLimitExceeded => {
                write!(
                    f,
                    "reduction limit exceeded: beta/zeta reduction steps exceed {}",
                    MAX_WHNF_FUEL
                )
            }
            Self::SubstitutionBlowup { node_count } => {
                write!(
                    f,
                    "substitution blowup: result has {} nodes (limit {})",
                    node_count, MAX_SUBST_NODES
                )
            }
        }
    }
}

impl std::error::Error for TypeError {}

// ---------------------------------------------------------------------------
// Level evaluation
// ---------------------------------------------------------------------------

/// The omega limit — levels at or beyond this are rejected (mirrors `levels::OMEGA_LIMIT`).
const OMEGA_LIMIT: u64 = 1_000_000;

/// Evaluate a level expression to a concrete `u64`.
///
/// Returns `None` if the expression contains unresolved level variables
/// **or** if the result overflows `u64` / exceeds [`OMEGA_LIMIT`].
fn eval_level(level: &Level) -> Option<u64> {
    let result = match level {
        Level::Nat(n) => Some(*n),
        Level::Var(_) => None,
        Level::Succ(base, n) => {
            let b = eval_level(base)?;
            let v = b.checked_add(*n)?;
            Some(v)
        }
        Level::Max(a, b) => {
            let ea = eval_level(a)?;
            let eb = eval_level(b)?;
            Some(ea.max(eb))
        }
    };
    // Reject levels that reach or exceed the omega limit.
    result.filter(|&v| v < OMEGA_LIMIT)
}

/// Find the first unresolved level variable index.
fn find_level_var(level: &Level) -> Option<u32> {
    match level {
        Level::Nat(_) => None,
        Level::Var(lv) => Some(lv.index),
        Level::Succ(base, _) => find_level_var(base),
        Level::Max(a, b) => find_level_var(a).or_else(|| find_level_var(b)),
    }
}

// ---------------------------------------------------------------------------
// Substitution and shifting
// ---------------------------------------------------------------------------

/// Shift all free variables (De Bruijn indices >= `cutoff`) by `amount`.
fn shift(term: &Term, cutoff: u32, amount: i64, depth: usize) -> Result<Term, TypeError> {
    if depth > MAX_DEPTH {
        return Err(TypeError::RecursionLimitExceeded);
    }
    match term {
        Term::Var { name, index } => {
            if *index >= cutoff {
                Ok(Term::Var {
                    name: name.clone(),
                    index: (*index as i64 + amount) as u32,
                })
            } else {
                Ok(term.clone())
            }
        }
        Term::Sort(_) => Ok(term.clone()),
        Term::Lambda {
            binder,
            domain,
            body,
        } => Ok(Term::Lambda {
            binder: binder.clone(),
            domain: Box::new(shift(domain, cutoff, amount, depth + 1)?),
            body: Box::new(shift(body, cutoff + 1, amount, depth + 1)?),
        }),
        Term::Pi {
            binder,
            domain,
            effect_row,
            codomain,
        } => Ok(Term::Pi {
            binder: binder.clone(),
            domain: Box::new(shift(domain, cutoff, amount, depth + 1)?),
            effect_row: effect_row.clone(),
            codomain: Box::new(shift(codomain, cutoff + 1, amount, depth + 1)?),
        }),
        Term::App { func, arg } => Ok(Term::App {
            func: Box::new(shift(func, cutoff, amount, depth + 1)?),
            arg: Box::new(shift(arg, cutoff, amount, depth + 1)?),
        }),
        Term::Annot { term: t, ty } => Ok(Term::Annot {
            term: Box::new(shift(t, cutoff, amount, depth + 1)?),
            ty: Box::new(shift(ty, cutoff, amount, depth + 1)?),
        }),
        Term::Let {
            binder,
            ty,
            val,
            body,
        } => Ok(Term::Let {
            binder: binder.clone(),
            ty: Box::new(shift(ty, cutoff, amount, depth + 1)?),
            val: Box::new(shift(val, cutoff, amount, depth + 1)?),
            body: Box::new(shift(body, cutoff + 1, amount, depth + 1)?),
        }),
        // All other term forms are outside the admissible fragment and
        // will be rejected by the admissibility checker before shift/subst.
        _ => Ok(term.clone()),
    }
}

/// Substitute `replacement` for De Bruijn index `target` in `term`.
fn subst(term: &Term, target: u32, replacement: &Term, depth: usize) -> Result<Term, TypeError> {
    if depth > MAX_DEPTH {
        return Err(TypeError::RecursionLimitExceeded);
    }
    match term {
        Term::Var { name, index } => {
            if *index == target {
                Ok(replacement.clone())
            } else if *index > target {
                Ok(Term::Var {
                    name: name.clone(),
                    index: *index - 1,
                })
            } else {
                Ok(term.clone())
            }
        }
        Term::Sort(_) => Ok(term.clone()),
        Term::Lambda {
            binder,
            domain,
            body,
        } => {
            let new_domain = subst(domain, target, replacement, depth + 1)?;
            let shifted_repl = shift(replacement, 0, 1, depth + 1)?;
            let new_body = subst(body, target + 1, &shifted_repl, depth + 1)?;
            Ok(Term::Lambda {
                binder: binder.clone(),
                domain: Box::new(new_domain),
                body: Box::new(new_body),
            })
        }
        Term::Pi {
            binder,
            domain,
            effect_row,
            codomain,
        } => {
            let new_domain = subst(domain, target, replacement, depth + 1)?;
            let shifted_repl = shift(replacement, 0, 1, depth + 1)?;
            let new_codomain = subst(codomain, target + 1, &shifted_repl, depth + 1)?;
            Ok(Term::Pi {
                binder: binder.clone(),
                domain: Box::new(new_domain),
                effect_row: effect_row.clone(),
                codomain: Box::new(new_codomain),
            })
        }
        Term::App { func, arg } => Ok(Term::App {
            func: Box::new(subst(func, target, replacement, depth + 1)?),
            arg: Box::new(subst(arg, target, replacement, depth + 1)?),
        }),
        Term::Annot { term: t, ty } => Ok(Term::Annot {
            term: Box::new(subst(t, target, replacement, depth + 1)?),
            ty: Box::new(subst(ty, target, replacement, depth + 1)?),
        }),
        Term::Let {
            binder,
            ty,
            val,
            body,
        } => {
            let new_ty = subst(ty, target, replacement, depth + 1)?;
            let new_val = subst(val, target, replacement, depth + 1)?;
            let shifted_repl = shift(replacement, 0, 1, depth + 1)?;
            let new_body = subst(body, target + 1, &shifted_repl, depth + 1)?;
            Ok(Term::Let {
                binder: binder.clone(),
                ty: Box::new(new_ty),
                val: Box::new(new_val),
                body: Box::new(new_body),
            })
        }
        // Non-admissible terms: clone as-is (rejected by checker).
        _ => Ok(term.clone()),
    }
}

// ---------------------------------------------------------------------------
// Term size measurement
// ---------------------------------------------------------------------------

/// Count the number of AST nodes in a term (bounded traversal).
///
/// Returns the node count or `MAX_SUBST_NODES + 1` if the limit is exceeded,
/// to allow early termination.
fn term_size(term: &Term) -> usize {
    fn go(term: &Term, acc: &mut usize) {
        *acc += 1;
        if *acc > MAX_SUBST_NODES {
            return;
        }
        match term {
            Term::Var { .. } | Term::Sort(_) | Term::Constant(_) => {}
            Term::Lambda { domain, body, .. } => {
                go(domain, acc);
                go(body, acc);
            }
            Term::Pi {
                domain, codomain, ..
            } => {
                go(domain, acc);
                go(codomain, acc);
            }
            Term::App { func, arg } => {
                go(func, acc);
                go(arg, acc);
            }
            Term::Annot { term: t, ty } => {
                go(t, acc);
                go(ty, acc);
            }
            Term::Let {
                ty, val, body, ..
            } => {
                go(ty, acc);
                go(val, acc);
                go(body, acc);
            }
            // Non-admissible terms count as 1 node (already counted above).
            _ => {}
        }
    }
    let mut count = 0;
    go(term, &mut count);
    count
}

// ---------------------------------------------------------------------------
// Weak-head normal form (WHNF) reduction
// ---------------------------------------------------------------------------

/// Reduce a term to weak-head normal form.
///
/// Applies beta-reduction (lambda application) and zeta-reduction (let
/// unfolding) at the head only.
///
/// `fuel` is a shared counter decremented on each beta/zeta step. When it
/// reaches zero, `TypeError::ReductionLimitExceeded` is returned. This
/// prevents wide computation (many sequential reductions at shallow depth)
/// and is complementary to the `depth` limit which prevents deep recursion.
fn whnf(term: &Term, depth: usize, fuel: &mut usize) -> Result<Term, TypeError> {
    if depth > MAX_DEPTH {
        return Err(TypeError::RecursionLimitExceeded);
    }
    match term {
        Term::App { func, arg } => {
            let f = whnf(func, depth + 1, fuel)?;
            match f {
                Term::Lambda { body, .. } => {
                    // Beta-reduction step — consume fuel.
                    *fuel = fuel
                        .checked_sub(1)
                        .ok_or(TypeError::ReductionLimitExceeded)?;
                    let result = subst(&body, 0, arg, depth + 1)?;
                    // Guard against substitution blowup before continuing.
                    let size = term_size(&result);
                    if size > MAX_SUBST_NODES {
                        return Err(TypeError::SubstitutionBlowup { node_count: size });
                    }
                    whnf(&result, depth + 1, fuel)
                }
                _ => Ok(Term::App {
                    func: Box::new(f),
                    arg: arg.clone(),
                }),
            }
        }
        Term::Let { val, body, .. } => {
            // Zeta-reduction step — consume fuel.
            *fuel = fuel
                .checked_sub(1)
                .ok_or(TypeError::ReductionLimitExceeded)?;
            let result = subst(body, 0, val, depth + 1)?;
            // Guard against substitution blowup before continuing.
            let size = term_size(&result);
            if size > MAX_SUBST_NODES {
                return Err(TypeError::SubstitutionBlowup { node_count: size });
            }
            whnf(&result, depth + 1, fuel)
        }
        Term::Annot { term: t, .. } => whnf(t, depth + 1, fuel),
        _ => Ok(term.clone()),
    }
}

// ---------------------------------------------------------------------------
// Effect row normalization for conversion checking
// ---------------------------------------------------------------------------

/// Collect every concrete [`Effect`] from an [`EffectRow`] by flattening `Join`
/// nodes and treating `Empty` / `Effects([])` as zero-contribution. Returns
/// `None` if a row variable is encountered (row variables block normalization
/// to a concrete set).
fn collect_effects(
    row: &EffectRow,
    branch_sensitive: bool,
) -> Option<(Vec<crate::ast::Effect>, bool)> {
    match row {
        EffectRow::Empty => Some((Vec::new(), branch_sensitive)),
        EffectRow::Effects(effs) => Some((effs.clone(), branch_sensitive)),
        EffectRow::Var(_) => None,
        EffectRow::Join(lhs, rhs) => {
            let (mut left, lbs) = collect_effects(lhs, false)?;
            let (right, rbs) = collect_effects(rhs, false)?;
            left.extend(right);
            Some((left, branch_sensitive || lbs || rbs))
        }
        EffectRow::BranchSensitive(inner) => collect_effects(inner, true),
    }
}

/// Normalize an effect list into canonical sorted, deduplicated form.
fn canonicalize_effects(mut effects: Vec<crate::ast::Effect>) -> Vec<crate::ast::Effect> {
    effects.sort_by(|a, b| format!("{:?}", a).cmp(&format!("{:?}", b)));
    effects.dedup();
    effects
}

/// Compare two optional effect rows for semantic equality.
///
/// Fixes false negatives from structural `PartialEq`:
/// - `None` ≡ `Some(EffectRow::Empty)` — both mean "pure"
/// - `Some(EffectRow::Effects([]))` ≡ `None` — empty effects list is pure
/// - `Join(Empty, Effects([Read]))` ≡ `Effects([Read])` — join with empty is identity
/// - `Join(Effects([Read]), Effects([Write(s)]))` ≡ `Effects([Read, Write(s)])` — flattening
fn effect_row_eq(a: &Option<EffectRow>, b: &Option<EffectRow>) -> bool {
    // Fast path: structural equality covers the common case.
    if a == b {
        return true;
    }

    let norm_a = match a {
        None => Some((Vec::new(), false)),
        Some(row) => collect_effects(row, false),
    };
    let norm_b = match b {
        None => Some((Vec::new(), false)),
        Some(row) => collect_effects(row, false),
    };

    match (norm_a, norm_b) {
        (Some((ea, bsa)), Some((eb, bsb))) => {
            bsa == bsb && canonicalize_effects(ea) == canonicalize_effects(eb)
        }
        // Row variable on either side: cannot normalize, structural comparison
        // already failed above.
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Conversion checking (definitional equality)
// ---------------------------------------------------------------------------

/// Check whether two terms are definitionally equal.
///
/// Reduces both to WHNF and compares structurally. For De Bruijn-indexed
/// terms, structural equality IS alpha-equivalence. Binder names are ignored.
fn conv_eq(a: &Term, b: &Term, depth: usize, fuel: &mut usize) -> Result<bool, TypeError> {
    if depth > MAX_DEPTH {
        return Err(TypeError::RecursionLimitExceeded);
    }
    let a_whnf = whnf(a, depth + 1, fuel)?;
    let b_whnf = whnf(b, depth + 1, fuel)?;
    match (&a_whnf, &b_whnf) {
        (Term::Var { index: i, .. }, Term::Var { index: j, .. }) => Ok(i == j),
        (Term::Constant(c1), Term::Constant(c2)) => Ok(c1 == c2),
        (Term::Sort(s1), Term::Sort(s2)) => Ok(sort_eq(s1, s2)),
        (
            Term::Pi {
                domain: d1,
                codomain: c1,
                effect_row: e1,
                ..
            },
            Term::Pi {
                domain: d2,
                codomain: c2,
                effect_row: e2,
                ..
            },
        ) => Ok(conv_eq(d1, d2, depth + 1, fuel)?
            && conv_eq(c1, c2, depth + 1, fuel)?
            && effect_row_eq(e1, e2)),
        (
            Term::Lambda {
                domain: p1,
                body: b1,
                ..
            },
            Term::Lambda {
                domain: p2,
                body: b2,
                ..
            },
        ) => Ok(conv_eq(p1, p2, depth + 1, fuel)? && conv_eq(b1, b2, depth + 1, fuel)?),
        (
            Term::App {
                func: f1, arg: a1, ..
            },
            Term::App {
                func: f2, arg: a2, ..
            },
        ) => Ok(conv_eq(f1, f2, depth + 1, fuel)? && conv_eq(a1, a2, depth + 1, fuel)?),
        _ => Ok(false),
    }
}

/// Compare two `Sort` values for equality.
fn sort_eq(a: &Sort, b: &Sort) -> bool {
    match (a, b) {
        (Sort::Type(la), Sort::Type(lb)) => level_eq(la, lb),
        (Sort::Prop, Sort::Prop) => true,
        (Sort::Rule(la), Sort::Rule(lb)) => level_eq(la, lb),
        _ => false,
    }
}

/// Compare two `Level` expressions for equality (by evaluation when possible).
fn level_eq(a: &Level, b: &Level) -> bool {
    match (eval_level(a), eval_level(b)) {
        (Some(va), Some(vb)) => va == vb,
        _ => a == b,
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Ensure `ty` reduces to a `Sort` and return the level as `u64`.
fn ensure_sort(ty: &Term, depth: usize, fuel: &mut usize) -> Result<u64, TypeError> {
    let n = whnf(ty, depth, fuel)?;
    match &n {
        Term::Sort(Sort::Type(level)) => eval_level(level).ok_or_else(|| TypeError::NotASort {
            term: ty.clone(),
            found: n.clone(),
        }),
        Term::Sort(Sort::Prop) => Ok(0),
        Term::Sort(Sort::Rule(level)) => eval_level(level).ok_or_else(|| TypeError::NotASort {
            term: ty.clone(),
            found: n.clone(),
        }),
        _ => Err(TypeError::NotASort {
            term: ty.clone(),
            found: n,
        }),
    }
}

/// Ensure `ty` reduces to a pure `Pi` and return (domain, codomain).
fn ensure_pi(ty: &Term, depth: usize, fuel: &mut usize) -> Result<(Term, Term), TypeError> {
    let n = whnf(ty, depth, fuel)?;
    match n {
        Term::Pi {
            domain, codomain, ..
        } => Ok((*domain, *codomain)),
        _ => Err(TypeError::NotAFunction {
            term: ty.clone(),
            found_type: n,
        }),
    }
}

/// Make a `Sort::Type(Level::Nat(n))` term.
fn type_level(n: u64) -> Term {
    Term::Sort(Sort::Type(Level::Nat(n)))
}

// ---------------------------------------------------------------------------
// Admissibility checker
// ---------------------------------------------------------------------------

/// Check that `term` is in the admissible fragment.
///
/// Returns `Ok(())` if admissible, or `Err(TypeError::Admissibility)` with
/// the specific violation.
pub fn check_admissibility(term: &Term) -> Result<(), TypeError> {
    check_admissibility_inner(term, 0)
}

fn check_admissibility_inner(term: &Term, depth: usize) -> Result<(), TypeError> {
    if depth > MAX_DEPTH {
        return Err(TypeError::RecursionLimitExceeded);
    }
    match term {
        Term::Var { .. } => Ok(()),

        Term::Sort(sort) => {
            let level = match sort {
                Sort::Type(level) | Sort::Rule(level) => level,
                Sort::Prop | Sort::Time0 | Sort::Time1 => return Ok(()),
            };
            if let Some(var_idx) = find_level_var(level) {
                return Err(TypeError::Admissibility {
                    violation: AdmissibilityViolation::UnresolvedLevelVar(var_idx),
                    term: term.clone(),
                });
            }
            Ok(())
        }

        Term::Lambda { domain, body, .. } => {
            check_admissibility_inner(domain, depth + 1)?;
            check_admissibility_inner(body, depth + 1)
        }

        Term::Pi {
            domain,
            effect_row,
            codomain,
            ..
        } => {
            if let Some(row) = effect_row {
                if !matches!(row, EffectRow::Empty) {
                    return Err(TypeError::Admissibility {
                        violation: AdmissibilityViolation::EffectfulPiNotSupported,
                        term: term.clone(),
                    });
                }
            }
            check_admissibility_inner(domain, depth + 1)?;
            check_admissibility_inner(codomain, depth + 1)
        }

        Term::App { func, arg } => {
            check_admissibility_inner(func, depth + 1)?;
            check_admissibility_inner(arg, depth + 1)
        }

        Term::Annot { term: t, ty } => {
            check_admissibility_inner(t, depth + 1)?;
            check_admissibility_inner(ty, depth + 1)
        }

        Term::Let { ty, val, body, .. } => {
            check_admissibility_inner(ty, depth + 1)?;
            check_admissibility_inner(val, depth + 1)?;
            check_admissibility_inner(body, depth + 1)
        }

        // -- Non-admissible forms --
        Term::Rec { .. } => Err(TypeError::Admissibility {
            violation: AdmissibilityViolation::RecNotSupported,
            term: term.clone(),
        }),
        Term::Hole(_) => Err(TypeError::Admissibility {
            violation: AdmissibilityViolation::UnfilledHole,
            term: term.clone(),
        }),
        Term::Sigma { .. } => Err(TypeError::Admissibility {
            violation: AdmissibilityViolation::SigmaNotSupported,
            term: term.clone(),
        }),
        Term::Match {
            scrutinee,
            return_ty,
            branches,
        } => {
            // Step 1 — every constructor pattern must be a prelude
            // constructor; wildcards are allowed unconditionally.
            for branch in branches {
                match &branch.pattern {
                    Pattern::Wildcard => {}
                    Pattern::Constructor { constructor, .. } => {
                        let ctor_name = constructor.name.segments.join(".");
                        if !is_prelude_constructor(&ctor_name) {
                            return Err(TypeError::Admissibility {
                                violation: AdmissibilityViolation::MatchOnNonPreludeType {
                                    constructor_name: ctor_name,
                                },
                                term: term.clone(),
                            });
                        }
                    }
                }
            }

            // Step 2 — infer the scrutinee's datatype. The admissibility
            // check is lightweight (it runs without a typing context), so
            // scrutinee-datatype inference uses a narrow set of syntactic
            // rules that cover the admissible fragment:
            //
            //   - `Term::Constant(name)` where `name` is itself a prelude
            //     type (e.g. `Nat`): the datatype is that name;
            //   - `Term::Constant(name)` where `name` is a prelude
            //     constructor (e.g. `Zero`): the datatype is the type the
            //     constructor belongs to;
            //   - otherwise, resolution falls back to the branch
            //     constructors — if every constructor pattern belongs to
            //     the same datatype, that datatype is used.
            //
            // The last fallback keeps the match-on-wildcard-only form
            // admissible without requiring a typing context.
            let scrutinee_datatype =
                resolve_match_scrutinee_datatype(scrutinee, branches);

            let datatype = match scrutinee_datatype {
                Some(dt) => dt,
                None => {
                    // If every branch is a wildcard we can't pin the
                    // datatype, but the match is still exhaustive — accept
                    // without coverage checks.
                    if branches
                        .iter()
                        .all(|b| matches!(b.pattern, Pattern::Wildcard))
                    {
                        check_admissibility_inner(scrutinee, depth + 1)?;
                        check_admissibility_inner(return_ty, depth + 1)?;
                        for branch in branches {
                            check_admissibility_inner(&branch.body, depth + 1)?;
                        }
                        return Ok(());
                    }
                    return Err(TypeError::Admissibility {
                        violation: AdmissibilityViolation::MatchScrutineeDatatypeUnresolved,
                        term: term.clone(),
                    });
                }
            };

            // Step 3 — every constructor pattern must belong to the
            // scrutinee's datatype.
            let expected_constructors =
                crate::prelude::PreludeRegistry::lookup_variant_constructors(&datatype)
                    .unwrap_or_default();
            for branch in branches {
                if let Pattern::Constructor { constructor, .. } = &branch.pattern {
                    let ctor_name = constructor.name.segments.join(".");
                    if !expected_constructors.iter().any(|c| *c == ctor_name) {
                        let actual_datatype =
                            crate::prelude::PreludeRegistry::constructor_datatype(&ctor_name)
                                .map(str::to_string);
                        return Err(TypeError::Admissibility {
                            violation:
                                AdmissibilityViolation::MatchBranchConstructorMismatch {
                                    scrutinee_datatype: datatype.clone(),
                                    branch_constructor: ctor_name,
                                    branch_constructor_datatype: actual_datatype,
                                },
                            term: term.clone(),
                        });
                    }
                }
            }

            // Step 4 — coverage: full finite coverage OR a wildcard branch.
            let has_wildcard = branches
                .iter()
                .any(|b| matches!(b.pattern, Pattern::Wildcard));
            if !has_wildcard {
                let covered: std::collections::BTreeSet<String> = branches
                    .iter()
                    .filter_map(|b| match &b.pattern {
                        Pattern::Constructor { constructor, .. } => {
                            Some(constructor.name.segments.join("."))
                        }
                        Pattern::Wildcard => None,
                    })
                    .collect();
                let missing: Vec<String> = expected_constructors
                    .iter()
                    .filter(|c| !covered.contains(**c))
                    .map(|c| (*c).to_string())
                    .collect();
                if !missing.is_empty() {
                    return Err(TypeError::Admissibility {
                        violation: AdmissibilityViolation::MatchNonExhaustive {
                            scrutinee_datatype: datatype.clone(),
                            missing_constructors: missing,
                        },
                        term: term.clone(),
                    });
                }
            }

            // Recursively check scrutinee, return type, and branch bodies.
            check_admissibility_inner(scrutinee, depth + 1)?;
            check_admissibility_inner(return_ty, depth + 1)?;
            for branch in branches {
                check_admissibility_inner(&branch.body, depth + 1)?;
            }
            Ok(())
        }
        Term::Pair { .. } => Err(TypeError::Admissibility {
            violation: AdmissibilityViolation::PairNotSupported,
            term: term.clone(),
        }),
        Term::Proj { .. } => Err(TypeError::Admissibility {
            violation: AdmissibilityViolation::ProjectionNotSupported,
            term: term.clone(),
        }),
        Term::Constant(_) => Ok(()),
        Term::AxiomUse { .. } => Err(TypeError::Admissibility {
            violation: AdmissibilityViolation::AxiomNotSupported,
            term: term.clone(),
        }),
        Term::InductiveIntro { .. } => Err(TypeError::Admissibility {
            violation: AdmissibilityViolation::InductiveIntroNotSupported,
            term: term.clone(),
        }),
        Term::HoleFill { .. } => Err(TypeError::Admissibility {
            violation: AdmissibilityViolation::HoleFillNotSupported,
            term: term.clone(),
        }),
        Term::Defeasible(rule) => {
            check_admissibility_inner(&rule.base_ty, depth + 1)?;
            check_admissibility_inner(&rule.base_body, depth + 1)?;
            for exception in &rule.exceptions {
                check_admissibility_inner(&exception.guard, depth + 1)?;
                check_admissibility_inner(&exception.body, depth + 1)?;
            }
            Ok(())
        }
        Term::DefeatElim { .. } => Err(TypeError::Admissibility {
            violation: AdmissibilityViolation::DefeatElimNotSupported,
            term: term.clone(),
        }),
        Term::ModalAt { .. }
        | Term::ModalEventually { .. }
        | Term::ModalAlways { .. }
        | Term::ModalIntro { .. }
        | Term::ModalElim { .. } => Err(TypeError::Admissibility {
            violation: AdmissibilityViolation::ModalNotSupported,
            term: term.clone(),
        }),
        Term::SanctionsDominance { .. } => Err(TypeError::Admissibility {
            violation: AdmissibilityViolation::SanctionsDominanceNotSupported,
            term: term.clone(),
        }),
        Term::PrincipleBalance(_) => Err(TypeError::Admissibility {
            violation: AdmissibilityViolation::PrincipleBalanceNotSupported,
            term: term.clone(),
        }),
        Term::Unlock { .. } => Err(TypeError::Admissibility {
            violation: AdmissibilityViolation::UnlockNotSupported,
            term: term.clone(),
        }),
        Term::Lift0 { .. } | Term::Derive1 { .. } => Err(TypeError::Admissibility {
            violation: AdmissibilityViolation::TemporalCoercionNotSupported,
            term: term.clone(),
        }),
        Term::ContentRefTerm(_) => Err(TypeError::Admissibility {
            violation: AdmissibilityViolation::ContentRefNotSupported,
            term: term.clone(),
        }),
        Term::IntLit(_) | Term::RatLit(_, _) | Term::StringLit(_) => {
            Err(TypeError::Admissibility {
                violation: AdmissibilityViolation::LiteralNotSupported,
                term: term.clone(),
            })
        }
    }
}

/// Resolve the datatype of a match scrutinee for the admissibility check.
///
/// The admissibility check does not run full type inference, so the
/// scrutinee's datatype is recovered syntactically:
///
///   1. If `scrutinee` is `Term::Constant(name)` and `name` is itself a
///      prelude type (e.g. `"Nat"`), the datatype is `name`.
///   2. If `scrutinee` is `Term::Constant(name)` and `name` is a prelude
///      constructor (e.g. `"Compliant"`), the datatype is the one that
///      constructor belongs to (e.g. `"ComplianceVerdict"`).
///   3. Otherwise, if every constructor pattern across `branches` belongs
///      to the same prelude datatype, that datatype is returned.
///
/// Returns `None` if none of those rules fire (e.g. opaque variable
/// scrutinee with only-wildcard branches); the caller decides how to
/// handle that case.
fn resolve_match_scrutinee_datatype(
    scrutinee: &Term,
    branches: &[crate::ast::Branch],
) -> Option<String> {
    use crate::prelude::{is_prelude_type, PreludeRegistry};

    // Rule 1 and 2: the scrutinee is a Constant.
    if let Term::Constant(q) = scrutinee {
        let name = q.segments.join(".");
        if is_prelude_type(&name) {
            return Some(name);
        }
        if let Some(dt) = PreludeRegistry::constructor_datatype(&name) {
            return Some(dt.to_string());
        }
    }

    // Rule 3: every constructor pattern shares a datatype.
    let mut shared: Option<&'static str> = None;
    for branch in branches {
        if let Pattern::Constructor { constructor, .. } = &branch.pattern {
            let ctor_name = constructor.name.segments.join(".");
            let dt = PreludeRegistry::constructor_datatype(&ctor_name)?;
            match shared {
                None => shared = Some(dt),
                Some(prev) if prev == dt => {}
                Some(_) => return None,
            }
        }
    }
    shared.map(str::to_string)
}

// ---------------------------------------------------------------------------
// Bidirectional type checker
// ---------------------------------------------------------------------------

/// **Inference mode** -- synthesize the type of `term` under context `ctx`.
///
/// # Rules
///
/// | Term | Rule |
/// |------|------|
/// | `Var(i)` | Look up index `i` in Gamma |
/// | `Constant(c)` | Look up global constant `c` in the signature |
/// | `Sort(Type_l)` | `Type_l : Type_{l+1}` |
/// | `Sort(Prop)` | `Prop : Type_1` |
/// | `Sort(Rule_l)` | `Rule_l : Type_{l+1}` |
/// | `Pi(A, B)` | Infer sorts of `A` and `B`, return `Type_{max(i,j)}` |
/// | `App(f, a)` | Infer `Pi(x:A).B` for `f`, check `a : A`, return `B[a/x]` |
/// | `Annot(e, t)` | Check `e : t`, return `t` |
/// | `Let(A, e, b)` | Check `e : A`, infer `b` under extension, subst out |
/// | `Defeasible(r)` | Check `base_body : base_ty`, check exception bodies, return `base_ty` |
/// | `Lambda` | Cannot infer -- requires annotation |
pub fn infer(ctx: &Context, term: &Term) -> Result<Term, TypeError> {
    let mut fuel = MAX_WHNF_FUEL;
    infer_inner(ctx, term, 0, &mut fuel)
}

/// Inner inference with shared fuel counter and depth tracking.
fn infer_inner(ctx: &Context, term: &Term, depth: usize, fuel: &mut usize) -> Result<Term, TypeError> {
    if depth > MAX_DEPTH {
        return Err(TypeError::RecursionLimitExceeded);
    }
    check_admissibility(term)?;

    match term {
        // -- Var --
        Term::Var { name, index } => {
            ctx.lookup(*index)
                .cloned()
                .ok_or_else(|| TypeError::UnboundVar {
                    name: name.name.clone(),
                    index: *index,
                    ctx_len: ctx.len(),
                })
        }

        // -- Constant --
        Term::Constant(name) => {
            ctx.lookup_constant(name)
                .cloned()
                .ok_or_else(|| TypeError::Admissibility {
                    violation: AdmissibilityViolation::ConstantNotSupported,
                    term: term.clone(),
                })
        }

        // -- Sort --
        Term::Sort(sort) => match sort {
            Sort::Type(level) => {
                let n = eval_level(level).ok_or(TypeError::LevelOverflow)?;
                let succ = n.checked_add(1).ok_or(TypeError::LevelOverflow)?;
                Ok(type_level(succ))
            }
            Sort::Prop => Ok(type_level(1)),
            Sort::Rule(level) => {
                let n = eval_level(level).ok_or(TypeError::LevelOverflow)?;
                let succ = n.checked_add(1).ok_or(TypeError::LevelOverflow)?;
                Ok(type_level(succ))
            }
            Sort::Time0 | Sort::Time1 => Ok(type_level(0)),
        },

        Term::IntLit(_) | Term::RatLit(_, _) | Term::StringLit(_) => {
            Err(TypeError::Admissibility {
                violation: AdmissibilityViolation::LiteralNotSupported,
                term: term.clone(),
            })
        }

        // -- Pi --
        Term::Pi {
            domain, codomain, ..
        } => {
            let i = infer_sort(ctx, domain, depth + 1, fuel)?;
            let ext_ctx = ctx.extend((**domain).clone());
            let j = infer_sort(&ext_ctx, codomain, depth + 1, fuel)?;
            Ok(type_level(i.max(j)))
        }

        // -- App --
        Term::App { func, arg } => {
            let func_ty = infer_inner(ctx, func, depth + 1, fuel)?;
            let (domain, codomain) = ensure_pi(&func_ty, depth + 1, fuel)?;
            check_inner(ctx, arg, &domain, depth + 1, fuel)?;
            subst(&codomain, 0, arg, depth + 1)
        }

        // -- Annot --
        Term::Annot { term: inner, ty } => {
            let _ = infer_sort(ctx, ty, depth + 1, fuel)?;
            check_inner(ctx, inner, ty, depth + 1, fuel)?;
            Ok((**ty).clone())
        }

        // -- Let --
        Term::Let { ty, val, body, .. } => {
            let _ = infer_sort(ctx, ty, depth + 1, fuel)?;
            check_inner(ctx, val, ty, depth + 1, fuel)?;
            let ext_ctx = ctx.extend((**ty).clone());
            let body_ty = infer_inner(&ext_ctx, body, depth + 1, fuel)?;
            subst(&body_ty, 0, val, depth + 1)
        }

        // -- Defeasible --
        // A defeasible rule has the same type as its base_ty annotation.
        // We verify that base_ty is a valid type (inhabits some sort),
        // then check that base_body inhabits base_ty, and that each
        // exception body also inhabits base_ty.
        Term::Defeasible(rule) => {
            let _ = infer_sort(ctx, &rule.base_ty, depth + 1, fuel)?;
            check_inner(ctx, &rule.base_body, &rule.base_ty, depth + 1, fuel)?;
            for exception in &rule.exceptions {
                // Guards must be propositions (inhabit some sort).
                let _ = infer_inner(ctx, &exception.guard, depth + 1, fuel)?;
                check_inner(ctx, &exception.body, &rule.base_ty, depth + 1, fuel)?;
            }
            Ok((*rule.base_ty).clone())
        }

        // -- Match on prelude types --
        // Admissibility already verified that all patterns are prelude
        // constructors or wildcards.  The return_ty (motive) gives the
        // result type.  We verify the scrutinee type-checks, then check
        // each branch body against the return type.
        Term::Match {
            scrutinee,
            return_ty,
            branches,
        } => {
            // Scrutinee must be well-typed.
            let _scrutinee_ty = infer_inner(ctx, scrutinee, depth + 1, fuel)?;
            // Return type must inhabit a sort.
            let _ = infer_sort(ctx, return_ty, depth + 1, fuel)?;
            // Each branch body must check against the return type.
            for branch in branches {
                // For Constructor patterns with binders, we would need to
                // extend the context with the binder types.  Prelude
                // constructors are nullary (zero binders), so no context
                // extension is needed.  Wildcard patterns also bind nothing.
                check_inner(ctx, &branch.body, return_ty, depth + 1, fuel)?;
            }
            Ok((**return_ty).clone())
        }

        // -- Lambda --
        Term::Lambda { .. } => Err(TypeError::CannotInfer { term: term.clone() }),

        // All other forms rejected by admissibility (unreachable after
        // the check_admissibility call at the top of this function).
        _ => Err(TypeError::Admissibility {
            violation: AdmissibilityViolation::RecNotSupported,
            term: term.clone(),
        }),
    }
}

/// **Checking mode** -- verify that `term` has type `expected_type` under `ctx`.
pub fn check(ctx: &Context, term: &Term, expected_type: &Term) -> Result<(), TypeError> {
    let mut fuel = MAX_WHNF_FUEL;
    check_inner(ctx, term, expected_type, 0, &mut fuel)
}

/// Inner checking with shared fuel counter and depth tracking.
fn check_inner(
    ctx: &Context,
    term: &Term,
    expected_type: &Term,
    depth: usize,
    fuel: &mut usize,
) -> Result<(), TypeError> {
    if depth > MAX_DEPTH {
        return Err(TypeError::RecursionLimitExceeded);
    }
    check_admissibility(term)?;

    match term {
        // -- Lambda (checking mode) --
        Term::Lambda { domain, body, .. } => {
            let (pi_domain, codomain) =
                ensure_pi(expected_type, depth, fuel).map_err(|_| TypeError::Mismatch {
                    ctx_len: ctx.len(),
                    term: term.clone(),
                    expected: expected_type.clone(),
                    found: term.clone(),
                })?;

            if !conv_eq(domain, &pi_domain, depth, fuel)? {
                return Err(TypeError::Mismatch {
                    ctx_len: ctx.len(),
                    term: (**domain).clone(),
                    expected: pi_domain,
                    found: (**domain).clone(),
                });
            }

            let ext_ctx = ctx.extend(pi_domain);
            check_inner(&ext_ctx, body, &codomain, depth + 1, fuel)
        }

        // -- Fallback: infer then compare --
        _ => {
            let inferred = infer_inner(ctx, term, depth, fuel)?;
            if conv_eq(&inferred, expected_type, depth, fuel)? {
                Ok(())
            } else {
                Err(TypeError::Mismatch {
                    ctx_len: ctx.len(),
                    term: term.clone(),
                    expected: expected_type.clone(),
                    found: inferred,
                })
            }
        }
    }
}

/// Inner sort inference with shared fuel counter and depth tracking.
fn infer_sort(ctx: &Context, term: &Term, depth: usize, fuel: &mut usize) -> Result<u64, TypeError> {
    let ty = infer_inner(ctx, term, depth, fuel)?;
    ensure_sort(&ty, depth, fuel)
}

// ---------------------------------------------------------------------------
// Combined entry points
// ---------------------------------------------------------------------------

/// Check admissibility, then infer the type.
pub fn infer_admissible(ctx: &Context, term: &Term) -> Result<Term, TypeError> {
    infer(ctx, term)
}

/// Check admissibility, then check against expected type.
pub fn check_admissible(ctx: &Context, term: &Term, expected_type: &Term) -> Result<(), TypeError> {
    check(ctx, term, expected_type)
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{
        AuthorityRef, Branch, Constructor, DefeasibleRule, Effect, EffectRow, Exception,
        Hole as AstHole, Ident, Level, LevelVar, Pattern, QualIdent, Sort, Term,
    };

    /// Test helper: call `conv_eq` with fresh fuel.
    fn test_conv_eq(a: &Term, b: &Term) -> bool {
        let mut fuel = MAX_WHNF_FUEL;
        conv_eq(a, b, 0, &mut fuel).expect("conv_eq should not fail in tests")
    }

    /// Test helper: call `whnf` with fresh fuel.
    fn test_whnf(term: &Term) -> Term {
        let mut fuel = MAX_WHNF_FUEL;
        whnf(term, 0, &mut fuel).expect("whnf should not fail in tests")
    }

    /// `Type_0`
    fn type0() -> Term {
        Term::Sort(Sort::Type(Level::Nat(0)))
    }

    /// `Type_1`
    fn type1() -> Term {
        Term::Sort(Sort::Type(Level::Nat(1)))
    }

    /// `Type_2`
    fn type2() -> Term {
        Term::Sort(Sort::Type(Level::Nat(2)))
    }

    /// Variable at De Bruijn index `i`.
    fn var(i: u32) -> Term {
        Term::Var {
            name: Ident::new(&format!("v{}", i)),
            index: i,
        }
    }

    /// `Pi(x : A). B` (pure)
    fn pi(domain: Term, codomain: Term) -> Term {
        Term::Pi {
            binder: Ident::new("_"),
            domain: Box::new(domain),
            effect_row: None,
            codomain: Box::new(codomain),
        }
    }

    /// `lam(x : A). b`
    fn lam(param_type: Term, body: Term) -> Term {
        Term::Lambda {
            binder: Ident::new("x"),
            domain: Box::new(param_type),
            body: Box::new(body),
        }
    }

    /// `f a`
    fn app(func: Term, arg: Term) -> Term {
        Term::App {
            func: Box::new(func),
            arg: Box::new(arg),
        }
    }

    /// `(e : t)`
    fn annot(term: Term, ty: Term) -> Term {
        Term::Annot {
            term: Box::new(term),
            ty: Box::new(ty),
        }
    }

    /// `let x : A := e in b`
    fn let_(def_type: Term, def_val: Term, body: Term) -> Term {
        Term::Let {
            binder: Ident::new("x"),
            ty: Box::new(def_type),
            val: Box::new(def_val),
            body: Box::new(body),
        }
    }

    // -- 1. Sort hierarchy: Type_0 : Type_1 --

    #[test]
    fn sort_hierarchy_type0_has_type_type1() {
        let ctx = Context::empty();
        let ty = infer(&ctx, &type0()).unwrap();
        assert!(test_conv_eq(&ty, &type1()));
    }

    #[test]
    fn sort_hierarchy_type1_has_type_type2() {
        let ctx = Context::empty();
        let ty = infer(&ctx, &type1()).unwrap();
        assert!(test_conv_eq(&ty, &type2()));
    }

    // -- 2. Pi formation --

    #[test]
    fn pi_formation_same_level() {
        let ctx = Context::empty();
        let term = pi(type0(), type0());
        let ty = infer(&ctx, &term).unwrap();
        assert!(test_conv_eq(&ty, &type1()));
    }

    #[test]
    fn pi_formation_max_level() {
        let ctx = Context::empty();
        let term = pi(type1(), type0());
        let ty = infer(&ctx, &term).unwrap();
        assert!(test_conv_eq(&ty, &type2()));
    }

    // -- 3. Identity function --

    #[test]
    fn identity_function_checks() {
        let ctx = Context::empty();
        let id = lam(type0(), var(0));
        let id_type = pi(type0(), type0());
        check(&ctx, &id, &id_type).unwrap();
    }

    // -- 4. Constant function --

    #[test]
    fn constant_function_checks() {
        let ctx = Context::empty();
        let inner_lam = lam(type0(), var(1));
        let const_fn = lam(type0(), inner_lam);
        let const_type = pi(type0(), pi(type0(), type0()));
        check(&ctx, &const_fn, &const_type).unwrap();
    }

    // -- 5. Application type --

    #[test]
    fn application_type_inferred() {
        let ctx = Context::empty();
        let id = lam(type1(), var(0));
        let id_type = pi(type1(), type1());
        let f = annot(id, id_type);
        let application = app(f, type0());
        let ty = infer(&ctx, &application).unwrap();
        assert!(test_conv_eq(&ty, &type1()));
    }

    // -- 6. Let binding type --

    #[test]
    fn let_binding_infers_correctly() {
        let ctx = Context::empty();
        let term = let_(type1(), type0(), var(0));
        let ty = infer(&ctx, &term).unwrap();
        assert!(test_conv_eq(&ty, &type1()));
    }

    // -- 7. Ill-typed application rejected --

    #[test]
    fn ill_typed_application_rejected() {
        let ctx = Context::empty();
        let id = lam(type0(), var(0));
        let id_type = pi(type0(), type0());
        let f = annot(id, id_type);
        let bad_arg = pi(type0(), type0());
        let application = app(f, bad_arg);
        let result = infer(&ctx, &application);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::Mismatch { .. } => {}
            other => panic!("expected Mismatch, got: {:?}", other),
        }
    }

    // -- 8. Unbound variable rejected --

    #[test]
    fn unbound_variable_rejected() {
        let ctx = Context::empty();
        let result = infer(&ctx, &var(0));
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::UnboundVar {
                index: 0,
                ctx_len: 0,
                ..
            } => {}
            other => panic!("expected UnboundVar, got: {:?}", other),
        }
    }

    #[test]
    fn unbound_variable_in_nonempty_context() {
        let ctx = Context::empty().extend(type0());
        let result = infer(&ctx, &var(1));
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::UnboundVar {
                index: 1,
                ctx_len: 1,
                ..
            } => {}
            other => panic!("expected UnboundVar, got: {:?}", other),
        }
    }

    // -- 9. Universe level mismatch rejected --

    #[test]
    fn universe_level_mismatch_rejected() {
        let ctx = Context::empty();
        let result = check(&ctx, &type1(), &type1());
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::Mismatch {
                expected, found, ..
            } => {
                assert!(test_conv_eq(&expected, &type1()));
                assert!(test_conv_eq(&found, &type2()));
            }
            other => panic!("expected Mismatch, got: {:?}", other),
        }
    }

    // -- 10. Lambda without Pi target rejected --

    #[test]
    fn lambda_checked_against_non_pi_rejected() {
        let ctx = Context::empty();
        let id = lam(type0(), var(0));
        let result = check(&ctx, &id, &type0());
        assert!(result.is_err());
    }

    // -- 11. Bare lambda cannot be inferred --

    #[test]
    fn bare_lambda_cannot_be_inferred() {
        let ctx = Context::empty();
        let id = lam(type0(), var(0));
        let result = infer(&ctx, &id);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::CannotInfer { .. } => {}
            other => panic!("expected CannotInfer, got: {:?}", other),
        }
    }

    // -- 12. Annotation enables inference of lambda --

    #[test]
    fn annotation_enables_lambda_inference() {
        let ctx = Context::empty();
        let id = lam(type0(), var(0));
        let id_type = pi(type0(), type0());
        let annotated = annot(id, id_type.clone());
        let ty = infer(&ctx, &annotated).unwrap();
        assert!(test_conv_eq(&ty, &id_type));
    }

    // -- 13. Conversion via beta reduction --

    #[test]
    fn conversion_via_beta_reduction() {
        let reduced = test_whnf(&app(lam(type0(), var(0)), type0()));
        assert!(test_conv_eq(&reduced, &type0()));
    }

    // -- 14. Nested Pi types --

    #[test]
    fn nested_pi_types_infer_correctly() {
        let ctx = Context::empty();
        let inner = pi(var(1), var(1));
        let mid = pi(type0(), inner);
        let outer = pi(type0(), mid);
        let ty = infer(&ctx, &outer).unwrap();
        assert!(test_conv_eq(&ty, &type1()));
    }

    // -- 15. Rec (fix) rejected by admissibility --

    #[test]
    fn rec_rejected_by_admissibility() {
        let ctx = Context::empty();
        let rec_term = Term::Rec {
            binder: Ident::new("f"),
            ty: Box::new(type0()),
            body: Box::new(var(0)),
        };
        let result = infer(&ctx, &rec_term);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::Admissibility {
                violation: AdmissibilityViolation::RecNotSupported,
                ..
            } => {}
            other => panic!("expected RecNotSupported, got: {:?}", other),
        }
    }

    // -- 16. Hole rejected by admissibility --

    #[test]
    fn hole_rejected_by_admissibility() {
        let ctx = Context::empty();
        let hole = Term::Hole(AstHole {
            name: Some(Ident::new("h")),
            ty: Box::new(type0()),
            authority: AuthorityRef::Named(QualIdent::simple("authority.test")),
            scope: None,
        });
        let result = infer(&ctx, &hole);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::Admissibility {
                violation: AdmissibilityViolation::UnfilledHole,
                ..
            } => {}
            other => panic!("expected UnfilledHole, got: {:?}", other),
        }
    }

    // -- 17. Unresolved level var rejected --

    #[test]
    fn unresolved_level_var_rejected() {
        let ctx = Context::empty();
        let term = Term::Sort(Sort::Type(Level::Var(LevelVar { index: 0 })));
        let result = infer(&ctx, &term);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::Admissibility {
                violation: AdmissibilityViolation::UnresolvedLevelVar(0),
                ..
            } => {}
            other => panic!("expected UnresolvedLevelVar, got: {:?}", other),
        }
    }

    // -- 18. Prop sort typing --

    #[test]
    fn prop_sort_has_type_type1() {
        let ctx = Context::empty();
        let prop = Term::Sort(Sort::Prop);
        let ty = infer(&ctx, &prop).unwrap();
        assert!(test_conv_eq(&ty, &type1()));
    }

    // -- 19. Let with dependent body --

    #[test]
    fn let_with_dependent_type() {
        let ctx = Context::empty();
        let body = pi(var(0), var(1));
        let term = let_(type1(), type0(), body);
        let ty = infer(&ctx, &term).unwrap();
        assert!(test_conv_eq(&ty, &type1()));
    }

    // -- 20. Effectful Pi rejected --

    #[test]
    fn effectful_pi_rejected() {
        let ctx = Context::empty();
        let term = Term::Pi {
            binder: Ident::new("x"),
            domain: Box::new(type0()),
            effect_row: Some(EffectRow::Effects(vec![Effect::Read])),
            codomain: Box::new(type0()),
        };
        let result = infer(&ctx, &term);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::Admissibility {
                violation: AdmissibilityViolation::EffectfulPiNotSupported,
                ..
            } => {}
            other => panic!("expected EffectfulPiNotSupported, got: {:?}", other),
        }
    }

    // -- 21. Deep application chain hits recursion depth limit --

    #[test]
    fn deep_app_chain_hits_recursion_limit() {
        // Build: (lam.id)(lam.id)...(lam.id)(Type_0) with depth > MAX_DEPTH.
        // The admissibility checker walks the arg chain of App nodes, so
        // 200 applications exceed the MAX_DEPTH=192 limit. We keep the chain
        // short enough that Rust's recursive Drop doesn't overflow the stack.
        // The test spawns on a thread with a large stack to be safe.
        let result = std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let ctx = Context::empty();
                let mut term = type0();
                for _ in 0..200 {
                    let id = lam(type1(), var(0));
                    let id_annot = annot(id, pi(type1(), type1()));
                    term = app(id_annot, term);
                }
                infer(&ctx, &term)
            })
            .expect("thread spawn")
            .join()
            .expect("thread join");
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::RecursionLimitExceeded => {}
            other => panic!("expected RecursionLimitExceeded, got: {:?}", other),
        }
    }

    // -- 22. Normal reduction within fuel budget succeeds --

    #[test]
    fn normal_reduction_within_fuel_budget() {
        // A modest chain of 10 identity applications should succeed.
        let ctx = Context::empty();
        let mut term = type0();
        for _ in 0..10 {
            let id = lam(type1(), var(0));
            let id_annot = annot(id, pi(type1(), type1()));
            term = app(id_annot, term);
        }
        let ty = infer(&ctx, &term).unwrap();
        assert!(test_conv_eq(&ty, &type1()));
    }

    // -- 23. term_size counts nodes correctly --

    #[test]
    fn term_size_basic() {
        // Type_0 is 1 node (Sort).
        assert_eq!(term_size(&type0()), 1);
        // lam(Type_0, v0) = Lambda { domain: Sort, body: Var } = 3 nodes.
        assert_eq!(term_size(&lam(type0(), var(0))), 3);
        // app(v0, v1) = App { func: Var, arg: Var } = 3 nodes.
        assert_eq!(term_size(&app(var(0), var(1))), 3);
    }

    // -- Fuel exhaustion: direct whnf tests --

    #[test]
    fn whnf_recursion_limit_on_chained_beta_reductions() {
        // Build: app(lam(T, v0), app(lam(T, v0), ... type0())) with depth > MAX_DEPTH.
        // whnf increments depth on each beta-reduce + recursive whnf call,
        // so 200 levels exceed MAX_DEPTH=192 before fuel runs out.
        let result = std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let mut term = type0();
                for _ in 0..200 {
                    term = app(lam(type1(), var(0)), term);
                }
                let mut fuel = MAX_WHNF_FUEL;
                whnf(&term, 0, &mut fuel)
            })
            .expect("thread spawn")
            .join()
            .expect("thread join");
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::RecursionLimitExceeded => {}
            other => panic!("expected RecursionLimitExceeded, got: {:?}", other),
        }
    }

    #[test]
    fn whnf_fuel_sufficient_for_normal_terms() {
        // 100 identity beta-reductions should be within budget and depth.
        let result = std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let mut term = type0();
                for _ in 0..100 {
                    term = app(lam(type1(), var(0)), term);
                }
                let mut fuel = MAX_WHNF_FUEL;
                let result = whnf(&term, 0, &mut fuel).unwrap();
                let consumed = MAX_WHNF_FUEL - fuel;
                (result, consumed)
            })
            .expect("thread spawn")
            .join()
            .expect("thread join");
        assert!(test_conv_eq(&result.0, &type0()));
        assert_eq!(result.1, 100);
    }

    #[test]
    fn whnf_let_unfolding_consumes_fuel() {
        // A single let-unfolding should consume exactly 1 fuel unit.
        // let x : Type_1 = Type_0 in x  =>  Type_0 (one zeta step)
        let term = let_(type1(), type0(), var(0));
        let mut fuel = MAX_WHNF_FUEL;
        let result = whnf(&term, 0, &mut fuel).unwrap();
        assert!(test_conv_eq(&result, &type0()));
        assert_eq!(MAX_WHNF_FUEL - fuel, 1);
    }

    #[test]
    fn whnf_fuel_exhaustion_with_limited_fuel() {
        // Build a 50-deep beta chain (well within MAX_DEPTH=192) but
        // supply only 10 units of fuel. Fuel exhaustion must fire before
        // the depth limit.
        let mut term = type0();
        for _ in 0..50 {
            term = app(lam(type1(), var(0)), term);
        }
        let mut fuel: usize = 10;
        let result = whnf(&term, 0, &mut fuel);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::ReductionLimitExceeded => {}
            other => panic!("expected ReductionLimitExceeded, got: {:?}", other),
        }
        // Fuel should be fully consumed (reached 0).
        assert_eq!(fuel, 0);
    }

    #[test]
    fn whnf_fuel_exhaustion_let_with_limited_fuel() {
        // Build a 50-deep let chain (within MAX_DEPTH=192) but supply
        // only 5 units of fuel.
        let mut term = type0();
        for _ in 0..50 {
            term = let_(type1(), type0(), term);
        }
        let mut fuel: usize = 5;
        let result = whnf(&term, 0, &mut fuel);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::ReductionLimitExceeded => {}
            other => panic!("expected ReductionLimitExceeded, got: {:?}", other),
        }
    }

    // -- 24. effect_row_eq: None vs Some(Empty) --

    #[test]
    fn effect_row_eq_none_vs_some_empty() {
        assert!(effect_row_eq(&None, &Some(EffectRow::Empty)));
        assert!(effect_row_eq(&Some(EffectRow::Empty), &None));
    }

    // -- 25. effect_row_eq: None vs Some(Effects([])) --

    #[test]
    fn effect_row_eq_none_vs_empty_effects_list() {
        assert!(effect_row_eq(&None, &Some(EffectRow::Effects(vec![]))));
        assert!(effect_row_eq(&Some(EffectRow::Effects(vec![])), &None));
    }

    // -- 26. effect_row_eq: Empty vs Effects([]) --

    #[test]
    fn effect_row_eq_empty_vs_empty_effects() {
        assert!(effect_row_eq(
            &Some(EffectRow::Empty),
            &Some(EffectRow::Effects(vec![]))
        ));
    }

    // -- 27. effect_row_eq: Join(Empty, Effects([Read])) vs Effects([Read]) --

    #[test]
    fn effect_row_eq_join_with_empty_is_identity() {
        let joined = EffectRow::Join(
            Box::new(EffectRow::Empty),
            Box::new(EffectRow::Effects(vec![Effect::Read])),
        );
        let flat = EffectRow::Effects(vec![Effect::Read]);
        assert!(effect_row_eq(&Some(joined.clone()), &Some(flat.clone())));
        assert!(effect_row_eq(&Some(flat), &Some(joined)));
    }

    // -- 28. effect_row_eq: nested Join flattening --

    #[test]
    fn effect_row_eq_nested_join_flattening() {
        let joined = EffectRow::Join(
            Box::new(EffectRow::Effects(vec![Effect::Read])),
            Box::new(EffectRow::Effects(vec![Effect::SanctionsQuery])),
        );
        let flat = EffectRow::Effects(vec![Effect::Read, Effect::SanctionsQuery]);
        assert!(effect_row_eq(&Some(joined), &Some(flat)));
    }

    // -- 29. effect_row_eq: deeply nested Join --

    #[test]
    fn effect_row_eq_deeply_nested_join() {
        let deep = EffectRow::Join(
            Box::new(EffectRow::Join(
                Box::new(EffectRow::Empty),
                Box::new(EffectRow::Effects(vec![Effect::Read])),
            )),
            Box::new(EffectRow::Join(
                Box::new(EffectRow::Effects(vec![Effect::SanctionsQuery])),
                Box::new(EffectRow::Empty),
            )),
        );
        let flat = EffectRow::Effects(vec![Effect::Read, Effect::SanctionsQuery]);
        assert!(effect_row_eq(&Some(deep), &Some(flat)));
    }

    // -- 30. effect_row_eq: different effects are not equal --

    #[test]
    fn effect_row_eq_different_effects_not_equal() {
        let a = Some(EffectRow::Effects(vec![Effect::Read]));
        let b = Some(EffectRow::Effects(vec![Effect::SanctionsQuery]));
        assert!(!effect_row_eq(&a, &b));
    }

    // -- 31. effect_row_eq: row variables block normalization --

    #[test]
    fn effect_row_eq_var_blocks_normalization() {
        assert!(!effect_row_eq(
            &Some(EffectRow::Var(0)),
            &Some(EffectRow::Var(1))
        ));
        assert!(effect_row_eq(
            &Some(EffectRow::Var(0)),
            &Some(EffectRow::Var(0))
        ));
        let joined_with_var = EffectRow::Join(
            Box::new(EffectRow::Var(0)),
            Box::new(EffectRow::Effects(vec![Effect::Read])),
        );
        assert!(!effect_row_eq(
            &Some(joined_with_var),
            &Some(EffectRow::Effects(vec![Effect::Read]))
        ));
    }

    // -- 32. effect_row_eq: None vs None --

    #[test]
    fn effect_row_eq_none_vs_none() {
        assert!(effect_row_eq(&None, &None));
    }

    // -- 33. effect_row_eq: BranchSensitive preserved --

    #[test]
    fn effect_row_eq_branch_sensitive_matters() {
        let plain = EffectRow::Effects(vec![Effect::Read]);
        let sensitive = EffectRow::BranchSensitive(Box::new(EffectRow::Effects(vec![Effect::Read])));
        assert!(!effect_row_eq(&Some(plain), &Some(sensitive)));
    }

    // -- 34. effect_row_eq: duplicate effects via Join --

    #[test]
    fn effect_row_eq_deduplicates_effects() {
        let joined_dup = EffectRow::Join(
            Box::new(EffectRow::Effects(vec![Effect::Read])),
            Box::new(EffectRow::Effects(vec![Effect::Read])),
        );
        let single = EffectRow::Effects(vec![Effect::Read]);
        assert!(effect_row_eq(&Some(joined_dup), &Some(single)));
    }

    // -- 35. Defeasible with admissible sub-terms passes admissibility --

    #[test]
    fn defeasible_with_admissible_body_passes_admissibility() {
        let term = Term::Defeasible(DefeasibleRule {
            name: Ident::new("simple_rule"),
            base_ty: Box::new(type0()),
            base_body: Box::new(type0()),
            exceptions: vec![],
            lattice: None,
        });
        assert!(check_admissibility(&term).is_ok());
    }

    #[test]
    fn defeasible_with_exceptions_passes_admissibility() {
        let term = Term::Defeasible(DefeasibleRule {
            name: Ident::new("rule_with_exceptions"),
            base_ty: Box::new(type0()),
            base_body: Box::new(type0()),
            exceptions: vec![
                Exception {
                    guard: Box::new(type0()),
                    body: Box::new(type0()),
                    priority: Some(10),
                    authority: None,
                },
                Exception {
                    guard: Box::new(type0()),
                    body: Box::new(type0()),
                    priority: Some(20),
                    authority: None,
                },
            ],
            lattice: None,
        });
        assert!(check_admissibility(&term).is_ok());
    }

    #[test]
    fn defeasible_with_rec_in_body_fails_admissibility() {
        let rec_term = Term::Rec {
            binder: Ident::new("f"),
            ty: Box::new(type0()),
            body: Box::new(var(0)),
        };
        let term = Term::Defeasible(DefeasibleRule {
            name: Ident::new("bad_rule"),
            base_ty: Box::new(type0()),
            base_body: Box::new(rec_term),
            exceptions: vec![],
            lattice: None,
        });
        let result = check_admissibility(&term);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::Admissibility {
                violation: AdmissibilityViolation::RecNotSupported,
                ..
            } => {}
            other => panic!("expected RecNotSupported, got: {:?}", other),
        }
    }

    #[test]
    fn defeasible_with_rec_in_exception_guard_fails_admissibility() {
        let rec_term = Term::Rec {
            binder: Ident::new("f"),
            ty: Box::new(type0()),
            body: Box::new(var(0)),
        };
        let term = Term::Defeasible(DefeasibleRule {
            name: Ident::new("bad_exception_rule"),
            base_ty: Box::new(type0()),
            base_body: Box::new(type0()),
            exceptions: vec![Exception {
                guard: Box::new(rec_term),
                body: Box::new(type0()),
                priority: None,
                authority: None,
            }],
            lattice: None,
        });
        let result = check_admissibility(&term);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::Admissibility {
                violation: AdmissibilityViolation::RecNotSupported,
                ..
            } => {}
            other => panic!("expected RecNotSupported, got: {:?}", other),
        }
    }

    #[test]
    fn defeasible_with_rec_in_exception_body_fails_admissibility() {
        let rec_term = Term::Rec {
            binder: Ident::new("f"),
            ty: Box::new(type0()),
            body: Box::new(var(0)),
        };
        let term = Term::Defeasible(DefeasibleRule {
            name: Ident::new("bad_exception_body_rule"),
            base_ty: Box::new(type0()),
            base_body: Box::new(type0()),
            exceptions: vec![Exception {
                guard: Box::new(type0()),
                body: Box::new(rec_term),
                priority: None,
                authority: None,
            }],
            lattice: None,
        });
        let result = check_admissibility(&term);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::Admissibility {
                violation: AdmissibilityViolation::RecNotSupported,
                ..
            } => {}
            other => panic!("expected RecNotSupported, got: {:?}", other),
        }
    }

    #[test]
    fn defeasible_with_rec_in_base_ty_fails_admissibility() {
        let rec_term = Term::Rec {
            binder: Ident::new("f"),
            ty: Box::new(type0()),
            body: Box::new(var(0)),
        };
        let term = Term::Defeasible(DefeasibleRule {
            name: Ident::new("bad_type_rule"),
            base_ty: Box::new(rec_term),
            base_body: Box::new(type0()),
            exceptions: vec![],
            lattice: None,
        });
        let result = check_admissibility(&term);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::Admissibility {
                violation: AdmissibilityViolation::RecNotSupported,
                ..
            } => {}
            other => panic!("expected RecNotSupported, got: {:?}", other),
        }
    }

    // -- 36. Defeasible type inference --

    #[test]
    fn defeasible_infers_base_ty() {
        // A defeasible rule with base_ty = Type_1 and base_body = Type_0
        // should infer to Type_1 (since Type_0 : Type_1).
        let ctx = Context::empty();
        let term = Term::Defeasible(DefeasibleRule {
            name: Ident::new("typed_rule"),
            base_ty: Box::new(type1()),
            base_body: Box::new(type0()),
            exceptions: vec![],
            lattice: None,
        });
        let ty = infer(&ctx, &term).unwrap();
        assert!(test_conv_eq(&ty, &type1()));
    }

    #[test]
    fn defeasible_with_exceptions_infers_base_ty() {
        // base_ty = Type_1, base_body = Type_0 (Type_0 : Type_1),
        // exception body = Type_0 (also Type_0 : Type_1).
        let ctx = Context::empty();
        let term = Term::Defeasible(DefeasibleRule {
            name: Ident::new("typed_exc_rule"),
            base_ty: Box::new(type1()),
            base_body: Box::new(type0()),
            exceptions: vec![Exception {
                guard: Box::new(type0()),
                body: Box::new(type0()),
                priority: Some(10),
                authority: None,
            }],
            lattice: None,
        });
        let ty = infer(&ctx, &term).unwrap();
        assert!(test_conv_eq(&ty, &type1()));
    }

    // -- 37. Match on prelude types --

    /// Helper: build a Constructor pattern with a simple name and no binders.
    fn ctor_pat(name: &str) -> Pattern {
        Pattern::Constructor {
            constructor: Constructor::new(QualIdent::simple(name)),
            binders: vec![],
        }
    }

    #[test]
    fn match_on_compliance_verdict_is_admissible() {
        let term = Term::match_expr(
            Term::constant("Compliant"),
            Term::constant("ComplianceVerdict"),
            vec![
                Branch {
                    pattern: ctor_pat("Compliant"),
                    body: Term::constant("Compliant"),
                },
                Branch {
                    pattern: ctor_pat("NonCompliant"),
                    body: Term::constant("NonCompliant"),
                },
                Branch {
                    pattern: ctor_pat("Pending"),
                    body: Term::constant("Pending"),
                },
            ],
        );
        assert!(check_admissibility(&term).is_ok());
    }

    #[test]
    fn match_on_bool_is_admissible() {
        let term = Term::match_expr(
            Term::constant("True"),
            Term::constant("Bool"),
            vec![
                Branch {
                    pattern: ctor_pat("True"),
                    body: Term::constant("Compliant"),
                },
                Branch {
                    pattern: ctor_pat("False"),
                    body: Term::constant("NonCompliant"),
                },
            ],
        );
        assert!(check_admissibility(&term).is_ok());
    }

    #[test]
    fn match_on_sanctions_result_is_admissible() {
        let term = Term::match_expr(
            Term::constant("Clear"),
            Term::constant("SanctionsResult"),
            vec![
                Branch {
                    pattern: ctor_pat("Clear"),
                    body: Term::constant("Compliant"),
                },
                Branch {
                    pattern: Pattern::Wildcard,
                    body: Term::constant("NonCompliant"),
                },
            ],
        );
        assert!(check_admissibility(&term).is_ok());
    }

    #[test]
    fn match_on_compliance_tag_is_admissible() {
        let term = Term::match_expr(
            Term::constant("Active"),
            Term::constant("ComplianceTag"),
            vec![
                Branch {
                    pattern: ctor_pat("Active"),
                    body: Term::constant("Compliant"),
                },
                Branch {
                    pattern: ctor_pat("Suspended"),
                    body: Term::constant("NonCompliant"),
                },
                Branch {
                    pattern: Pattern::Wildcard,
                    body: Term::constant("Pending"),
                },
            ],
        );
        assert!(check_admissibility(&term).is_ok());
    }

    #[test]
    fn match_on_nat_is_admissible() {
        let term = Term::match_expr(
            Term::constant("Zero"),
            Term::constant("Nat"),
            vec![
                Branch {
                    pattern: ctor_pat("Zero"),
                    body: Term::constant("Compliant"),
                },
                Branch {
                    pattern: Pattern::Wildcard,
                    body: Term::constant("NonCompliant"),
                },
            ],
        );
        assert!(check_admissibility(&term).is_ok());
    }

    #[test]
    fn match_wildcard_only_is_admissible() {
        let term = Term::match_expr(
            Term::constant("Compliant"),
            Term::constant("ComplianceVerdict"),
            vec![Branch {
                pattern: Pattern::Wildcard,
                body: Term::constant("Compliant"),
            }],
        );
        assert!(check_admissibility(&term).is_ok());
    }

    #[test]
    fn match_on_non_prelude_type_rejected() {
        let term = Term::match_expr(
            Term::constant("SomeUserType"),
            Term::constant("SomeUserType"),
            vec![Branch {
                pattern: ctor_pat("MyConstructor"),
                body: Term::constant("Compliant"),
            }],
        );
        let result = check_admissibility(&term);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::Admissibility {
                violation:
                    AdmissibilityViolation::MatchOnNonPreludeType {
                        constructor_name, ..
                    },
                ..
            } => {
                assert_eq!(constructor_name, "MyConstructor");
            }
            other => panic!("expected MatchOnNonPreludeType, got: {:?}", other),
        }
    }

    #[test]
    fn match_mixed_prelude_and_non_prelude_rejected() {
        let term = Term::match_expr(
            Term::constant("Compliant"),
            Term::constant("ComplianceVerdict"),
            vec![
                Branch {
                    pattern: ctor_pat("Compliant"),
                    body: Term::constant("Compliant"),
                },
                Branch {
                    pattern: ctor_pat("UnknownCtor"),
                    body: Term::constant("NonCompliant"),
                },
            ],
        );
        let result = check_admissibility(&term);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::Admissibility {
                violation:
                    AdmissibilityViolation::MatchOnNonPreludeType {
                        constructor_name, ..
                    },
                ..
            } => {
                assert_eq!(constructor_name, "UnknownCtor");
            }
            other => panic!("expected MatchOnNonPreludeType, got: {:?}", other),
        }
    }

    #[test]
    fn match_non_admissible_body_rejected() {
        let rec_body = Term::Rec {
            binder: Ident::new("f"),
            ty: Box::new(type0()),
            body: Box::new(var(0)),
        };
        // Cover both constructors of Bool so the match is exhaustive; the
        // body-level Rec must still be rejected by the inner admissibility
        // check.
        let term = Term::match_expr(
            Term::constant("True"),
            Term::constant("Bool"),
            vec![
                Branch {
                    pattern: ctor_pat("True"),
                    body: rec_body,
                },
                Branch {
                    pattern: ctor_pat("False"),
                    body: Term::constant("Compliant"),
                },
            ],
        );
        let result = check_admissibility(&term);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::Admissibility {
                violation: AdmissibilityViolation::RecNotSupported,
                ..
            } => {}
            other => panic!("expected RecNotSupported in branch body, got: {:?}", other),
        }
    }

    #[test]
    fn match_on_prelude_types_typechecks_with_prelude_context() {
        use crate::prelude::compliance_prelude;
        let ctx = compliance_prelude();

        let term = Term::match_expr(
            Term::constant("Compliant"),
            Term::constant("ComplianceVerdict"),
            vec![
                Branch {
                    pattern: ctor_pat("Compliant"),
                    body: Term::constant("Compliant"),
                },
                Branch {
                    pattern: ctor_pat("NonCompliant"),
                    body: Term::constant("NonCompliant"),
                },
                Branch {
                    pattern: ctor_pat("Pending"),
                    body: Term::constant("Pending"),
                },
            ],
        );
        let ty = infer(&ctx, &term).unwrap();
        assert!(test_conv_eq(&ty, &Term::constant("ComplianceVerdict")));
    }

    #[test]
    fn match_on_bool_typechecks_with_prelude_context() {
        use crate::prelude::compliance_prelude;
        let ctx = compliance_prelude();

        let term = Term::match_expr(
            Term::constant("True"),
            Term::constant("ComplianceVerdict"),
            vec![
                Branch {
                    pattern: ctor_pat("True"),
                    body: Term::constant("Compliant"),
                },
                Branch {
                    pattern: ctor_pat("False"),
                    body: Term::constant("NonCompliant"),
                },
            ],
        );
        let ty = infer(&ctx, &term).unwrap();
        assert!(test_conv_eq(&ty, &Term::constant("ComplianceVerdict")));
    }

    #[test]
    fn match_check_mode_on_prelude_type() {
        use crate::prelude::compliance_prelude;
        let ctx = compliance_prelude();

        let term = Term::match_expr(
            Term::constant("Clear"),
            Term::constant("ComplianceVerdict"),
            vec![
                Branch {
                    pattern: ctor_pat("Clear"),
                    body: Term::constant("Compliant"),
                },
                Branch {
                    pattern: Pattern::Wildcard,
                    body: Term::constant("NonCompliant"),
                },
            ],
        );
        check(&ctx, &term, &Term::constant("ComplianceVerdict")).unwrap();
    }
}
