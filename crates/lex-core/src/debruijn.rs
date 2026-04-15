//! De Bruijn index assignment and alpha-normalization for Core Lex.
//!
//! This module converts named-variable ASTs into De Bruijn-indexed form,
//! implements capture-avoiding substitution, index shifting, and
//! alpha-equality comparison.
//!
//! **De Bruijn convention:** index 0 refers to the innermost enclosing
//! binder, index 1 to the next enclosing binder, etc. Free variables
//! that are not bound by any enclosing binder produce `DebruijnError::Unbound`.
//!
//! Reference: `docs/architecture/LEX-CORE-GRAMMAR.md` §3.

use crate::ast::{
    Branch, DefeasibleRule, Exception, Hole, Ident, Pattern, PrincipleBalancingStep, Term,
};
use std::fmt;

/// Maximum recursion depth for De Bruijn index assignment, shifting, and substitution.
const MAX_DEPTH: usize = 192;

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors arising during De Bruijn index assignment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DebruijnError {
    /// A variable name was not bound by any enclosing binder.
    Unbound {
        /// The unbound variable name.
        name: String,
    },
    /// Recursion depth exceeded the safety limit.
    RecursionLimit {
        /// Which operation hit the limit.
        operation: String,
    },
}

impl fmt::Display for DebruijnError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DebruijnError::Unbound { name } => {
                write!(f, "unbound variable: {}", name)
            }
            DebruijnError::RecursionLimit { operation } => {
                write!(
                    f,
                    "recursion depth limit exceeded ({MAX_DEPTH}) during {operation}"
                )
            }
        }
    }
}

impl std::error::Error for DebruijnError {}

// ---------------------------------------------------------------------------
// Context — name-to-index mapping
// ---------------------------------------------------------------------------

/// A De Bruijn context: a stack of bound names where the most recent
/// binding is at the end (index 0).
#[derive(Debug, Clone, Default)]
struct Context {
    /// Stack of binder names (most recent = last).
    names: Vec<String>,
}

impl Context {
    /// Look up a name and return its De Bruijn index (0-based from the top).
    fn lookup(&self, name: &str) -> Option<u32> {
        for (i, n) in self.names.iter().rev().enumerate() {
            if n == name {
                return Some(i as u32);
            }
        }
        None
    }

    /// Push a new binder onto the context.
    fn push(&mut self, name: &str) {
        self.names.push(name.to_string());
    }

    /// Pop the most recent binder.
    fn pop(&mut self) {
        self.names.pop();
    }

    /// Push multiple names (for pattern bindings). Returns the count pushed.
    fn push_many(&mut self, idents: &[Ident]) -> usize {
        let n = idents.len();
        for id in idents {
            self.names.push(id.name.clone());
        }
        n
    }

    /// Pop `n` names.
    fn pop_many(&mut self, n: usize) {
        for _ in 0..n {
            self.names.pop();
        }
    }
}

// ---------------------------------------------------------------------------
// assign_indices — named variables → De Bruijn indices
// ---------------------------------------------------------------------------

/// Traverse the AST and replace every named variable reference with a
/// De Bruijn index relative to its binding site.
///
/// Returns a new `Term` where every `Var` has a correctly computed index.
/// Returns `DebruijnError::Unbound` if any variable is not in scope.
///
/// # Note on input format
///
/// The input `Term` is expected to have `Var { name, index: 0 }` for all
/// variables (the index value is ignored and recomputed). The output will
/// have correct De Bruijn indices.
pub fn assign_indices(term: &Term) -> Result<Term, DebruijnError> {
    let mut ctx = Context::default();
    assign_inner(term, &mut ctx, 0)
}

fn assign_inner(term: &Term, ctx: &mut Context, depth: usize) -> Result<Term, DebruijnError> {
    if depth > MAX_DEPTH {
        return Err(DebruijnError::RecursionLimit {
            operation: "index assignment".to_owned(),
        });
    }
    match term {
        Term::Var { name, .. } => match ctx.lookup(&name.name) {
            Some(idx) => Ok(Term::Var {
                name: name.clone(),
                index: idx,
            }),
            None => Err(DebruijnError::Unbound {
                name: name.name.clone(),
            }),
        },

        Term::Sort(s) => Ok(Term::Sort(s.clone())),
        Term::Constant(c) => Ok(Term::Constant(c.clone())),
        Term::ContentRefTerm(r) => Ok(Term::ContentRefTerm(r.clone())),
        Term::IntLit(n) => Ok(Term::IntLit(*n)),
        Term::RatLit(n, d) => Ok(Term::RatLit(*n, *d)),
        Term::StringLit(s) => Ok(Term::StringLit(s.clone())),
        Term::AxiomUse { axiom } => Ok(Term::AxiomUse {
            axiom: axiom.clone(),
        }),

        Term::Lambda {
            binder,
            domain,
            body,
        } => {
            let domain2 = assign_inner(domain, ctx, depth + 1)?;
            ctx.push(&binder.name);
            let body2 = assign_inner(body, ctx, depth + 1)?;
            ctx.pop();
            Ok(Term::Lambda {
                binder: binder.clone(),
                domain: Box::new(domain2),
                body: Box::new(body2),
            })
        }

        Term::Pi {
            binder,
            domain,
            effect_row,
            codomain,
        } => {
            let domain2 = assign_inner(domain, ctx, depth + 1)?;
            ctx.push(&binder.name);
            let codomain2 = assign_inner(codomain, ctx, depth + 1)?;
            ctx.pop();
            Ok(Term::Pi {
                binder: binder.clone(),
                domain: Box::new(domain2),
                effect_row: effect_row.clone(),
                codomain: Box::new(codomain2),
            })
        }

        Term::Sigma {
            binder,
            fst_ty,
            snd_ty,
        } => {
            let fst2 = assign_inner(fst_ty, ctx, depth + 1)?;
            ctx.push(&binder.name);
            let snd2 = assign_inner(snd_ty, ctx, depth + 1)?;
            ctx.pop();
            Ok(Term::Sigma {
                binder: binder.clone(),
                fst_ty: Box::new(fst2),
                snd_ty: Box::new(snd2),
            })
        }

        Term::App { func, arg } => {
            let func2 = assign_inner(func, ctx, depth + 1)?;
            let arg2 = assign_inner(arg, ctx, depth + 1)?;
            Ok(Term::App {
                func: Box::new(func2),
                arg: Box::new(arg2),
            })
        }

        Term::Pair { fst, snd } => {
            let fst2 = assign_inner(fst, ctx, depth + 1)?;
            let snd2 = assign_inner(snd, ctx, depth + 1)?;
            Ok(Term::Pair {
                fst: Box::new(fst2),
                snd: Box::new(snd2),
            })
        }

        Term::Proj { first, pair } => {
            let pair2 = assign_inner(pair, ctx, depth + 1)?;
            Ok(Term::Proj {
                first: *first,
                pair: Box::new(pair2),
            })
        }

        Term::InductiveIntro { constructor, args } => {
            let args2: Result<Vec<Term>, _> = args
                .iter()
                .map(|a| assign_inner(a, ctx, depth + 1))
                .collect();
            Ok(Term::InductiveIntro {
                constructor: constructor.clone(),
                args: args2?,
            })
        }

        Term::Annot { term: t, ty } => {
            let t2 = assign_inner(t, ctx, depth + 1)?;
            let ty2 = assign_inner(ty, ctx, depth + 1)?;
            Ok(Term::Annot {
                term: Box::new(t2),
                ty: Box::new(ty2),
            })
        }

        Term::Let {
            binder,
            ty,
            val,
            body,
        } => {
            let ty2 = assign_inner(ty, ctx, depth + 1)?;
            let val2 = assign_inner(val, ctx, depth + 1)?;
            ctx.push(&binder.name);
            let body2 = assign_inner(body, ctx, depth + 1)?;
            ctx.pop();
            Ok(Term::Let {
                binder: binder.clone(),
                ty: Box::new(ty2),
                val: Box::new(val2),
                body: Box::new(body2),
            })
        }

        Term::Match {
            scrutinee,
            return_ty,
            branches,
        } => {
            let scrutinee2 = assign_inner(scrutinee, ctx, depth + 1)?;
            let return_ty2 = assign_inner(return_ty, ctx, depth + 1)?;
            let mut branches2 = Vec::with_capacity(branches.len());
            for br in branches {
                branches2.push(assign_branch(br, ctx, depth + 1)?);
            }
            Ok(Term::Match {
                scrutinee: Box::new(scrutinee2),
                return_ty: Box::new(return_ty2),
                branches: branches2,
            })
        }

        Term::Rec { binder, ty, body } => {
            let ty2 = assign_inner(ty, ctx, depth + 1)?;
            ctx.push(&binder.name);
            let body2 = assign_inner(body, ctx, depth + 1)?;
            ctx.pop();
            Ok(Term::Rec {
                binder: binder.clone(),
                ty: Box::new(ty2),
                body: Box::new(body2),
            })
        }

        // Temporal / modal / sanctions — recurse into sub-terms
        Term::SanctionsDominance { proof } => {
            let proof2 = assign_inner(proof, ctx, depth + 1)?;
            Ok(Term::SanctionsDominance {
                proof: Box::new(proof2),
            })
        }

        Term::DefeatElim { rule } => {
            let rule2 = assign_inner(rule, ctx, depth + 1)?;
            Ok(Term::DefeatElim {
                rule: Box::new(rule2),
            })
        }

        Term::Lift0 { time } => {
            let time2 = assign_inner(time, ctx, depth + 1)?;
            Ok(Term::Lift0 {
                time: Box::new(time2),
            })
        }

        Term::Derive1 { time, witness } => {
            let time2 = assign_inner(time, ctx, depth + 1)?;
            let witness2 = assign_inner(witness, ctx, depth + 1)?;
            Ok(Term::Derive1 {
                time: Box::new(time2),
                witness: Box::new(witness2),
            })
        }

        Term::ModalAt { time, body } => {
            let body2 = assign_inner(body, ctx, depth + 1)?;
            Ok(Term::ModalAt {
                time: time.clone(),
                body: Box::new(body2),
            })
        }

        Term::ModalEventually { time, body } => {
            let body2 = assign_inner(body, ctx, depth + 1)?;
            Ok(Term::ModalEventually {
                time: time.clone(),
                body: Box::new(body2),
            })
        }

        Term::ModalAlways { from, to, body } => {
            let body2 = assign_inner(body, ctx, depth + 1)?;
            Ok(Term::ModalAlways {
                from: from.clone(),
                to: to.clone(),
                body: Box::new(body2),
            })
        }

        Term::ModalIntro { tribunal, body } => {
            let body2 = assign_inner(body, ctx, depth + 1)?;
            Ok(Term::ModalIntro {
                tribunal: tribunal.clone(),
                body: Box::new(body2),
            })
        }

        Term::ModalElim {
            from_tribunal,
            to_tribunal,
            term: inner,
            witness,
        } => {
            let inner2 = assign_inner(inner, ctx, depth + 1)?;
            let witness2 = assign_inner(witness, ctx, depth + 1)?;
            Ok(Term::ModalElim {
                from_tribunal: from_tribunal.clone(),
                to_tribunal: to_tribunal.clone(),
                term: Box::new(inner2),
                witness: Box::new(witness2),
            })
        }

        Term::Defeasible(dr) => {
            let base_ty2 = assign_inner(&dr.base_ty, ctx, depth + 1)?;
            let base_body2 = assign_inner(&dr.base_body, ctx, depth + 1)?;
            let exceptions2: Result<Vec<Exception>, _> = dr
                .exceptions
                .iter()
                .map(|ex| {
                    let guard2 = assign_inner(&ex.guard, ctx, depth + 1)?;
                    let body2 = assign_inner(&ex.body, ctx, depth + 1)?;
                    Ok(Exception {
                        guard: Box::new(guard2),
                        body: Box::new(body2),
                        priority: ex.priority,
                        authority: ex.authority.clone(),
                    })
                })
                .collect();
            Ok(Term::Defeasible(DefeasibleRule {
                name: dr.name.clone(),
                base_ty: Box::new(base_ty2),
                base_body: Box::new(base_body2),
                exceptions: exceptions2?,
                lattice: dr.lattice.clone(),
            }))
        }

        Term::Hole(h) => {
            let ty2 = assign_inner(&h.ty, ctx, depth + 1)?;
            Ok(Term::Hole(Hole {
                name: h.name.clone(),
                ty: Box::new(ty2),
                authority: h.authority.clone(),
                scope: h.scope.clone(),
            }))
        }

        Term::HoleFill {
            hole_name,
            filler,
            pcauth,
        } => {
            let filler2 = assign_inner(filler, ctx, depth + 1)?;
            let pcauth2 = assign_inner(pcauth, ctx, depth + 1)?;
            Ok(Term::HoleFill {
                hole_name: hole_name.clone(),
                filler: Box::new(filler2),
                pcauth: Box::new(pcauth2),
            })
        }

        Term::PrincipleBalance(pb) => {
            let verdict2 = assign_inner(&pb.verdict, ctx, depth + 1)?;
            let rationale2 = assign_inner(&pb.rationale, ctx, depth + 1)?;
            Ok(Term::PrincipleBalance(PrincipleBalancingStep {
                principles: pb.principles.clone(),
                precedents: pb.precedents.clone(),
                verdict: Box::new(verdict2),
                rationale: Box::new(rationale2),
            }))
        }

        Term::Unlock { effect_row, body } => {
            let row2 = assign_inner(effect_row, ctx, depth + 1)?;
            let body2 = assign_inner(body, ctx, depth + 1)?;
            Ok(Term::Unlock {
                effect_row: Box::new(row2),
                body: Box::new(body2),
            })
        }
    }
}

fn assign_branch(br: &Branch, ctx: &mut Context, depth: usize) -> Result<Branch, DebruijnError> {
    match &br.pattern {
        Pattern::Constructor {
            constructor,
            binders,
        } => {
            let n = ctx.push_many(binders);
            let body2 = assign_inner(&br.body, ctx, depth + 1)?;
            ctx.pop_many(n);
            Ok(Branch {
                pattern: Pattern::Constructor {
                    constructor: constructor.clone(),
                    binders: binders.clone(),
                },
                body: body2,
            })
        }
        Pattern::Wildcard => {
            let body2 = assign_inner(&br.body, ctx, depth + 1)?;
            Ok(Branch {
                pattern: Pattern::Wildcard,
                body: body2,
            })
        }
    }
}

// ---------------------------------------------------------------------------
// shift — adjust free variable indices
// ---------------------------------------------------------------------------

/// Shift all free variable indices in `term` by `amount`.
///
/// A variable is "free" relative to `cutoff`: any `Var` with
/// `index >= cutoff` is shifted. Bound variables (index < cutoff) are
/// left untouched. The `cutoff` increases by 1 when descending under
/// a binder.
///
/// Returns `DebruijnError::RecursionLimit` if the term exceeds `MAX_DEPTH`.
pub fn shift(term: &Term, cutoff: u32, amount: i32) -> Result<Term, DebruijnError> {
    shift_inner(term, cutoff, amount, 0)
}

fn shift_inner(term: &Term, cutoff: u32, amount: i32, depth: usize) -> Result<Term, DebruijnError> {
    if depth > MAX_DEPTH {
        return Err(DebruijnError::RecursionLimit {
            operation: "shift".to_owned(),
        });
    }
    match term {
        Term::Var { name, index } => {
            if *index >= cutoff {
                let sum = *index as i64 + amount as i64;
                assert!(
                    sum >= 0,
                    "shift would produce negative De Bruijn index: {index} + {amount}"
                );
                let new_idx = sum as u32;
                Ok(Term::Var {
                    name: name.clone(),
                    index: new_idx,
                })
            } else {
                Ok(Term::Var {
                    name: name.clone(),
                    index: *index,
                })
            }
        }

        Term::Sort(s) => Ok(Term::Sort(s.clone())),
        Term::Constant(c) => Ok(Term::Constant(c.clone())),
        Term::ContentRefTerm(r) => Ok(Term::ContentRefTerm(r.clone())),
        Term::IntLit(n) => Ok(Term::IntLit(*n)),
        Term::RatLit(n, d) => Ok(Term::RatLit(*n, *d)),
        Term::StringLit(s) => Ok(Term::StringLit(s.clone())),
        Term::AxiomUse { axiom } => Ok(Term::AxiomUse {
            axiom: axiom.clone(),
        }),

        Term::Lambda {
            binder,
            domain,
            body,
        } => Ok(Term::Lambda {
            binder: binder.clone(),
            domain: Box::new(shift_inner(domain, cutoff, amount, depth + 1)?),
            body: Box::new(shift_inner(body, cutoff + 1, amount, depth + 1)?),
        }),

        Term::Pi {
            binder,
            domain,
            effect_row,
            codomain,
        } => Ok(Term::Pi {
            binder: binder.clone(),
            domain: Box::new(shift_inner(domain, cutoff, amount, depth + 1)?),
            effect_row: effect_row.clone(),
            codomain: Box::new(shift_inner(codomain, cutoff + 1, amount, depth + 1)?),
        }),

        Term::Sigma {
            binder,
            fst_ty,
            snd_ty,
        } => Ok(Term::Sigma {
            binder: binder.clone(),
            fst_ty: Box::new(shift_inner(fst_ty, cutoff, amount, depth + 1)?),
            snd_ty: Box::new(shift_inner(snd_ty, cutoff + 1, amount, depth + 1)?),
        }),

        Term::App { func, arg } => Ok(Term::App {
            func: Box::new(shift_inner(func, cutoff, amount, depth + 1)?),
            arg: Box::new(shift_inner(arg, cutoff, amount, depth + 1)?),
        }),

        Term::Pair { fst, snd } => Ok(Term::Pair {
            fst: Box::new(shift_inner(fst, cutoff, amount, depth + 1)?),
            snd: Box::new(shift_inner(snd, cutoff, amount, depth + 1)?),
        }),

        Term::Proj { first, pair } => Ok(Term::Proj {
            first: *first,
            pair: Box::new(shift_inner(pair, cutoff, amount, depth + 1)?),
        }),

        Term::InductiveIntro { constructor, args } => {
            let args2: Result<Vec<Term>, _> = args
                .iter()
                .map(|a| shift_inner(a, cutoff, amount, depth + 1))
                .collect();
            Ok(Term::InductiveIntro {
                constructor: constructor.clone(),
                args: args2?,
            })
        }

        Term::Annot { term: t, ty } => Ok(Term::Annot {
            term: Box::new(shift_inner(t, cutoff, amount, depth + 1)?),
            ty: Box::new(shift_inner(ty, cutoff, amount, depth + 1)?),
        }),

        Term::Let {
            binder,
            ty,
            val,
            body,
        } => Ok(Term::Let {
            binder: binder.clone(),
            ty: Box::new(shift_inner(ty, cutoff, amount, depth + 1)?),
            val: Box::new(shift_inner(val, cutoff, amount, depth + 1)?),
            body: Box::new(shift_inner(body, cutoff + 1, amount, depth + 1)?),
        }),

        Term::Match {
            scrutinee,
            return_ty,
            branches,
        } => {
            let branches2: Result<Vec<Branch>, _> = branches
                .iter()
                .map(|br| shift_branch(br, cutoff, amount, depth + 1))
                .collect();
            Ok(Term::Match {
                scrutinee: Box::new(shift_inner(scrutinee, cutoff, amount, depth + 1)?),
                return_ty: Box::new(shift_inner(return_ty, cutoff, amount, depth + 1)?),
                branches: branches2?,
            })
        }

        Term::Rec { binder, ty, body } => Ok(Term::Rec {
            binder: binder.clone(),
            ty: Box::new(shift_inner(ty, cutoff, amount, depth + 1)?),
            body: Box::new(shift_inner(body, cutoff + 1, amount, depth + 1)?),
        }),

        Term::SanctionsDominance { proof } => Ok(Term::SanctionsDominance {
            proof: Box::new(shift_inner(proof, cutoff, amount, depth + 1)?),
        }),
        Term::DefeatElim { rule } => Ok(Term::DefeatElim {
            rule: Box::new(shift_inner(rule, cutoff, amount, depth + 1)?),
        }),
        Term::Lift0 { time } => Ok(Term::Lift0 {
            time: Box::new(shift_inner(time, cutoff, amount, depth + 1)?),
        }),
        Term::Derive1 { time, witness } => Ok(Term::Derive1 {
            time: Box::new(shift_inner(time, cutoff, amount, depth + 1)?),
            witness: Box::new(shift_inner(witness, cutoff, amount, depth + 1)?),
        }),

        Term::ModalAt { time, body } => Ok(Term::ModalAt {
            time: time.clone(),
            body: Box::new(shift_inner(body, cutoff, amount, depth + 1)?),
        }),
        Term::ModalEventually { time, body } => Ok(Term::ModalEventually {
            time: time.clone(),
            body: Box::new(shift_inner(body, cutoff, amount, depth + 1)?),
        }),
        Term::ModalAlways { from, to, body } => Ok(Term::ModalAlways {
            from: from.clone(),
            to: to.clone(),
            body: Box::new(shift_inner(body, cutoff, amount, depth + 1)?),
        }),
        Term::ModalIntro { tribunal, body } => Ok(Term::ModalIntro {
            tribunal: tribunal.clone(),
            body: Box::new(shift_inner(body, cutoff, amount, depth + 1)?),
        }),
        Term::ModalElim {
            from_tribunal,
            to_tribunal,
            term: inner,
            witness,
        } => Ok(Term::ModalElim {
            from_tribunal: from_tribunal.clone(),
            to_tribunal: to_tribunal.clone(),
            term: Box::new(shift_inner(inner, cutoff, amount, depth + 1)?),
            witness: Box::new(shift_inner(witness, cutoff, amount, depth + 1)?),
        }),

        Term::Defeasible(dr) => {
            let exceptions2: Result<Vec<Exception>, _> = dr
                .exceptions
                .iter()
                .map(|ex| {
                    Ok(Exception {
                        guard: Box::new(shift_inner(&ex.guard, cutoff, amount, depth + 1)?),
                        body: Box::new(shift_inner(&ex.body, cutoff, amount, depth + 1)?),
                        priority: ex.priority,
                        authority: ex.authority.clone(),
                    })
                })
                .collect();
            Ok(Term::Defeasible(DefeasibleRule {
                name: dr.name.clone(),
                base_ty: Box::new(shift_inner(&dr.base_ty, cutoff, amount, depth + 1)?),
                base_body: Box::new(shift_inner(&dr.base_body, cutoff, amount, depth + 1)?),
                exceptions: exceptions2?,
                lattice: dr.lattice.clone(),
            }))
        }

        Term::Hole(h) => Ok(Term::Hole(Hole {
            name: h.name.clone(),
            ty: Box::new(shift_inner(&h.ty, cutoff, amount, depth + 1)?),
            authority: h.authority.clone(),
            scope: h.scope.clone(),
        })),

        Term::HoleFill {
            hole_name,
            filler,
            pcauth,
        } => Ok(Term::HoleFill {
            hole_name: hole_name.clone(),
            filler: Box::new(shift_inner(filler, cutoff, amount, depth + 1)?),
            pcauth: Box::new(shift_inner(pcauth, cutoff, amount, depth + 1)?),
        }),

        Term::PrincipleBalance(pb) => Ok(Term::PrincipleBalance(PrincipleBalancingStep {
            principles: pb.principles.clone(),
            precedents: pb.precedents.clone(),
            verdict: Box::new(shift_inner(&pb.verdict, cutoff, amount, depth + 1)?),
            rationale: Box::new(shift_inner(&pb.rationale, cutoff, amount, depth + 1)?),
        })),

        Term::Unlock { effect_row, body } => Ok(Term::Unlock {
            effect_row: Box::new(shift_inner(effect_row, cutoff, amount, depth + 1)?),
            body: Box::new(shift_inner(body, cutoff, amount, depth + 1)?),
        }),
    }
}

fn shift_branch(
    br: &Branch,
    cutoff: u32,
    amount: i32,
    depth: usize,
) -> Result<Branch, DebruijnError> {
    match &br.pattern {
        Pattern::Constructor {
            constructor,
            binders,
        } => {
            let binder_count = binders.len() as u32;
            Ok(Branch {
                pattern: Pattern::Constructor {
                    constructor: constructor.clone(),
                    binders: binders.clone(),
                },
                body: shift_inner(&br.body, cutoff + binder_count, amount, depth + 1)?,
            })
        }
        Pattern::Wildcard => Ok(Branch {
            pattern: Pattern::Wildcard,
            body: shift_inner(&br.body, cutoff, amount, depth + 1)?,
        }),
    }
}

// ---------------------------------------------------------------------------
// substitute — capture-avoiding substitution
// ---------------------------------------------------------------------------

/// Capture-avoiding substitution: `term[index := replacement]`.
///
/// Replaces every free occurrence of variable `index` in `term` with
/// `replacement`. Uses `shift` to avoid capture when descending under
/// binders.
///
/// Returns `DebruijnError::RecursionLimit` if the term exceeds `MAX_DEPTH`.
pub fn substitute(term: &Term, index: u32, replacement: &Term) -> Result<Term, DebruijnError> {
    substitute_inner(term, index, replacement, 0)
}

fn substitute_inner(
    term: &Term,
    index: u32,
    replacement: &Term,
    depth: usize,
) -> Result<Term, DebruijnError> {
    if depth > MAX_DEPTH {
        return Err(DebruijnError::RecursionLimit {
            operation: "substitution".to_owned(),
        });
    }
    match term {
        Term::Var { name, index: idx } => {
            if *idx == index {
                Ok(replacement.clone())
            } else if *idx > index {
                Ok(Term::Var {
                    name: name.clone(),
                    index: *idx - 1,
                })
            } else {
                Ok(Term::Var {
                    name: name.clone(),
                    index: *idx,
                })
            }
        }

        Term::Sort(s) => Ok(Term::Sort(s.clone())),
        Term::Constant(c) => Ok(Term::Constant(c.clone())),
        Term::ContentRefTerm(r) => Ok(Term::ContentRefTerm(r.clone())),
        Term::IntLit(n) => Ok(Term::IntLit(*n)),
        Term::RatLit(n, d) => Ok(Term::RatLit(*n, *d)),
        Term::StringLit(s) => Ok(Term::StringLit(s.clone())),
        Term::AxiomUse { axiom } => Ok(Term::AxiomUse {
            axiom: axiom.clone(),
        }),

        Term::Lambda {
            binder,
            domain,
            body,
        } => {
            let domain2 = substitute_inner(domain, index, replacement, depth + 1)?;
            let shifted_repl = shift(replacement, 0, 1)?;
            let body2 = substitute_inner(body, index + 1, &shifted_repl, depth + 1)?;
            Ok(Term::Lambda {
                binder: binder.clone(),
                domain: Box::new(domain2),
                body: Box::new(body2),
            })
        }

        Term::Pi {
            binder,
            domain,
            effect_row,
            codomain,
        } => {
            let domain2 = substitute_inner(domain, index, replacement, depth + 1)?;
            let shifted_repl = shift(replacement, 0, 1)?;
            let codomain2 = substitute_inner(codomain, index + 1, &shifted_repl, depth + 1)?;
            Ok(Term::Pi {
                binder: binder.clone(),
                domain: Box::new(domain2),
                effect_row: effect_row.clone(),
                codomain: Box::new(codomain2),
            })
        }

        Term::Sigma {
            binder,
            fst_ty,
            snd_ty,
        } => {
            let fst2 = substitute_inner(fst_ty, index, replacement, depth + 1)?;
            let shifted_repl = shift(replacement, 0, 1)?;
            let snd2 = substitute_inner(snd_ty, index + 1, &shifted_repl, depth + 1)?;
            Ok(Term::Sigma {
                binder: binder.clone(),
                fst_ty: Box::new(fst2),
                snd_ty: Box::new(snd2),
            })
        }

        Term::App { func, arg } => Ok(Term::App {
            func: Box::new(substitute_inner(func, index, replacement, depth + 1)?),
            arg: Box::new(substitute_inner(arg, index, replacement, depth + 1)?),
        }),

        Term::Pair { fst, snd } => Ok(Term::Pair {
            fst: Box::new(substitute_inner(fst, index, replacement, depth + 1)?),
            snd: Box::new(substitute_inner(snd, index, replacement, depth + 1)?),
        }),

        Term::Proj { first, pair } => Ok(Term::Proj {
            first: *first,
            pair: Box::new(substitute_inner(pair, index, replacement, depth + 1)?),
        }),

        Term::InductiveIntro { constructor, args } => {
            let args2: Result<Vec<Term>, _> = args
                .iter()
                .map(|a| substitute_inner(a, index, replacement, depth + 1))
                .collect();
            Ok(Term::InductiveIntro {
                constructor: constructor.clone(),
                args: args2?,
            })
        }

        Term::Annot { term: t, ty } => Ok(Term::Annot {
            term: Box::new(substitute_inner(t, index, replacement, depth + 1)?),
            ty: Box::new(substitute_inner(ty, index, replacement, depth + 1)?),
        }),

        Term::Let {
            binder,
            ty,
            val,
            body,
        } => {
            let ty2 = substitute_inner(ty, index, replacement, depth + 1)?;
            let val2 = substitute_inner(val, index, replacement, depth + 1)?;
            let shifted_repl = shift(replacement, 0, 1)?;
            let body2 = substitute_inner(body, index + 1, &shifted_repl, depth + 1)?;
            Ok(Term::Let {
                binder: binder.clone(),
                ty: Box::new(ty2),
                val: Box::new(val2),
                body: Box::new(body2),
            })
        }

        Term::Match {
            scrutinee,
            return_ty,
            branches,
        } => {
            let branches2: Result<Vec<Branch>, _> = branches
                .iter()
                .map(|br| substitute_branch(br, index, replacement, depth + 1))
                .collect();
            Ok(Term::Match {
                scrutinee: Box::new(substitute_inner(scrutinee, index, replacement, depth + 1)?),
                return_ty: Box::new(substitute_inner(return_ty, index, replacement, depth + 1)?),
                branches: branches2?,
            })
        }

        Term::Rec { binder, ty, body } => {
            let ty2 = substitute_inner(ty, index, replacement, depth + 1)?;
            let shifted_repl = shift(replacement, 0, 1)?;
            let body2 = substitute_inner(body, index + 1, &shifted_repl, depth + 1)?;
            Ok(Term::Rec {
                binder: binder.clone(),
                ty: Box::new(ty2),
                body: Box::new(body2),
            })
        }

        Term::SanctionsDominance { proof } => Ok(Term::SanctionsDominance {
            proof: Box::new(substitute_inner(proof, index, replacement, depth + 1)?),
        }),
        Term::DefeatElim { rule } => Ok(Term::DefeatElim {
            rule: Box::new(substitute_inner(rule, index, replacement, depth + 1)?),
        }),
        Term::Lift0 { time } => Ok(Term::Lift0 {
            time: Box::new(substitute_inner(time, index, replacement, depth + 1)?),
        }),
        Term::Derive1 { time, witness } => Ok(Term::Derive1 {
            time: Box::new(substitute_inner(time, index, replacement, depth + 1)?),
            witness: Box::new(substitute_inner(witness, index, replacement, depth + 1)?),
        }),

        Term::ModalAt { time, body } => Ok(Term::ModalAt {
            time: time.clone(),
            body: Box::new(substitute_inner(body, index, replacement, depth + 1)?),
        }),
        Term::ModalEventually { time, body } => Ok(Term::ModalEventually {
            time: time.clone(),
            body: Box::new(substitute_inner(body, index, replacement, depth + 1)?),
        }),
        Term::ModalAlways { from, to, body } => Ok(Term::ModalAlways {
            from: from.clone(),
            to: to.clone(),
            body: Box::new(substitute_inner(body, index, replacement, depth + 1)?),
        }),
        Term::ModalIntro { tribunal, body } => Ok(Term::ModalIntro {
            tribunal: tribunal.clone(),
            body: Box::new(substitute_inner(body, index, replacement, depth + 1)?),
        }),
        Term::ModalElim {
            from_tribunal,
            to_tribunal,
            term: inner,
            witness,
        } => Ok(Term::ModalElim {
            from_tribunal: from_tribunal.clone(),
            to_tribunal: to_tribunal.clone(),
            term: Box::new(substitute_inner(inner, index, replacement, depth + 1)?),
            witness: Box::new(substitute_inner(witness, index, replacement, depth + 1)?),
        }),

        Term::Defeasible(dr) => {
            let exceptions2: Result<Vec<Exception>, _> = dr
                .exceptions
                .iter()
                .map(|ex| {
                    Ok(Exception {
                        guard: Box::new(substitute_inner(
                            &ex.guard,
                            index,
                            replacement,
                            depth + 1,
                        )?),
                        body: Box::new(substitute_inner(&ex.body, index, replacement, depth + 1)?),
                        priority: ex.priority,
                        authority: ex.authority.clone(),
                    })
                })
                .collect();
            Ok(Term::Defeasible(DefeasibleRule {
                name: dr.name.clone(),
                base_ty: Box::new(substitute_inner(
                    &dr.base_ty,
                    index,
                    replacement,
                    depth + 1,
                )?),
                base_body: Box::new(substitute_inner(
                    &dr.base_body,
                    index,
                    replacement,
                    depth + 1,
                )?),
                exceptions: exceptions2?,
                lattice: dr.lattice.clone(),
            }))
        }

        Term::Hole(h) => Ok(Term::Hole(Hole {
            name: h.name.clone(),
            ty: Box::new(substitute_inner(&h.ty, index, replacement, depth + 1)?),
            authority: h.authority.clone(),
            scope: h.scope.clone(),
        })),

        Term::HoleFill {
            hole_name,
            filler,
            pcauth,
        } => Ok(Term::HoleFill {
            hole_name: hole_name.clone(),
            filler: Box::new(substitute_inner(filler, index, replacement, depth + 1)?),
            pcauth: Box::new(substitute_inner(pcauth, index, replacement, depth + 1)?),
        }),

        Term::PrincipleBalance(pb) => Ok(Term::PrincipleBalance(PrincipleBalancingStep {
            principles: pb.principles.clone(),
            precedents: pb.precedents.clone(),
            verdict: Box::new(substitute_inner(
                &pb.verdict,
                index,
                replacement,
                depth + 1,
            )?),
            rationale: Box::new(substitute_inner(
                &pb.rationale,
                index,
                replacement,
                depth + 1,
            )?),
        })),

        Term::Unlock { effect_row, body } => Ok(Term::Unlock {
            effect_row: Box::new(substitute_inner(effect_row, index, replacement, depth + 1)?),
            body: Box::new(substitute_inner(body, index, replacement, depth + 1)?),
        }),
    }
}

fn substitute_branch(
    br: &Branch,
    index: u32,
    replacement: &Term,
    depth: usize,
) -> Result<Branch, DebruijnError> {
    match &br.pattern {
        Pattern::Constructor {
            constructor,
            binders,
        } => {
            let binder_count = binders.len() as u32;
            let mut shifted = replacement.clone();
            for _ in 0..binder_count {
                shifted = shift(&shifted, 0, 1)?;
            }
            Ok(Branch {
                pattern: Pattern::Constructor {
                    constructor: constructor.clone(),
                    binders: binders.clone(),
                },
                body: substitute_inner(&br.body, index + binder_count, &shifted, depth + 1)?,
            })
        }
        Pattern::Wildcard => Ok(Branch {
            pattern: Pattern::Wildcard,
            body: substitute_inner(&br.body, index, replacement, depth + 1)?,
        }),
    }
}

// ---------------------------------------------------------------------------
// alpha_equal — structural equality after index assignment
// ---------------------------------------------------------------------------

/// Returns `true` if `a` and `b` are alpha-equivalent.
///
/// Both terms are first converted to De Bruijn-indexed form via
/// `assign_indices`. If either conversion fails, the terms are
/// considered not equal. After index assignment, structural equality
/// on the indexed terms (ignoring binder name hints) determines
/// alpha-equivalence.
pub fn alpha_equal(a: &Term, b: &Term) -> bool {
    let a_idx = match assign_indices(a) {
        Ok(t) => t,
        Err(_) => return false,
    };
    let b_idx = match assign_indices(b) {
        Ok(t) => t,
        Err(_) => return false,
    };
    structural_eq(&a_idx, &b_idx)
}

/// Structural equality on De Bruijn-indexed terms, ignoring binder name hints.
fn structural_eq(a: &Term, b: &Term) -> bool {
    match (a, b) {
        (Term::Var { index: i1, .. }, Term::Var { index: i2, .. }) => i1 == i2,

        (Term::Sort(s1), Term::Sort(s2)) => s1 == s2,
        (Term::Constant(c1), Term::Constant(c2)) => c1 == c2,
        (Term::ContentRefTerm(r1), Term::ContentRefTerm(r2)) => r1 == r2,
        (Term::IntLit(i1), Term::IntLit(i2)) => i1 == i2,
        (Term::RatLit(n1, d1), Term::RatLit(n2, d2)) => n1 == n2 && d1 == d2,
        (Term::StringLit(s1), Term::StringLit(s2)) => s1 == s2,
        (Term::AxiomUse { axiom: a1 }, Term::AxiomUse { axiom: a2 }) => a1 == a2,

        (
            Term::Lambda {
                domain: d1,
                body: b1,
                ..
            },
            Term::Lambda {
                domain: d2,
                body: b2,
                ..
            },
        ) => structural_eq(d1, d2) && structural_eq(b1, b2),

        (
            Term::Pi {
                domain: d1,
                effect_row: e1,
                codomain: c1,
                ..
            },
            Term::Pi {
                domain: d2,
                effect_row: e2,
                codomain: c2,
                ..
            },
        ) => structural_eq(d1, d2) && e1 == e2 && structural_eq(c1, c2),

        (
            Term::Sigma {
                fst_ty: f1,
                snd_ty: s1,
                ..
            },
            Term::Sigma {
                fst_ty: f2,
                snd_ty: s2,
                ..
            },
        ) => structural_eq(f1, f2) && structural_eq(s1, s2),

        (Term::App { func: f1, arg: a1 }, Term::App { func: f2, arg: a2 }) => {
            structural_eq(f1, f2) && structural_eq(a1, a2)
        }

        (Term::Pair { fst: f1, snd: s1 }, Term::Pair { fst: f2, snd: s2 }) => {
            structural_eq(f1, f2) && structural_eq(s1, s2)
        }

        (
            Term::Proj {
                first: f1,
                pair: p1,
            },
            Term::Proj {
                first: f2,
                pair: p2,
            },
        ) => f1 == f2 && structural_eq(p1, p2),

        (
            Term::InductiveIntro {
                constructor: c1,
                args: a1,
            },
            Term::InductiveIntro {
                constructor: c2,
                args: a2,
            },
        ) => {
            c1 == c2
                && a1.len() == a2.len()
                && a1.iter().zip(a2.iter()).all(|(x, y)| structural_eq(x, y))
        }

        (Term::Annot { term: t1, ty: ty1 }, Term::Annot { term: t2, ty: ty2 }) => {
            structural_eq(t1, t2) && structural_eq(ty1, ty2)
        }

        (
            Term::Let {
                ty: ty1,
                val: v1,
                body: b1,
                ..
            },
            Term::Let {
                ty: ty2,
                val: v2,
                body: b2,
                ..
            },
        ) => structural_eq(ty1, ty2) && structural_eq(v1, v2) && structural_eq(b1, b2),

        (
            Term::Match {
                scrutinee: s1,
                return_ty: r1,
                branches: bs1,
            },
            Term::Match {
                scrutinee: s2,
                return_ty: r2,
                branches: bs2,
            },
        ) => {
            structural_eq(s1, s2)
                && structural_eq(r1, r2)
                && bs1.len() == bs2.len()
                && bs1
                    .iter()
                    .zip(bs2.iter())
                    .all(|(b1, b2)| branch_structural_eq(b1, b2))
        }

        (
            Term::Rec {
                ty: ty1, body: b1, ..
            },
            Term::Rec {
                ty: ty2, body: b2, ..
            },
        ) => structural_eq(ty1, ty2) && structural_eq(b1, b2),

        (Term::SanctionsDominance { proof: p1 }, Term::SanctionsDominance { proof: p2 }) => {
            structural_eq(p1, p2)
        }

        (Term::DefeatElim { rule: r1 }, Term::DefeatElim { rule: r2 }) => structural_eq(r1, r2),

        (Term::Lift0 { time: t1 }, Term::Lift0 { time: t2 }) => structural_eq(t1, t2),

        (
            Term::Derive1 {
                time: t1,
                witness: w1,
            },
            Term::Derive1 {
                time: t2,
                witness: w2,
            },
        ) => structural_eq(t1, t2) && structural_eq(w1, w2),

        (Term::ModalAt { time: t1, body: b1 }, Term::ModalAt { time: t2, body: b2 }) => {
            t1 == t2 && structural_eq(b1, b2)
        }

        (
            Term::ModalIntro {
                tribunal: t1,
                body: b1,
            },
            Term::ModalIntro {
                tribunal: t2,
                body: b2,
            },
        ) => t1 == t2 && structural_eq(b1, b2),

        (
            Term::ModalElim {
                from_tribunal: f1,
                to_tribunal: t1,
                term: te1,
                witness: w1,
            },
            Term::ModalElim {
                from_tribunal: f2,
                to_tribunal: t2,
                term: te2,
                witness: w2,
            },
        ) => f1 == f2 && t1 == t2 && structural_eq(te1, te2) && structural_eq(w1, w2),

        (
            Term::Unlock {
                effect_row: e1,
                body: b1,
            },
            Term::Unlock {
                effect_row: e2,
                body: b2,
            },
        ) => structural_eq(e1, e2) && structural_eq(b1, b2),

        // For complex wrapped types, delegate to PartialEq
        (Term::Defeasible(d1), Term::Defeasible(d2)) => d1 == d2,
        (Term::Hole(h1), Term::Hole(h2)) => h1 == h2,
        (Term::HoleFill { .. }, Term::HoleFill { .. }) => a == b,
        (Term::PrincipleBalance(p1), Term::PrincipleBalance(p2)) => p1 == p2,
        (Term::ModalEventually { .. }, Term::ModalEventually { .. }) => a == b,
        (Term::ModalAlways { .. }, Term::ModalAlways { .. }) => a == b,

        _ => false,
    }
}

fn branch_structural_eq(a: &Branch, b: &Branch) -> bool {
    let pat_eq = match (&a.pattern, &b.pattern) {
        (
            Pattern::Constructor {
                constructor: c1,
                binders: b1,
            },
            Pattern::Constructor {
                constructor: c2,
                binders: b2,
            },
        ) => c1 == c2 && b1.len() == b2.len(),
        (Pattern::Wildcard, Pattern::Wildcard) => true,
        _ => false,
    };
    pat_eq && structural_eq(&a.body, &b.body)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Branch, Constructor, Ident, Pattern, QualIdent, Sort, Term};

    fn prop() -> Term {
        Term::Sort(Sort::Prop)
    }

    // Helper: create a Var with a dummy index (will be overwritten by assign_indices).
    fn named_var(name: &str) -> Term {
        Term::Var {
            name: Ident::new(name),
            index: 0,
        }
    }

    fn indexed_var(name: &str, idx: u32) -> Term {
        Term::Var {
            name: Ident::new(name),
            index: idx,
        }
    }

    fn lam(name: &str, domain: Term, body: Term) -> Term {
        Term::Lambda {
            binder: Ident::new(name),
            domain: Box::new(domain),
            body: Box::new(body),
        }
    }

    fn pi(name: &str, domain: Term, codomain: Term) -> Term {
        Term::Pi {
            binder: Ident::new(name),
            domain: Box::new(domain),
            effect_row: None,
            codomain: Box::new(codomain),
        }
    }

    fn let_in(name: &str, ty: Term, val: Term, body: Term) -> Term {
        Term::Let {
            binder: Ident::new(name),
            ty: Box::new(ty),
            val: Box::new(val),
            body: Box::new(body),
        }
    }

    fn sigma(name: &str, fst_ty: Term, snd_ty: Term) -> Term {
        Term::Sigma {
            binder: Ident::new(name),
            fst_ty: Box::new(fst_ty),
            snd_ty: Box::new(snd_ty),
        }
    }

    fn rec(name: &str, ty: Term, body: Term) -> Term {
        Term::Rec {
            binder: Ident::new(name),
            ty: Box::new(ty),
            body: Box::new(body),
        }
    }

    // ── Test 1: simple binding (λx.x gets index 0) ──────────────────

    #[test]
    fn simple_lambda_identity() {
        let term = lam("x", prop(), named_var("x"));
        let result = assign_indices(&term).unwrap();
        match &result {
            Term::Lambda { body, .. } => {
                assert_eq!(**body, indexed_var("x", 0));
            }
            _ => panic!("expected Lambda"),
        }
    }

    // ── Test 2: nested binding (λx.λy.x gets index 1) ───────────────

    #[test]
    fn nested_lambda_outer_ref() {
        let term = lam("x", prop(), lam("y", prop(), named_var("x")));
        let result = assign_indices(&term).unwrap();
        match &result {
            Term::Lambda {
                body: outer_body, ..
            } => match outer_body.as_ref() {
                Term::Lambda {
                    body: inner_body, ..
                } => {
                    assert_eq!(**inner_body, indexed_var("x", 1));
                }
                _ => panic!("expected inner Lambda"),
            },
            _ => panic!("expected outer Lambda"),
        }
    }

    // ── Test 3: free variable detection ──────────────────────────────

    #[test]
    fn unbound_variable_error() {
        let term = lam("x", prop(), named_var("y"));
        let err = assign_indices(&term).unwrap_err();
        assert_eq!(
            err,
            DebruijnError::Unbound {
                name: "y".to_string()
            }
        );
    }

    // ── Test 4: alpha equality (λx.x == λy.y) ───────────────────────

    #[test]
    fn alpha_equal_identity_functions() {
        let t1 = lam("x", prop(), named_var("x"));
        let t2 = lam("y", prop(), named_var("y"));
        assert!(alpha_equal(&t1, &t2));
    }

    #[test]
    fn alpha_not_equal_different_structure() {
        let t1 = lam("x", prop(), named_var("x"));
        let t2 = lam("x", prop(), lam("y", prop(), named_var("y")));
        assert!(!alpha_equal(&t1, &t2));
    }

    // ── Test 5: shift preserves bound variables ──────────────────────

    #[test]
    fn shift_preserves_bound() {
        // λ(x : Prop). x@0 — shifting by +10 at cutoff 0 should NOT
        // affect the bound variable (index 0 < cutoff=1 inside the binder).
        let term = Term::Lambda {
            binder: Ident::new("x"),
            domain: Box::new(prop()),
            body: Box::new(indexed_var("x", 0)),
        };
        let shifted = shift(&term, 0, 10).unwrap();
        match &shifted {
            Term::Lambda { body, .. } => {
                assert_eq!(**body, indexed_var("x", 0));
            }
            _ => panic!("expected Lambda"),
        }
    }

    #[test]
    fn shift_increments_free() {
        let term = indexed_var("free", 0);
        let shifted = shift(&term, 0, 5).unwrap();
        assert_eq!(shifted, indexed_var("free", 5));
    }

    // ── Test 6: substitution basic case ──────────────────────────────

    #[test]
    fn substitute_basic() {
        let term = indexed_var("x", 0);
        let result = substitute(&term, 0, &prop()).unwrap();
        assert_eq!(result, prop());
    }

    // ── Test 7: substitution under binder (capture avoidance) ────────

    #[test]
    fn substitute_under_binder_capture_avoidance() {
        // λ(y : Prop). x@1 — subst [0 := z@0]:
        // Under the binder, target becomes 1, replacement z@0 is shifted to z@1.
        // x@1 matches target 1 → z@1.
        let term = Term::Lambda {
            binder: Ident::new("y"),
            domain: Box::new(prop()),
            body: Box::new(indexed_var("x", 1)),
        };
        let replacement = indexed_var("z", 0);
        let result = substitute(&term, 0, &replacement).unwrap();
        match &result {
            Term::Lambda { body, .. } => {
                assert_eq!(**body, indexed_var("z", 1));
            }
            _ => panic!("expected Lambda"),
        }
    }

    // ── Test 8: let binding assigns index ────────────────────────────

    #[test]
    fn let_binding_assigns_index() {
        let term = let_in("x", prop(), prop(), named_var("x"));
        let result = assign_indices(&term).unwrap();
        match &result {
            Term::Let { body, .. } => {
                assert_eq!(**body, indexed_var("x", 0));
            }
            _ => panic!("expected Let"),
        }
    }

    // ── Test 9: match pattern binding ────────────────────────────────

    #[test]
    fn match_pattern_binds_variables() {
        // match e return P with | C a b ⇒ a
        // "a" pushed first, "b" second → "b" at index 0, "a" at index 1.
        let term = lam(
            "e",
            prop(),
            Term::Match {
                scrutinee: Box::new(named_var("e")),
                return_ty: Box::new(prop()),
                branches: vec![Branch {
                    pattern: Pattern::Constructor {
                        constructor: Constructor::new(QualIdent::simple("C")),
                        binders: vec![Ident::new("a"), Ident::new("b")],
                    },
                    body: named_var("a"),
                }],
            },
        );
        let result = assign_indices(&term).unwrap();
        match &result {
            Term::Lambda { body: lam_body, .. } => match lam_body.as_ref() {
                Term::Match { branches, .. } => {
                    assert_eq!(branches[0].body, indexed_var("a", 1));
                }
                _ => panic!("expected Match"),
            },
            _ => panic!("expected Lambda"),
        }
    }

    // ── Test 10: Pi binder in domain vs codomain ─────────────────────

    #[test]
    fn pi_binder_domain_vs_codomain() {
        // Π(x : Prop). x — binder not in scope in domain, IS in scope in codomain.
        let term = pi("x", prop(), named_var("x"));
        let result = assign_indices(&term).unwrap();
        match &result {
            Term::Pi {
                domain, codomain, ..
            } => {
                assert_eq!(**domain, prop());
                assert_eq!(**codomain, indexed_var("x", 0));
            }
            _ => panic!("expected Pi"),
        }
    }

    // ── Test 11: Pi domain cannot see its own binder ─────────────────

    #[test]
    fn pi_domain_cannot_see_own_binder() {
        let term = pi("x", named_var("x"), prop());
        let err = assign_indices(&term).unwrap_err();
        assert_eq!(
            err,
            DebruijnError::Unbound {
                name: "x".to_string()
            }
        );
    }

    // ── Test 12: rec (fix) binder in scope in body ───────────────────

    #[test]
    fn rec_binder_in_body() {
        let term = rec("f", prop(), named_var("f"));
        let result = assign_indices(&term).unwrap();
        match &result {
            Term::Rec { body, .. } => {
                assert_eq!(**body, indexed_var("f", 0));
            }
            _ => panic!("expected Rec"),
        }
    }

    // ── Test 13: shadowing — inner binder shadows outer ──────────────

    #[test]
    fn binder_shadowing() {
        let term = lam("x", prop(), lam("x", prop(), named_var("x")));
        let result = assign_indices(&term).unwrap();
        match &result {
            Term::Lambda { body: outer, .. } => match outer.as_ref() {
                Term::Lambda { body: inner, .. } => {
                    assert_eq!(**inner, indexed_var("x", 0));
                }
                _ => panic!("expected inner Lambda"),
            },
            _ => panic!("expected outer Lambda"),
        }
    }

    // ── Test 14: alpha equality across nested lambdas ────────────────

    #[test]
    fn alpha_equal_nested_different_names() {
        let t1 = lam("a", prop(), lam("b", prop(), named_var("a")));
        let t2 = lam("x", prop(), lam("y", prop(), named_var("x")));
        assert!(alpha_equal(&t1, &t2));
    }

    // ── Test 15: shift literal unchanged ─────────────────────────────

    #[test]
    fn shift_constant_unchanged() {
        let term = Term::Constant(QualIdent::simple("Nat"));
        let shifted = shift(&term, 0, 100).unwrap();
        assert_eq!(shifted, Term::Constant(QualIdent::simple("Nat")));
    }

    // ── Test 16: substitute non-matching index ───────────────────────

    #[test]
    fn substitute_non_matching() {
        let term = indexed_var("x", 0);
        let result = substitute(&term, 1, &prop()).unwrap();
        assert_eq!(result, indexed_var("x", 0));
    }

    // ── Test 17: DebruijnError display ───────────────────────────────

    #[test]
    fn error_display() {
        let err = DebruijnError::Unbound {
            name: "foo".to_string(),
        };
        assert_eq!(err.to_string(), "unbound variable: foo");
    }

    // ── Test 18: sigma binder scoping ────────────────────────────────

    #[test]
    fn sigma_binder_scoping() {
        let term = sigma("x", prop(), named_var("x"));
        let result = assign_indices(&term).unwrap();
        match &result {
            Term::Sigma { snd_ty, .. } => {
                assert_eq!(**snd_ty, indexed_var("x", 0));
            }
            _ => panic!("expected Sigma"),
        }
    }
}
