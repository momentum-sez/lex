use super::{boxed_error, TypeError, MAX_DEPTH};
use crate::ast::{Effect, EffectRow, Level, ScopeField, Sort, Term, TimeTerm};

enum Node<'a> {
    Term(&'a Term),
    Level(&'a Level),
    Row(&'a EffectRow),
    Time(&'a TimeTerm),
}

/// Bound every recursive payload before context validation can clone a diagnostic.
pub(super) fn check(term: &Term) -> Result<(), Box<TypeError>> {
    let mut pending = vec![(Node::Term(term), 0)];
    while let Some((node, depth)) = pending.pop() {
        if depth > MAX_DEPTH {
            return Err(boxed_error(|| TypeError::RecursionLimitExceeded));
        }
        let mut push = |node| pending.push((node, depth + 1));
        match node {
            Node::Level(level) => match level {
                Level::Nat(_) | Level::Var(_) => {}
                Level::Succ(base, _) => push(Node::Level(base)),
                Level::Max(left, right) => {
                    push(Node::Level(left));
                    push(Node::Level(right));
                }
            },
            Node::Row(row) => match row {
                EffectRow::Empty | EffectRow::Var(_) => {}
                EffectRow::Join(left, right) => {
                    push(Node::Row(left));
                    push(Node::Row(right));
                }
                EffectRow::BranchSensitive(row) => push(Node::Row(row)),
                EffectRow::Effects(effects) => {
                    for effect in effects {
                        match effect {
                            Effect::Write(term) => push(Node::Term(term)),
                            Effect::Fuel(level, _) => push(Node::Level(level)),
                            Effect::Read
                            | Effect::Attest(_)
                            | Effect::Authority(_)
                            | Effect::Oracle(_)
                            | Effect::SanctionsQuery
                            | Effect::Discretion(_) => {}
                        }
                    }
                }
            },
            Node::Time(time) => match time {
                TimeTerm::Literal(_) | TimeTerm::Var { .. } => {}
                TimeTerm::AsOf0(term) | TimeTerm::AsOf1(term) => push(Node::Term(term)),
                TimeTerm::Lift0(time) => push(Node::Time(time)),
                TimeTerm::Derive1 { time, witness } => {
                    push(Node::Time(time));
                    push(Node::Term(&witness.term));
                }
            },
            Node::Term(term) => match term {
                Term::Var { .. }
                | Term::Constant(_)
                | Term::ContentRefTerm(_)
                | Term::IntLit(_)
                | Term::RatLit(_, _)
                | Term::StringLit(_)
                | Term::AxiomUse { .. } => {}
                Term::Sort(sort) => match sort {
                    Sort::Type(level) | Sort::Rule(level) => push(Node::Level(level)),
                    Sort::Prop | Sort::Time0 | Sort::Time1 => {}
                },
                Term::Pair { fst, snd }
                | Term::App {
                    func: fst,
                    arg: snd,
                }
                | Term::Derive1 {
                    time: fst,
                    witness: snd,
                }
                | Term::Lambda {
                    domain: fst,
                    body: snd,
                    ..
                }
                | Term::Sigma {
                    fst_ty: fst,
                    snd_ty: snd,
                    ..
                }
                | Term::Annot { term: fst, ty: snd }
                | Term::Rec {
                    ty: fst, body: snd, ..
                }
                | Term::ModalElim {
                    term: fst,
                    witness: snd,
                    ..
                }
                | Term::HoleFill {
                    filler: fst,
                    pcauth: snd,
                    ..
                }
                | Term::Unlock {
                    effect_row: fst,
                    body: snd,
                } => {
                    push(Node::Term(fst));
                    push(Node::Term(snd));
                }
                Term::Proj { pair: body, .. }
                | Term::SanctionsDominance { proof: body }
                | Term::DefeatElim { rule: body }
                | Term::Lift0 { time: body }
                | Term::ModalIntro { body, .. } => push(Node::Term(body)),
                Term::InductiveIntro { args, .. } => {
                    for arg in args {
                        push(Node::Term(arg));
                    }
                }
                Term::Pi {
                    domain,
                    effect_row,
                    codomain,
                    ..
                } => {
                    push(Node::Term(domain));
                    push(Node::Term(codomain));
                    if let Some(row) = effect_row {
                        push(Node::Row(row));
                    }
                }
                Term::Let { ty, val, body, .. } => {
                    push(Node::Term(ty));
                    push(Node::Term(val));
                    push(Node::Term(body));
                }
                Term::Match {
                    scrutinee,
                    return_ty,
                    branches,
                } => {
                    push(Node::Term(scrutinee));
                    push(Node::Term(return_ty));
                    for branch in branches {
                        push(Node::Term(&branch.body));
                    }
                }
                Term::ModalAt { time, body } | Term::ModalEventually { time, body } => {
                    push(Node::Time(time));
                    push(Node::Term(body));
                }
                Term::ModalAlways { from, to, body } => {
                    push(Node::Time(from));
                    push(Node::Time(to));
                    push(Node::Term(body));
                }
                Term::Defeasible(rule) => {
                    push(Node::Term(&rule.base_ty));
                    push(Node::Term(&rule.base_body));
                    for exception in &rule.exceptions {
                        push(Node::Term(&exception.guard));
                        push(Node::Term(&exception.body));
                    }
                }
                Term::Hole(hole) => {
                    push(Node::Term(&hole.ty));
                    if let Some(scope) = &hole.scope {
                        for field in &scope.fields {
                            match field {
                                ScopeField::Corridor(_) | ScopeField::Jurisdiction(_) => {}
                                ScopeField::TimeWindow { from, to } => {
                                    push(Node::Time(from));
                                    push(Node::Time(to));
                                }
                                ScopeField::EntityClass(term) => push(Node::Term(term)),
                            }
                        }
                    }
                }
                Term::PrincipleBalance(step) => {
                    push(Node::Term(&step.verdict));
                    push(Node::Term(&step.rationale));
                }
            },
        }
    }
    Ok(())
}
