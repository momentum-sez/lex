//! Surface Lex to Core Lex elaboration.
//!
//! Elaboration performs two steps:
//! 1. resolve surface-level global names against the compliance prelude;
//! 2. assign De Bruijn indices to the remaining local variables.

use std::fmt;

use crate::ast::{
    Branch, Constructor, DefeasibleRule, Effect, EffectRow, Exception, Hole, Pattern,
    PrincipleBalancingStep, QualIdent, RewriteWitness, ScopeConstraint, ScopeField, Term,
    TimeTerm,
};
use crate::debruijn;
use crate::typecheck::Context;

/// Errors raised while elaborating surface syntax into Core Lex.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElaborationError {
    /// Human-readable error message.
    pub message: String,
}

impl ElaborationError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for ElaborationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for ElaborationError {}

/// Elaborate a surface term into Core Lex.
pub fn elaborate(term: &Term, prelude: &Context) -> Result<Term, ElaborationError> {
    let resolved = resolve_names(term, prelude)?;
    debruijn::assign_indices(&resolved)
        .map_err(|err| ElaborationError::new(format!("de Bruijn assignment failed: {err}")))
}

fn resolve_names(term: &Term, prelude: &Context) -> Result<Term, ElaborationError> {
    resolve_names_inner(term, prelude, &[])
}

fn resolve_names_inner(
    term: &Term,
    prelude: &Context,
    locals: &[String],
) -> Result<Term, ElaborationError> {
    match term {
        Term::Var { name, index } => {
            if locals.iter().rev().any(|local| local == &name.name) {
                Ok(Term::Var {
                    name: name.clone(),
                    index: *index,
                })
            } else if *index == 0 && prelude.lookup_named_constant(&name.name).is_some() {
                Ok(Term::Constant(QualIdent::simple(&name.name)))
            } else {
                Ok(Term::Var {
                    name: name.clone(),
                    index: *index,
                })
            }
        }
        Term::Sort(sort) => Ok(Term::Sort(sort.clone())),
        Term::Constant(name) => Ok(Term::Constant(resolve_global(name, prelude, "constant")?)),
        Term::ContentRefTerm(content) => Ok(Term::ContentRefTerm(content.clone())),
        Term::IntLit(value) => Ok(Term::IntLit(*value)),
        Term::RatLit(numerator, denominator) => Ok(Term::RatLit(*numerator, *denominator)),
        Term::StringLit(value) => Ok(Term::StringLit(value.clone())),
        Term::AxiomUse { axiom } => Ok(Term::AxiomUse {
            axiom: axiom.clone(),
        }),
        Term::Pair { fst, snd } => Ok(Term::Pair {
            fst: Box::new(resolve_names_inner(fst, prelude, locals)?),
            snd: Box::new(resolve_names_inner(snd, prelude, locals)?),
        }),
        Term::Proj { first, pair } => Ok(Term::Proj {
            first: *first,
            pair: Box::new(resolve_names_inner(pair, prelude, locals)?),
        }),
        Term::App { func, arg } => Ok(Term::App {
            func: Box::new(resolve_names_inner(func, prelude, locals)?),
            arg: Box::new(resolve_names_inner(arg, prelude, locals)?),
        }),
        Term::InductiveIntro { constructor, args } => Ok(Term::InductiveIntro {
            constructor: resolve_constructor(constructor, prelude)?,
            args: args
                .iter()
                .map(|arg| resolve_names_inner(arg, prelude, locals))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        Term::SanctionsDominance { proof } => Ok(Term::SanctionsDominance {
            proof: Box::new(resolve_names_inner(proof, prelude, locals)?),
        }),
        Term::DefeatElim { rule } => Ok(Term::DefeatElim {
            rule: Box::new(resolve_names_inner(rule, prelude, locals)?),
        }),
        Term::Lift0 { time } => Ok(Term::Lift0 {
            time: Box::new(resolve_names_inner(time, prelude, locals)?),
        }),
        Term::Derive1 { time, witness } => Ok(Term::Derive1 {
            time: Box::new(resolve_names_inner(time, prelude, locals)?),
            witness: Box::new(resolve_names_inner(witness, prelude, locals)?),
        }),
        Term::Lambda {
            binder,
            domain,
            body,
        } => {
            let body_locals = locals_with(locals, &binder.name);
            Ok(Term::Lambda {
                binder: binder.clone(),
                domain: Box::new(resolve_names_inner(domain, prelude, locals)?),
                body: Box::new(resolve_names_inner(body, prelude, &body_locals)?),
            })
        }
        Term::Pi {
            binder,
            domain,
            effect_row,
            codomain,
        } => {
            let codomain_locals = locals_with(locals, &binder.name);
            Ok(Term::Pi {
                binder: binder.clone(),
                domain: Box::new(resolve_names_inner(domain, prelude, locals)?),
                effect_row: effect_row
                    .as_ref()
                    .map(|row| resolve_effect_row(row, prelude, locals))
                    .transpose()?,
                codomain: Box::new(resolve_names_inner(codomain, prelude, &codomain_locals)?),
            })
        }
        Term::Sigma {
            binder,
            fst_ty,
            snd_ty,
        } => {
            let snd_locals = locals_with(locals, &binder.name);
            Ok(Term::Sigma {
                binder: binder.clone(),
                fst_ty: Box::new(resolve_names_inner(fst_ty, prelude, locals)?),
                snd_ty: Box::new(resolve_names_inner(snd_ty, prelude, &snd_locals)?),
            })
        }
        Term::Annot { term, ty } => Ok(Term::Annot {
            term: Box::new(resolve_names_inner(term, prelude, locals)?),
            ty: Box::new(resolve_names_inner(ty, prelude, locals)?),
        }),
        Term::Let {
            binder,
            ty,
            val,
            body,
        } => {
            let body_locals = locals_with(locals, &binder.name);
            Ok(Term::Let {
                binder: binder.clone(),
                ty: Box::new(resolve_names_inner(ty, prelude, locals)?),
                val: Box::new(resolve_names_inner(val, prelude, locals)?),
                body: Box::new(resolve_names_inner(body, prelude, &body_locals)?),
            })
        }
        Term::Match {
            scrutinee,
            return_ty,
            branches,
        } => Ok(Term::Match {
            scrutinee: Box::new(resolve_names_inner(scrutinee, prelude, locals)?),
            return_ty: Box::new(resolve_names_inner(return_ty, prelude, locals)?),
            branches: branches
                .iter()
                .map(|branch| resolve_branch(branch, prelude, locals))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        Term::Rec { binder, ty, body } => {
            let body_locals = locals_with(locals, &binder.name);
            Ok(Term::Rec {
                binder: binder.clone(),
                ty: Box::new(resolve_names_inner(ty, prelude, locals)?),
                body: Box::new(resolve_names_inner(body, prelude, &body_locals)?),
            })
        }
        Term::ModalAt { time, body } => Ok(Term::ModalAt {
            time: resolve_time_term(time, prelude, locals)?,
            body: Box::new(resolve_names_inner(body, prelude, locals)?),
        }),
        Term::ModalEventually { time, body } => Ok(Term::ModalEventually {
            time: resolve_time_term(time, prelude, locals)?,
            body: Box::new(resolve_names_inner(body, prelude, locals)?),
        }),
        Term::ModalAlways { from, to, body } => Ok(Term::ModalAlways {
            from: resolve_time_term(from, prelude, locals)?,
            to: resolve_time_term(to, prelude, locals)?,
            body: Box::new(resolve_names_inner(body, prelude, locals)?),
        }),
        Term::ModalIntro { tribunal, body } => Ok(Term::ModalIntro {
            tribunal: tribunal.clone(),
            body: Box::new(resolve_names_inner(body, prelude, locals)?),
        }),
        Term::ModalElim {
            from_tribunal,
            to_tribunal,
            term,
            witness,
        } => Ok(Term::ModalElim {
            from_tribunal: from_tribunal.clone(),
            to_tribunal: to_tribunal.clone(),
            term: Box::new(resolve_names_inner(term, prelude, locals)?),
            witness: Box::new(resolve_names_inner(witness, prelude, locals)?),
        }),
        Term::Defeasible(rule) => Ok(Term::Defeasible(DefeasibleRule {
            name: rule.name.clone(),
            base_ty: Box::new(resolve_names_inner(&rule.base_ty, prelude, locals)?),
            base_body: Box::new(resolve_names_inner(&rule.base_body, prelude, locals)?),
            exceptions: rule
                .exceptions
                .iter()
                .map(|exception| resolve_exception(exception, prelude, locals))
                .collect::<Result<Vec<_>, _>>()?,
            lattice: rule.lattice.clone(),
        })),
        Term::Hole(hole) => Ok(Term::Hole(Hole {
            name: hole.name.clone(),
            ty: Box::new(resolve_names_inner(&hole.ty, prelude, locals)?),
            authority: hole.authority.clone(),
            scope: hole
                .scope
                .as_ref()
                .map(|scope| resolve_scope_constraint(scope, prelude, locals))
                .transpose()?,
        })),
        Term::HoleFill {
            hole_name,
            filler,
            pcauth,
        } => Ok(Term::HoleFill {
            hole_name: hole_name.clone(),
            filler: Box::new(resolve_names_inner(filler, prelude, locals)?),
            pcauth: Box::new(resolve_names_inner(pcauth, prelude, locals)?),
        }),
        Term::PrincipleBalance(balance) => Ok(Term::PrincipleBalance(
            PrincipleBalancingStep {
                principles: balance.principles.clone(),
                precedents: balance.precedents.clone(),
                verdict: Box::new(resolve_names_inner(&balance.verdict, prelude, locals)?),
                rationale: Box::new(resolve_names_inner(&balance.rationale, prelude, locals)?),
            },
        )),
        Term::Unlock { effect_row, body } => Ok(Term::Unlock {
            effect_row: Box::new(resolve_names_inner(effect_row, prelude, locals)?),
            body: Box::new(resolve_names_inner(body, prelude, locals)?),
        }),
    }
}

fn resolve_branch(
    branch: &Branch,
    prelude: &Context,
    locals: &[String],
) -> Result<Branch, ElaborationError> {
    match &branch.pattern {
        Pattern::Constructor {
            constructor,
            binders,
        } => {
            let branch_locals = locals_with_many(locals, binders.iter().map(|binder| binder.name.clone()));
            Ok(Branch {
                pattern: Pattern::Constructor {
                    constructor: resolve_constructor(constructor, prelude)?,
                    binders: binders.clone(),
                },
                body: resolve_names_inner(&branch.body, prelude, &branch_locals)?,
            })
        }
        Pattern::Wildcard => Ok(Branch {
            pattern: Pattern::Wildcard,
            body: resolve_names_inner(&branch.body, prelude, locals)?,
        }),
    }
}

fn resolve_exception(
    exception: &Exception,
    prelude: &Context,
    locals: &[String],
) -> Result<Exception, ElaborationError> {
    Ok(Exception {
        guard: Box::new(resolve_names_inner(&exception.guard, prelude, locals)?),
        body: Box::new(resolve_names_inner(&exception.body, prelude, locals)?),
        priority: exception.priority,
        authority: exception.authority.clone(),
    })
}

fn resolve_effect_row(
    row: &EffectRow,
    prelude: &Context,
    locals: &[String],
) -> Result<EffectRow, ElaborationError> {
    match row {
        EffectRow::Empty => Ok(EffectRow::Empty),
        EffectRow::Effects(effects) => Ok(EffectRow::Effects(
            effects
                .iter()
                .map(|effect| resolve_effect(effect, prelude, locals))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        EffectRow::Var(index) => Ok(EffectRow::Var(*index)),
        EffectRow::Join(left, right) => Ok(EffectRow::Join(
            Box::new(resolve_effect_row(left, prelude, locals)?),
            Box::new(resolve_effect_row(right, prelude, locals)?),
        )),
        EffectRow::BranchSensitive(inner) => Ok(EffectRow::BranchSensitive(Box::new(
            resolve_effect_row(inner, prelude, locals)?,
        ))),
    }
}

fn resolve_effect(
    effect: &Effect,
    prelude: &Context,
    locals: &[String],
) -> Result<Effect, ElaborationError> {
    match effect {
        Effect::Read => Ok(Effect::Read),
        Effect::Write(scope) => Ok(Effect::Write(Box::new(resolve_names_inner(
            scope, prelude, locals,
        )?))),
        Effect::Attest(authority) => Ok(Effect::Attest(authority.clone())),
        Effect::Authority(authority) => Ok(Effect::Authority(authority.clone())),
        Effect::Oracle(oracle) => Ok(Effect::Oracle(oracle.clone())),
        Effect::Fuel(level, amount) => Ok(Effect::Fuel(level.clone(), *amount)),
        Effect::SanctionsQuery => Ok(Effect::SanctionsQuery),
        Effect::Discretion(authority) => Ok(Effect::Discretion(authority.clone())),
    }
}

fn resolve_time_term(
    time: &TimeTerm,
    prelude: &Context,
    locals: &[String],
) -> Result<TimeTerm, ElaborationError> {
    match time {
        TimeTerm::Literal(literal) => Ok(TimeTerm::Literal(literal.clone())),
        TimeTerm::Var { name, index } => Ok(TimeTerm::Var {
            name: name.clone(),
            index: *index,
        }),
        TimeTerm::AsOf0(term) => Ok(TimeTerm::AsOf0(Box::new(resolve_names_inner(
            term, prelude, locals,
        )?))),
        TimeTerm::AsOf1(term) => Ok(TimeTerm::AsOf1(Box::new(resolve_names_inner(
            term, prelude, locals,
        )?))),
        TimeTerm::Lift0(inner) => Ok(TimeTerm::Lift0(Box::new(resolve_time_term(
            inner, prelude, locals,
        )?))),
        TimeTerm::Derive1 { time, witness } => Ok(TimeTerm::Derive1 {
            time: Box::new(resolve_time_term(time, prelude, locals)?),
            witness: RewriteWitness {
                term: Box::new(resolve_names_inner(&witness.term, prelude, locals)?),
            },
        }),
    }
}

fn resolve_scope_constraint(
    scope: &ScopeConstraint,
    prelude: &Context,
    locals: &[String],
) -> Result<ScopeConstraint, ElaborationError> {
    Ok(ScopeConstraint {
        fields: scope
            .fields
            .iter()
            .map(|field| resolve_scope_field(field, prelude, locals))
            .collect::<Result<Vec<_>, _>>()?,
    })
}

fn resolve_scope_field(
    field: &ScopeField,
    prelude: &Context,
    locals: &[String],
) -> Result<ScopeField, ElaborationError> {
    match field {
        ScopeField::Corridor(name) => Ok(ScopeField::Corridor(name.clone())),
        ScopeField::TimeWindow { from, to } => Ok(ScopeField::TimeWindow {
            from: resolve_time_term(from, prelude, locals)?,
            to: resolve_time_term(to, prelude, locals)?,
        }),
        ScopeField::Jurisdiction(name) => Ok(ScopeField::Jurisdiction(name.clone())),
        ScopeField::EntityClass(term) => Ok(ScopeField::EntityClass(Box::new(
            resolve_names_inner(term, prelude, locals)?,
        ))),
    }
}

fn resolve_constructor(
    constructor: &Constructor,
    prelude: &Context,
) -> Result<Constructor, ElaborationError> {
    Ok(Constructor::new(resolve_global(
        &constructor.name,
        prelude,
        "constructor",
    )?))
}

fn resolve_global(
    name: &QualIdent,
    prelude: &Context,
    kind: &str,
) -> Result<QualIdent, ElaborationError> {
    if prelude.lookup_constant(name).is_some() {
        Ok(name.clone())
    } else {
        Err(ElaborationError::new(format!(
            "unknown {kind}: {}",
            display_qual_ident(name)
        )))
    }
}

fn display_qual_ident(name: &QualIdent) -> String {
    name.segments.join(".")
}

fn locals_with(locals: &[String], name: &str) -> Vec<String> {
    locals_with_many(locals, [name.to_owned()])
}

fn locals_with_many(
    locals: &[String],
    names: impl IntoIterator<Item = String>,
) -> Vec<String> {
    let mut extended = locals.to_vec();
    extended.extend(names);
    extended
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{
        AuthorityRef, Blake3Hash, Branch, ContentRef, DefeasibleRule, Effect, EffectRow, Ident,
        Pattern, QualIdent, ScopeConstraint, ScopeField, Term, TimeLiteral, TimeTerm,
    };
    use crate::prelude::compliance_prelude;

    fn surface(name: &str) -> Term {
        Term::Var {
            name: Ident::new(name),
            index: 0,
        }
    }

    fn indexed(name: &str, index: u32) -> Term {
        Term::Var {
            name: Ident::new(name),
            index,
        }
    }

    fn constant(name: &str) -> Term {
        Term::constant(name)
    }

    fn app(func: Term, arg: Term) -> Term {
        Term::app(func, arg)
    }

    fn lam(name: &str, domain: Term, body: Term) -> Term {
        Term::lam(name, domain, body)
    }

    fn pi(name: &str, domain: Term, codomain: Term) -> Term {
        Term::pi(name, domain, codomain)
    }

    fn match_expr(scrutinee: Term, return_ty: Term, branches: Vec<Branch>) -> Term {
        Term::match_expr(scrutinee, return_ty, branches)
    }

    fn branch(ctor_name: &str, binders: &[&str], body: Term) -> Branch {
        Branch {
            pattern: Pattern::Constructor {
                constructor: Constructor::new(QualIdent::simple(ctor_name)),
                binders: binders.iter().map(|name| Ident::new(name)).collect(),
            },
            body,
        }
    }

    fn wildcard_branch(body: Term) -> Branch {
        Branch {
            pattern: Pattern::Wildcard,
            body,
        }
    }

    fn defeasible(name: &str, ty: Term, body: Term, exceptions: Vec<Exception>) -> Term {
        Term::Defeasible(DefeasibleRule {
            name: Ident::new(name),
            base_ty: Box::new(ty),
            base_body: Box::new(body),
            exceptions,
            lattice: None,
        })
    }

    fn prelude() -> Context {
        compliance_prelude()
    }

    #[test]
    fn elaborates_ibc_s66_minimum_directors_rule() {
        let rule = defeasible(
            "min_directors",
            pi("ctx", surface("IncorporationContext"), surface("ComplianceVerdict")),
            lam(
                "ctx",
                surface("IncorporationContext"),
                match_expr(
                    app(surface("director_count"), surface("ctx")),
                    surface("ComplianceVerdict"),
                    vec![
                        branch("Zero", &[], surface("NonCompliant")),
                        wildcard_branch(surface("Compliant")),
                    ],
                ),
            ),
            vec![],
        );

        let elaborated = elaborate(&rule, &prelude()).unwrap();

        assert_eq!(
            elaborated,
            defeasible(
                "min_directors",
                pi(
                    "ctx",
                    constant("IncorporationContext"),
                    constant("ComplianceVerdict")
                ),
                lam(
                    "ctx",
                    constant("IncorporationContext"),
                    match_expr(
                        app(constant("director_count"), indexed("ctx", 0)),
                        constant("ComplianceVerdict"),
                        vec![
                            branch("Zero", &[], constant("NonCompliant")),
                            wildcard_branch(constant("Compliant")),
                        ],
                    ),
                ),
                vec![],
            )
        );
    }

    #[test]
    fn elaborates_ibc_s92_registered_agent_rule() {
        let rule = defeasible(
            "registered_agent",
            pi("ctx", surface("IncorporationContext"), surface("ComplianceVerdict")),
            lam(
                "ctx",
                surface("IncorporationContext"),
                match_expr(
                    app(surface("registered_agent"), surface("ctx")),
                    surface("ComplianceVerdict"),
                    vec![
                        branch("None", &[], surface("NonCompliant")),
                        branch(
                            "Some",
                            &["agent"],
                            match_expr(
                                app(surface("csp_license_status"), surface("agent")),
                                surface("ComplianceVerdict"),
                                vec![
                                    branch("Active", &[], surface("Compliant")),
                                    branch("Suspended", &[], surface("NonCompliant")),
                                    branch("Revoked", &[], surface("NonCompliant")),
                                    wildcard_branch(surface("Pending")),
                                ],
                            ),
                        ),
                    ],
                ),
            ),
            vec![],
        );

        let elaborated = elaborate(&rule, &prelude()).unwrap();

        assert_eq!(
            elaborated,
            defeasible(
                "registered_agent",
                pi(
                    "ctx",
                    constant("IncorporationContext"),
                    constant("ComplianceVerdict")
                ),
                lam(
                    "ctx",
                    constant("IncorporationContext"),
                    match_expr(
                        app(constant("registered_agent"), indexed("ctx", 0)),
                        constant("ComplianceVerdict"),
                        vec![
                            branch("None", &[], constant("NonCompliant")),
                            branch(
                                "Some",
                                &["agent"],
                                match_expr(
                                    app(constant("csp_license_status"), indexed("agent", 0)),
                                    constant("ComplianceVerdict"),
                                    vec![
                                        branch("Active", &[], constant("Compliant")),
                                        branch("Suspended", &[], constant("NonCompliant")),
                                        branch("Revoked", &[], constant("NonCompliant")),
                                        wildcard_branch(constant("Pending")),
                                    ],
                                ),
                            ),
                        ],
                    ),
                ),
                vec![],
            )
        );
    }

    #[test]
    fn elaborates_ibc_s12_name_ending_rule() {
        let rule = defeasible(
            "name_ending",
            pi("ctx", surface("IncorporationContext"), surface("ComplianceVerdict")),
            lam(
                "ctx",
                surface("IncorporationContext"),
                match_expr(
                    app(surface("name_suffix"), surface("ctx")),
                    surface("ComplianceVerdict"),
                    vec![
                        branch("IBC", &[], surface("Compliant")),
                        branch("Limited", &[], surface("Compliant")),
                        branch("Ltd", &[], surface("Compliant")),
                        wildcard_branch(surface("NonCompliant")),
                    ],
                ),
            ),
            vec![],
        );

        let elaborated = elaborate(&rule, &prelude()).unwrap();

        assert_eq!(
            elaborated,
            defeasible(
                "name_ending",
                pi(
                    "ctx",
                    constant("IncorporationContext"),
                    constant("ComplianceVerdict")
                ),
                lam(
                    "ctx",
                    constant("IncorporationContext"),
                    match_expr(
                        app(constant("name_suffix"), indexed("ctx", 0)),
                        constant("ComplianceVerdict"),
                        vec![
                            branch("IBC", &[], constant("Compliant")),
                            branch("Limited", &[], constant("Compliant")),
                            branch("Ltd", &[], constant("Compliant")),
                            wildcard_branch(constant("NonCompliant")),
                        ],
                    ),
                ),
                vec![],
            )
        );
    }

    #[test]
    fn elaborates_ibc_s55_registered_office_rule() {
        let rule = defeasible(
            "registered_office_sc",
            pi("ctx", surface("IncorporationContext"), surface("ComplianceVerdict")),
            lam(
                "ctx",
                surface("IncorporationContext"),
                match_expr(
                    app(surface("registered_office_country"), surface("ctx")),
                    surface("ComplianceVerdict"),
                    vec![
                        branch("SC", &[], surface("Compliant")),
                        wildcard_branch(surface("NonCompliant")),
                    ],
                ),
            ),
            vec![],
        );

        let elaborated = elaborate(&rule, &prelude()).unwrap();

        assert_eq!(
            elaborated,
            defeasible(
                "registered_office_sc",
                pi(
                    "ctx",
                    constant("IncorporationContext"),
                    constant("ComplianceVerdict")
                ),
                lam(
                    "ctx",
                    constant("IncorporationContext"),
                    match_expr(
                        app(constant("registered_office_country"), indexed("ctx", 0)),
                        constant("ComplianceVerdict"),
                        vec![
                            branch("SC", &[], constant("Compliant")),
                            wildcard_branch(constant("NonCompliant")),
                        ],
                    ),
                ),
                vec![],
            )
        );
    }

    #[test]
    fn elaborates_ibc_entity_type_restriction_rule() {
        let rule = defeasible(
            "entity_type_restriction",
            pi("ctx", surface("IncorporationContext"), surface("ComplianceVerdict")),
            lam(
                "ctx",
                surface("IncorporationContext"),
                match_expr(
                    app(surface("entity_type"), surface("ctx")),
                    surface("ComplianceVerdict"),
                    vec![
                        branch("IBC", &[], surface("Compliant")),
                        branch("SpecialLicense", &[], surface("Compliant")),
                        branch("ProtectedCell", &[], surface("Compliant")),
                        wildcard_branch(surface("NonCompliant")),
                    ],
                ),
            ),
            vec![],
        );

        let elaborated = elaborate(&rule, &prelude()).unwrap();

        assert_eq!(
            elaborated,
            defeasible(
                "entity_type_restriction",
                pi(
                    "ctx",
                    constant("IncorporationContext"),
                    constant("ComplianceVerdict")
                ),
                lam(
                    "ctx",
                    constant("IncorporationContext"),
                    match_expr(
                        app(constant("entity_type"), indexed("ctx", 0)),
                        constant("ComplianceVerdict"),
                        vec![
                            branch("IBC", &[], constant("Compliant")),
                            branch("SpecialLicense", &[], constant("Compliant")),
                            branch("ProtectedCell", &[], constant("Compliant")),
                            wildcard_branch(constant("NonCompliant")),
                        ],
                    ),
                ),
                vec![],
            )
        );
    }

    #[test]
    fn elaborates_aml_kyc_exception_rule() {
        let rule = defeasible(
            "aml_kyc_identification",
            pi("ctx", surface("IncorporationContext"), surface("ComplianceVerdict")),
            lam(
                "ctx",
                surface("IncorporationContext"),
                match_expr(
                    app(surface("all_parties_identified"), surface("ctx")),
                    surface("ComplianceVerdict"),
                    vec![
                        branch("True", &[], surface("Compliant")),
                        branch("False", &[], surface("NonCompliant")),
                    ],
                ),
            ),
            vec![Exception {
                guard: Box::new(lam(
                    "ctx",
                    surface("IncorporationContext"),
                    app(surface("parent_entity_kyc_compliant"), surface("ctx")),
                )),
                body: Box::new(lam(
                    "ctx",
                    surface("IncorporationContext"),
                    surface("Compliant"),
                )),
                priority: Some(1),
                authority: Some(AuthorityRef::Named(QualIdent::new(
                    ["fsa", "seychelles"].iter().copied(),
                ))),
            }],
        );

        let elaborated = elaborate(&rule, &prelude()).unwrap();

        assert_eq!(
            elaborated,
            defeasible(
                "aml_kyc_identification",
                pi(
                    "ctx",
                    constant("IncorporationContext"),
                    constant("ComplianceVerdict")
                ),
                lam(
                    "ctx",
                    constant("IncorporationContext"),
                    match_expr(
                        app(constant("all_parties_identified"), indexed("ctx", 0)),
                        constant("ComplianceVerdict"),
                        vec![
                            branch("True", &[], constant("Compliant")),
                            branch("False", &[], constant("NonCompliant")),
                        ],
                    ),
                ),
                vec![Exception {
                    guard: Box::new(lam(
                        "ctx",
                        constant("IncorporationContext"),
                        app(constant("parent_entity_kyc_compliant"), indexed("ctx", 0)),
                    )),
                    body: Box::new(lam(
                        "ctx",
                        constant("IncorporationContext"),
                        constant("Compliant"),
                    )),
                    priority: Some(1),
                    authority: Some(AuthorityRef::Named(QualIdent::new(
                        ["fsa", "seychelles"].iter().copied(),
                    ))),
                }],
            )
        );
    }

    #[test]
    fn elaborates_sanctions_screening_let_rule() {
        let rule = lam(
            "ctx",
            surface("IncorporationContext"),
            Term::Let {
                binder: Ident::new("result"),
                ty: Box::new(surface("SanctionsResult")),
                val: Box::new(app(surface("sanctions_check"), surface("ctx"))),
                body: Box::new(match_expr(
                    surface("result"),
                    surface("ComplianceVerdict"),
                    vec![
                        branch("Clear", &[], surface("Compliant")),
                        wildcard_branch(surface("NonCompliant")),
                    ],
                )),
            },
        );

        let elaborated = elaborate(&rule, &prelude()).unwrap();

        assert_eq!(
            elaborated,
            lam(
                "ctx",
                constant("IncorporationContext"),
                Term::Let {
                    binder: Ident::new("result"),
                    ty: Box::new(constant("SanctionsResult")),
                    val: Box::new(app(constant("sanctions_check"), indexed("ctx", 0))),
                    body: Box::new(match_expr(
                        indexed("result", 0),
                        constant("ComplianceVerdict"),
                        vec![
                            branch("Clear", &[], constant("Compliant")),
                            wildcard_branch(constant("NonCompliant")),
                        ],
                    )),
                },
            )
        );
    }

    #[test]
    fn elaborates_beneficial_ownership_rule() {
        let rule = defeasible(
            "ubo_filing",
            pi("ctx", surface("IncorporationContext"), surface("ComplianceVerdict")),
            lam(
                "ctx",
                surface("IncorporationContext"),
                match_expr(
                    app(surface("beneficial_owners"), surface("ctx")),
                    surface("ComplianceVerdict"),
                    vec![
                        branch("Nil", &[], surface("NonCompliant")),
                        branch(
                            "Cons",
                            &["owner", "rest"],
                            match_expr(
                                app(
                                    surface("all_identified"),
                                    app(app(surface("Cons"), surface("owner")), surface("rest")),
                                ),
                                surface("ComplianceVerdict"),
                                vec![
                                    branch("True", &[], surface("Compliant")),
                                    branch("False", &[], surface("Pending")),
                                ],
                            ),
                        ),
                    ],
                ),
            ),
            vec![],
        );

        let elaborated = elaborate(&rule, &prelude()).unwrap();

        assert_eq!(
            elaborated,
            defeasible(
                "ubo_filing",
                pi(
                    "ctx",
                    constant("IncorporationContext"),
                    constant("ComplianceVerdict")
                ),
                lam(
                    "ctx",
                    constant("IncorporationContext"),
                    match_expr(
                        app(constant("beneficial_owners"), indexed("ctx", 0)),
                        constant("ComplianceVerdict"),
                        vec![
                            branch("Nil", &[], constant("NonCompliant")),
                            branch(
                                "Cons",
                                &["owner", "rest"],
                                match_expr(
                                    app(
                                        constant("all_identified"),
                                        app(
                                            app(constant("Cons"), indexed("owner", 1)),
                                            indexed("rest", 0)
                                        ),
                                    ),
                                    constant("ComplianceVerdict"),
                                    vec![
                                        branch("True", &[], constant("Compliant")),
                                        branch("False", &[], constant("Pending")),
                                    ],
                                ),
                            ),
                        ],
                    ),
                ),
                vec![],
            )
        );
    }

    #[test]
    fn elaborates_ibc_s135_annual_return_rule() {
        let rule = defeasible(
            "annual_return_deadline",
            pi("ctx", surface("IncorporationContext"), surface("ComplianceVerdict")),
            lam(
                "ctx",
                surface("IncorporationContext"),
                match_expr(
                    app(surface("annual_return_filing_status"), surface("ctx")),
                    surface("ComplianceVerdict"),
                    vec![
                        branch("Within30Days", &[], surface("Compliant")),
                        branch("Overdue", &[], surface("NonCompliant")),
                        wildcard_branch(surface("Pending")),
                    ],
                ),
            ),
            vec![],
        );

        let elaborated = elaborate(&rule, &prelude()).unwrap();

        assert_eq!(
            elaborated,
            defeasible(
                "annual_return_deadline",
                pi(
                    "ctx",
                    constant("IncorporationContext"),
                    constant("ComplianceVerdict")
                ),
                lam(
                    "ctx",
                    constant("IncorporationContext"),
                    match_expr(
                        app(constant("annual_return_filing_status"), indexed("ctx", 0)),
                        constant("ComplianceVerdict"),
                        vec![
                            branch("Within30Days", &[], constant("Compliant")),
                            branch("Overdue", &[], constant("NonCompliant")),
                            wildcard_branch(constant("Pending")),
                        ],
                    ),
                ),
                vec![],
            )
        );
    }

    #[test]
    fn elaborates_ibc_s94_registered_agent_change_notice_rule() {
        let rule = defeasible(
            "registered_agent_change_notice",
            pi("ctx", surface("IncorporationContext"), surface("ComplianceVerdict")),
            lam(
                "ctx",
                surface("IncorporationContext"),
                match_expr(
                    app(surface("registered_agent_change_notice_status"), surface("ctx")),
                    surface("ComplianceVerdict"),
                    vec![
                        branch("Within14Days", &[], surface("Compliant")),
                        branch("LateNotice", &[], surface("NonCompliant")),
                        wildcard_branch(surface("Pending")),
                    ],
                ),
            ),
            vec![],
        );

        let elaborated = elaborate(&rule, &prelude()).unwrap();

        assert_eq!(
            elaborated,
            defeasible(
                "registered_agent_change_notice",
                pi(
                    "ctx",
                    constant("IncorporationContext"),
                    constant("ComplianceVerdict")
                ),
                lam(
                    "ctx",
                    constant("IncorporationContext"),
                    match_expr(
                        app(
                            constant("registered_agent_change_notice_status"),
                            indexed("ctx", 0)
                        ),
                        constant("ComplianceVerdict"),
                        vec![
                            branch("Within14Days", &[], constant("Compliant")),
                            branch("LateNotice", &[], constant("NonCompliant")),
                            wildcard_branch(constant("Pending")),
                        ],
                    ),
                ),
                vec![],
            )
        );
    }

    #[test]
    fn elaborates_modal_and_effect_nested_terms() {
        let rule = Term::Pi {
            binder: Ident::new("ctx"),
            domain: Box::new(surface("IncorporationContext")),
            effect_row: Some(EffectRow::BranchSensitive(Box::new(EffectRow::Effects(vec![
                Effect::Write(Box::new(surface("ComplianceVerdict"))),
                Effect::SanctionsQuery,
            ])))),
            codomain: Box::new(Term::ModalAt {
                time: TimeTerm::AsOf0(Box::new(surface("ctx"))),
                body: Box::new(Term::Unlock {
                    effect_row: Box::new(surface("ComplianceVerdict")),
                    body: Box::new(surface("Compliant")),
                }),
            }),
        };

        let elaborated = elaborate(&rule, &prelude()).unwrap();

        assert_eq!(
            elaborated,
            Term::Pi {
                binder: Ident::new("ctx"),
                domain: Box::new(constant("IncorporationContext")),
                effect_row: Some(EffectRow::BranchSensitive(Box::new(EffectRow::Effects(vec![
                    Effect::Write(Box::new(constant("ComplianceVerdict"))),
                    Effect::SanctionsQuery,
                ])))),
                codomain: Box::new(Term::ModalAt {
                    time: TimeTerm::AsOf0(Box::new(indexed("ctx", 0))),
                    body: Box::new(Term::Unlock {
                        effect_row: Box::new(constant("ComplianceVerdict")),
                        body: Box::new(constant("Compliant")),
                    }),
                }),
            }
        );
    }

    #[test]
    fn elaborates_hole_scope_nested_terms() {
        let term = Term::Hole(Hole {
            name: Some(Ident::new("ibo")),
            ty: Box::new(surface("ComplianceVerdict")),
            authority: AuthorityRef::Named(QualIdent::new(["fsa", "seychelles"].iter().copied())),
            scope: Some(ScopeConstraint {
                fields: vec![
                    ScopeField::EntityClass(Box::new(surface("IBC"))),
                    ScopeField::TimeWindow {
                        from: TimeTerm::Literal(TimeLiteral {
                            iso8601: "2026-01-01T00:00:00Z".to_string(),
                        }),
                        to: TimeTerm::Derive1 {
                            time: Box::new(TimeTerm::Literal(TimeLiteral {
                                iso8601: "2026-01-02T00:00:00Z".to_string(),
                            })),
                            witness: RewriteWitness {
                                term: Box::new(surface("Compliant")),
                            },
                        },
                    },
                ],
            }),
        });

        let elaborated = elaborate(&term, &prelude()).unwrap();

        assert_eq!(
            elaborated,
            Term::Hole(Hole {
                name: Some(Ident::new("ibo")),
                ty: Box::new(constant("ComplianceVerdict")),
                authority: AuthorityRef::Named(QualIdent::new(
                    ["fsa", "seychelles"].iter().copied()
                )),
                scope: Some(ScopeConstraint {
                    fields: vec![
                        ScopeField::EntityClass(Box::new(constant("IBC"))),
                        ScopeField::TimeWindow {
                            from: TimeTerm::Literal(TimeLiteral {
                                iso8601: "2026-01-01T00:00:00Z".to_string(),
                            }),
                            to: TimeTerm::Derive1 {
                                time: Box::new(TimeTerm::Literal(TimeLiteral {
                                    iso8601: "2026-01-02T00:00:00Z".to_string(),
                                })),
                                witness: RewriteWitness {
                                    term: Box::new(constant("Compliant")),
                                },
                            },
                        },
                    ],
                }),
            })
        );
    }

    #[test]
    fn rejects_unknown_constant() {
        let err = elaborate(&constant("NotInPrelude"), &prelude()).unwrap_err();
        assert_eq!(err.message, "unknown constant: NotInPrelude");
    }

    #[test]
    fn rejects_unknown_pattern_constructor() {
        let term = lam(
            "ctx",
            surface("IncorporationContext"),
            match_expr(
                surface("ctx"),
                surface("ComplianceVerdict"),
                vec![branch("UnknownCtor", &[], surface("Compliant"))],
            ),
        );

        let err = elaborate(&term, &prelude()).unwrap_err();
        assert_eq!(err.message, "unknown constructor: UnknownCtor");
    }

    #[test]
    fn keeps_shadowing_local_names_as_variables() {
        let term = lam("Compliant", surface("IncorporationContext"), surface("Compliant"));

        let elaborated = elaborate(&term, &prelude()).unwrap();

        assert_eq!(
            elaborated,
            lam("Compliant", constant("IncorporationContext"), indexed("Compliant", 0))
        );
    }

    #[test]
    fn propagates_unbound_variable_error_after_resolution() {
        let term = lam(
            "ctx",
            surface("IncorporationContext"),
            app(surface("director_count"), surface("missing_local")),
        );

        let err = elaborate(&term, &prelude()).unwrap_err();
        assert_eq!(
            err.message,
            "de Bruijn assignment failed: unbound variable: missing_local"
        );
    }

    #[test]
    fn resolve_names_converts_surface_globals_before_indexing() {
        let term = match_expr(
            app(surface("director_count"), surface("ctx")),
            surface("ComplianceVerdict"),
            vec![branch("Zero", &[], surface("NonCompliant"))],
        );

        let resolved = resolve_names(&term, &prelude()).unwrap();

        assert_eq!(
            resolved,
            match_expr(
                app(constant("director_count"), surface("ctx")),
                constant("ComplianceVerdict"),
                vec![branch("Zero", &[], constant("NonCompliant"))],
            )
        );
    }

    #[test]
    fn elaborates_content_refs_and_string_literals_without_change() {
        let term = Term::Annot {
            term: Box::new(Term::ContentRefTerm(ContentRef {
                hash: Blake3Hash {
                    hex: "abc123".to_string(),
                },
            })),
            ty: Box::new(Term::Sigma {
                binder: Ident::new("ctx"),
                fst_ty: Box::new(surface("IncorporationContext")),
                snd_ty: Box::new(Term::StringLit("evidence".to_string())),
            }),
        };

        let elaborated = elaborate(&term, &prelude()).unwrap();

        assert_eq!(
            elaborated,
            Term::Annot {
                term: Box::new(Term::ContentRefTerm(ContentRef {
                    hash: Blake3Hash {
                        hex: "abc123".to_string(),
                    },
                })),
                ty: Box::new(Term::Sigma {
                    binder: Ident::new("ctx"),
                    fst_ty: Box::new(constant("IncorporationContext")),
                    snd_ty: Box::new(Term::StringLit("evidence".to_string())),
                }),
            }
        );
    }
}
