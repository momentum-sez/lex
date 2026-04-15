//! Universe level solver for Core Lex.
//!
//! Implements constraint solving in the **\u2115-max-plus semiring** as specified in
//! `docs/architecture/LEX-CORE-GRAMMAR.md` \u00a72 (Universe hierarchy).
//!
//! ## Level expressions
//!
//! ```text
//! <level> ::= <nat> | <level-var> | <level> '+' <nat> | max(<level>, <level>)
//! ```
//!
//! ## Solving strategy
//!
//! Level constraints are inequalities `\u21131 \u2264 \u21132` and `\u21131 < \u21132`. The solver
//! reduces these to a shortest-path problem on a constraint graph and applies
//! **Bellman-Ford** to find the minimal satisfying assignment (or detect
//! unsatisfiable positive cycles in the longest-path formulation).
//!
//! ## Universe rules
//!
//! - `Type_\u2113 : Type_{\u2113+1}`
//! - `Prop : Type_0`
//! - `Rule_\u2113 : Type_{\u2113+1}`
//! - A meta-rule at level `\u2113` may quantify over `Rule_\u2113\u2032` only when `\u2113\u2032 < \u2113`.
//! - `Type_\u03c9` is forbidden (Decision R.9).

use std::collections::HashMap;
use std::fmt;

#[cfg(test)]
use crate::ast::Ident;
use crate::ast::{Branch, Level, LevelVar, Sort, Term};

// ---------------------------------------------------------------------------
// Level operations -- evaluation, substitution, free variables
// ---------------------------------------------------------------------------

/// The omega limit -- any level beyond this is treated as an omega-violation.
/// Lex does not permit `Type_omega`, so we pick a generous but finite bound.
const OMEGA_LIMIT: u64 = 1_000_000;

/// Evaluate a level expression under a variable assignment.
///
/// Returns `None` if any variable in the expression is unbound.
pub fn eval_level(level: &Level, env: &HashMap<LevelVar, u64>) -> Option<u64> {
    match level {
        Level::Nat(n) => Some(*n),
        Level::Var(v) => env.get(v).copied(),
        Level::Succ(base, n) => eval_level(base, env).map(|b| b.saturating_add(*n)),
        Level::Max(a, b) => {
            let va = eval_level(a, env)?;
            let vb = eval_level(b, env)?;
            Some(va.max(vb))
        }
    }
}

/// Substitute a level variable with a replacement level expression.
pub fn subst_level(level: &Level, var: LevelVar, replacement: &Level) -> Level {
    match level {
        Level::Nat(n) => Level::Nat(*n),
        Level::Var(v) if *v == var => replacement.clone(),
        Level::Var(v) => Level::Var(v.clone()),
        Level::Succ(base, n) => Level::Succ(Box::new(subst_level(base, var, replacement)), *n),
        Level::Max(a, b) => Level::Max(
            Box::new(subst_level(a, var.clone(), replacement)),
            Box::new(subst_level(b, var, replacement)),
        ),
    }
}

/// Collect all free level variables from a level expression.
pub fn free_level_vars(level: &Level) -> Vec<LevelVar> {
    let mut vars = Vec::new();
    collect_level_vars(level, &mut vars);
    vars.sort_by_key(|v| v.index);
    vars.dedup();
    vars
}

fn collect_level_vars(level: &Level, acc: &mut Vec<LevelVar>) {
    match level {
        Level::Nat(_) => {}
        Level::Var(v) => acc.push(v.clone()),
        Level::Succ(base, _) => collect_level_vars(base, acc),
        Level::Max(a, b) => {
            collect_level_vars(a, acc);
            collect_level_vars(b, acc);
        }
    }
}

// ---------------------------------------------------------------------------
// Shorthand constructors
// ---------------------------------------------------------------------------

/// Shorthand: make a literal level.
pub fn lit(n: u64) -> Level {
    Level::Nat(n)
}

/// Shorthand: make a level variable by index.
pub fn lvar(idx: u32) -> Level {
    Level::Var(LevelVar { index: idx })
}

/// Shorthand: make a successor level `base + n`.
pub fn succ(base: Level, n: u64) -> Level {
    if n == 0 {
        base
    } else {
        Level::Succ(Box::new(base), n)
    }
}

/// Shorthand: make a max level `max(a, b)`.
pub fn level_max(a: Level, b: Level) -> Level {
    Level::Max(Box::new(a), Box::new(b))
}

/// Shorthand: make an Ident.
#[cfg(test)]
fn ident(name: &str) -> Ident {
    Ident {
        name: name.to_string(),
    }
}

// ---------------------------------------------------------------------------
// LevelConstraint -- inequality constraints between levels
// ---------------------------------------------------------------------------

/// A constraint between universe level expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LevelConstraint {
    /// `lhs <= rhs` -- non-strict inequality.
    Le(Level, Level),
    /// `lhs < rhs` -- strict inequality (equivalent to `lhs + 1 <= rhs`).
    Lt(Level, Level),
    /// `lhs = rhs` -- equality (equivalent to `lhs <= rhs AND rhs <= lhs`).
    Eq(Level, Level),
}

impl fmt::Display for LevelConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LevelConstraint::Le(l, r) => write!(f, "{} <= {}", fmt_level(l), fmt_level(r)),
            LevelConstraint::Lt(l, r) => write!(f, "{} < {}", fmt_level(l), fmt_level(r)),
            LevelConstraint::Eq(l, r) => write!(f, "{} = {}", fmt_level(l), fmt_level(r)),
        }
    }
}

fn fmt_level(l: &Level) -> String {
    match l {
        Level::Nat(n) => n.to_string(),
        Level::Var(v) => format!("l{}", v.index),
        Level::Succ(base, n) => format!("{} + {}", fmt_level(base), n),
        Level::Max(a, b) => format!("max({}, {})", fmt_level(a), fmt_level(b)),
    }
}

// ---------------------------------------------------------------------------
// LevelError -- solver errors
// ---------------------------------------------------------------------------

/// Errors that can arise during universe level solving or consistency checking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LevelError {
    /// The constraint set is unsatisfiable.
    Unsatisfiable {
        /// A human-readable description of the conflicting constraints.
        reason: String,
    },
    /// A positive cycle was detected in the longest-path constraint graph.
    CyclicDependency {
        /// The variables involved in the cycle.
        cycle: Vec<LevelVar>,
    },
    /// A level expression evaluated to omega, which is forbidden by Decision R.9.
    OmegaLimitViolation {
        /// The level expression that would require omega.
        expr: String,
    },
    /// A meta-rule at level l quantifies over `Rule_l'` where `l' >= l`.
    MetaRuleViolation {
        /// The level of the meta-rule binder's codomain.
        meta_level: Level,
        /// The level of the rule being quantified over.
        rule_level: Level,
    },
    /// A level variable was referenced but not present in the solution.
    UnboundVariable(LevelVar),
}

impl fmt::Display for LevelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LevelError::Unsatisfiable { reason } => {
                write!(f, "unsatisfiable level constraints: {}", reason)
            }
            LevelError::CyclicDependency { cycle } => {
                let names: Vec<_> = cycle.iter().map(|v| format!("l{}", v.index)).collect();
                write!(f, "cyclic level dependency: {}", names.join(" -> "))
            }
            LevelError::OmegaLimitViolation { expr } => {
                write!(
                    f,
                    "omega-limit violation: {} would require Type_omega",
                    expr
                )
            }
            LevelError::MetaRuleViolation {
                meta_level,
                rule_level,
            } => {
                write!(
                    f,
                    "meta-rule at level {} quantifies over Rule_{}, but requires l' < {}",
                    fmt_level(meta_level),
                    fmt_level(rule_level),
                    fmt_level(meta_level),
                )
            }
            LevelError::UnboundVariable(v) => {
                write!(f, "unbound level variable: l{}", v.index)
            }
        }
    }
}

impl std::error::Error for LevelError {}

// ---------------------------------------------------------------------------
// LevelSolution -- result of constraint solving
// ---------------------------------------------------------------------------

/// A satisfying assignment of level variables to concrete natural numbers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LevelSolution {
    /// The minimal assignment for each level variable.
    pub assignment: HashMap<LevelVar, u64>,
}

impl LevelSolution {
    /// Evaluate a level expression under this solution.
    pub fn eval(&self, level: &Level) -> Result<u64, LevelError> {
        eval_level(level, &self.assignment).ok_or_else(|| {
            let unbound = free_level_vars(level)
                .into_iter()
                .find(|v| !self.assignment.contains_key(v));
            match unbound {
                Some(v) => LevelError::UnboundVariable(v),
                None => LevelError::Unsatisfiable {
                    reason: "evaluation failed".to_string(),
                },
            }
        })
    }
}

// ---------------------------------------------------------------------------
// Constraint graph -- internal representation for Bellman-Ford
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct Edge {
    src: usize,
    dst: usize,
    weight: i64,
}

// ---------------------------------------------------------------------------
// solve_levels -- Bellman-Ford constraint solving
// ---------------------------------------------------------------------------

/// Solve a set of level constraints, finding the minimal assignment of level
/// variables that satisfies all constraints.
///
/// Uses Bellman-Ford longest-path in the max-plus semiring.
pub fn solve_levels(constraints: &[LevelConstraint]) -> Result<LevelSolution, LevelError> {
    if constraints.is_empty() {
        return Ok(LevelSolution {
            assignment: HashMap::new(),
        });
    }

    // Step 1: Collect all variables
    let mut var_set: Vec<LevelVar> = Vec::new();
    for c in constraints {
        match c {
            LevelConstraint::Le(l, r) | LevelConstraint::Lt(l, r) | LevelConstraint::Eq(l, r) => {
                collect_level_vars(l, &mut var_set);
                collect_level_vars(r, &mut var_set);
            }
        }
    }
    var_set.sort_by_key(|v| v.index);
    var_set.dedup();

    if var_set.is_empty() {
        for c in constraints {
            verify_literal_constraint(c)?;
        }
        return Ok(LevelSolution {
            assignment: HashMap::new(),
        });
    }

    let var_index: HashMap<LevelVar, usize> = var_set
        .iter()
        .enumerate()
        .map(|(i, v)| (v.clone(), i))
        .collect();
    let n = var_set.len();
    let source = n;
    let num_nodes = n + 1;
    let mut edges: Vec<Edge> = Vec::new();

    // Virtual source -> each variable with weight 0
    for i in 0..n {
        edges.push(Edge {
            src: source,
            dst: i,
            weight: 0,
        });
    }

    for c in constraints {
        normalize_constraint(c, &var_index, &mut edges);
    }

    // Bellman-Ford longest paths
    let mut dist = vec![0i64; num_nodes];

    for _ in 0..num_nodes - 1 {
        let mut changed = false;
        for e in &edges {
            let candidate = dist[e.src].saturating_add(e.weight);
            if candidate > dist[e.dst] {
                dist[e.dst] = candidate;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Detect positive cycles
    for e in &edges {
        let candidate = dist[e.src].saturating_add(e.weight);
        if candidate > dist[e.dst] {
            let cycle_vars = find_cycle_vars(e, &edges, &var_set, num_nodes);
            return Err(LevelError::CyclicDependency { cycle: cycle_vars });
        }
    }

    // Extract solution
    let mut assignment = HashMap::new();
    for (i, v) in var_set.iter().enumerate() {
        let val = dist[i];
        if val < 0 {
            return Err(LevelError::Unsatisfiable {
                reason: format!("variable l{} would require negative level {}", v.index, val),
            });
        }
        let val_u64 = val as u64;
        if val_u64 >= OMEGA_LIMIT {
            return Err(LevelError::OmegaLimitViolation {
                expr: format!("l{} = {}", v.index, val_u64),
            });
        }
        assignment.insert(v.clone(), val_u64);
    }

    let solution = LevelSolution { assignment };
    for c in constraints {
        verify_constraint_with_solution(c, &solution)?;
    }

    Ok(solution)
}

fn verify_literal_constraint(c: &LevelConstraint) -> Result<(), LevelError> {
    let empty = HashMap::new();
    match c {
        LevelConstraint::Le(l, r) => {
            let lv = eval_level(l, &empty).ok_or_else(|| LevelError::Unsatisfiable {
                reason: format!("cannot evaluate {}", fmt_level(l)),
            })?;
            let rv = eval_level(r, &empty).ok_or_else(|| LevelError::Unsatisfiable {
                reason: format!("cannot evaluate {}", fmt_level(r)),
            })?;
            if lv > rv {
                return Err(LevelError::Unsatisfiable {
                    reason: format!(
                        "{} <= {} is false ({} > {})",
                        fmt_level(l),
                        fmt_level(r),
                        lv,
                        rv
                    ),
                });
            }
        }
        LevelConstraint::Lt(l, r) => {
            let lv = eval_level(l, &empty).ok_or_else(|| LevelError::Unsatisfiable {
                reason: format!("cannot evaluate {}", fmt_level(l)),
            })?;
            let rv = eval_level(r, &empty).ok_or_else(|| LevelError::Unsatisfiable {
                reason: format!("cannot evaluate {}", fmt_level(r)),
            })?;
            if lv >= rv {
                return Err(LevelError::Unsatisfiable {
                    reason: format!(
                        "{} < {} is false ({} >= {})",
                        fmt_level(l),
                        fmt_level(r),
                        lv,
                        rv
                    ),
                });
            }
        }
        LevelConstraint::Eq(l, r) => {
            let lv = eval_level(l, &empty).ok_or_else(|| LevelError::Unsatisfiable {
                reason: format!("cannot evaluate {}", fmt_level(l)),
            })?;
            let rv = eval_level(r, &empty).ok_or_else(|| LevelError::Unsatisfiable {
                reason: format!("cannot evaluate {}", fmt_level(r)),
            })?;
            if lv != rv {
                return Err(LevelError::Unsatisfiable {
                    reason: format!("{} = {} is false", fmt_level(l), fmt_level(r)),
                });
            }
        }
    }
    Ok(())
}

fn normalize_constraint(
    c: &LevelConstraint,
    var_index: &HashMap<LevelVar, usize>,
    edges: &mut Vec<Edge>,
) {
    match c {
        LevelConstraint::Le(lhs, rhs) => {
            add_le_edges(lhs, rhs, 0, var_index, edges);
        }
        LevelConstraint::Lt(lhs, rhs) => {
            add_le_edges(lhs, rhs, 1, var_index, edges);
        }
        LevelConstraint::Eq(lhs, rhs) => {
            add_le_edges(lhs, rhs, 0, var_index, edges);
            add_le_edges(rhs, lhs, 0, var_index, edges);
        }
    }
}

fn add_le_edges(
    lhs: &Level,
    rhs: &Level,
    extra_offset: i64,
    var_index: &HashMap<LevelVar, usize>,
    edges: &mut Vec<Edge>,
) {
    let lhs_atoms = flatten_level(lhs);
    let rhs_atoms = flatten_level(rhs);

    for (lhs_var, lhs_off) in &lhs_atoms {
        for (rhs_var, rhs_off) in &rhs_atoms {
            let weight = *lhs_off + extra_offset - *rhs_off;
            let src = match lhs_var {
                Some(v) => match var_index.get(v) {
                    Some(&idx) => idx,
                    None => continue,
                },
                None => var_index.len(),
            };
            let dst = match rhs_var {
                Some(v) => match var_index.get(v) {
                    Some(&idx) => idx,
                    None => continue,
                },
                None => continue,
            };
            edges.push(Edge { src, dst, weight });
        }
    }
}

fn flatten_level(level: &Level) -> Vec<(Option<LevelVar>, i64)> {
    match level {
        Level::Nat(n) => vec![(None, *n as i64)],
        Level::Var(v) => vec![(Some(v.clone()), 0)],
        Level::Succ(base, n) => {
            let mut atoms = flatten_level(base);
            for (_, off) in &mut atoms {
                *off += *n as i64;
            }
            atoms
        }
        Level::Max(a, b) => {
            let mut atoms = flatten_level(a);
            atoms.extend(flatten_level(b));
            atoms
        }
    }
}

fn find_cycle_vars(
    trigger: &Edge,
    edges: &[Edge],
    var_set: &[LevelVar],
    num_nodes: usize,
) -> Vec<LevelVar> {
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); num_nodes];
    for e in edges {
        adj[e.src].push(e.dst);
    }

    let mut visited = vec![false; num_nodes];
    let mut path = Vec::new();
    visited[trigger.dst] = true;
    path.push(trigger.dst);

    let mut stack = vec![(trigger.dst, 0usize)];
    while let Some((node, idx)) = stack.last_mut() {
        if *idx >= adj[*node].len() {
            stack.pop();
            path.pop();
            continue;
        }
        let next = adj[*node][*idx];
        *idx += 1;
        if next == trigger.src {
            path.push(next);
            break;
        }
        if !visited[next] {
            visited[next] = true;
            path.push(next);
            stack.push((next, 0));
        }
    }

    path.into_iter()
        .filter_map(|i| var_set.get(i).cloned())
        .collect()
}

fn verify_constraint_with_solution(
    c: &LevelConstraint,
    solution: &LevelSolution,
) -> Result<(), LevelError> {
    match c {
        LevelConstraint::Le(l, r) => {
            let lv = solution.eval(l)?;
            let rv = solution.eval(r)?;
            if lv > rv {
                return Err(LevelError::Unsatisfiable {
                    reason: format!(
                        "{} <= {} is false under solution ({} > {})",
                        fmt_level(l),
                        fmt_level(r),
                        lv,
                        rv,
                    ),
                });
            }
        }
        LevelConstraint::Lt(l, r) => {
            let lv = solution.eval(l)?;
            let rv = solution.eval(r)?;
            if lv >= rv {
                return Err(LevelError::Unsatisfiable {
                    reason: format!(
                        "{} < {} is false under solution ({} >= {})",
                        fmt_level(l),
                        fmt_level(r),
                        lv,
                        rv,
                    ),
                });
            }
        }
        LevelConstraint::Eq(l, r) => {
            let lv = solution.eval(l)?;
            let rv = solution.eval(r)?;
            if lv != rv {
                return Err(LevelError::Unsatisfiable {
                    reason: format!(
                        "{} = {} is false under solution",
                        fmt_level(l),
                        fmt_level(r),
                    ),
                });
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// check_universe_consistency
// ---------------------------------------------------------------------------

/// Check that a term satisfies the universe hierarchy rules:
///
/// 1. `Type_l : Type_{l+1}`
/// 2. `Prop : Type_0`
/// 3. `Rule_l : Type_{l+1}`
/// 4. Meta-rule stratification: `Pi(r : Rule_l'). B` requires `l' < l`
///    when `B` is `Sort(Rule_l)` or `Sort(Type_l)`.
/// 5. `Type_omega` is forbidden (Decision R.9).
pub fn check_universe_consistency(term: &Term) -> Result<(), LevelError> {
    let mut constraints = Vec::new();
    check_term(term, &mut constraints)?;

    if !constraints.is_empty() {
        let _solution = solve_levels(&constraints)?;
    }

    Ok(())
}

fn check_term(term: &Term, constraints: &mut Vec<LevelConstraint>) -> Result<(), LevelError> {
    match term {
        Term::Sort(sort) => check_sort_finite(sort)?,

        Term::Var { .. }
        | Term::Constant(_)
        | Term::AxiomUse { .. }
        | Term::ContentRefTerm(_)
        | Term::IntLit(_)
        | Term::RatLit(_, _)
        | Term::StringLit(_) => {}

        Term::App { func, arg } => {
            check_term(func, constraints)?;
            check_term(arg, constraints)?;
        }

        Term::Lambda { domain, body, .. } => {
            check_term(domain, constraints)?;
            check_term(body, constraints)?;
        }

        Term::Pi {
            domain, codomain, ..
        } => {
            check_term(domain, constraints)?;
            check_term(codomain, constraints)?;

            // Meta-rule stratification: if domain is Rule_l' and
            // codomain is Sort(Rule_l) or Sort(Type_l), enforce l' < l.
            if let Term::Sort(Sort::Rule(rule_level)) = domain.as_ref() {
                match codomain.as_ref() {
                    Term::Sort(Sort::Rule(meta_level)) | Term::Sort(Sort::Type(meta_level)) => {
                        constraints
                            .push(LevelConstraint::Lt(rule_level.clone(), meta_level.clone()));
                    }
                    _ => {}
                }
            }
        }

        Term::Sigma { fst_ty, snd_ty, .. } => {
            check_term(fst_ty, constraints)?;
            check_term(snd_ty, constraints)?;
        }

        Term::Pair { fst, snd } => {
            check_term(fst, constraints)?;
            check_term(snd, constraints)?;
        }

        Term::Proj { pair, .. } => {
            check_term(pair, constraints)?;
        }

        Term::Annot { term: inner, ty } => {
            check_term(inner, constraints)?;
            check_term(ty, constraints)?;
        }

        Term::Let { ty, val, body, .. } => {
            check_term(ty, constraints)?;
            check_term(val, constraints)?;
            check_term(body, constraints)?;
        }

        Term::Match {
            scrutinee,
            return_ty,
            branches,
        } => {
            check_term(scrutinee, constraints)?;
            check_term(return_ty, constraints)?;
            for br in branches {
                check_branch(br, constraints)?;
            }
        }

        Term::Rec { ty, body, .. } => {
            check_term(ty, constraints)?;
            check_term(body, constraints)?;
        }

        Term::InductiveIntro { args, .. } => {
            for arg in args {
                check_term(arg, constraints)?;
            }
        }

        Term::ModalAt { body, .. } => {
            check_term(body, constraints)?;
        }

        Term::ModalEventually { body, .. } => {
            check_term(body, constraints)?;
        }

        Term::ModalAlways { body, .. } => {
            check_term(body, constraints)?;
        }

        Term::ModalIntro { body, .. } => {
            check_term(body, constraints)?;
        }

        Term::ModalElim {
            term: inner,
            witness,
            ..
        } => {
            check_term(inner, constraints)?;
            check_term(witness, constraints)?;
        }

        Term::SanctionsDominance { proof } => {
            check_term(proof, constraints)?;
        }

        Term::Defeasible(rule) => {
            check_term(&rule.base_ty, constraints)?;
            check_term(&rule.base_body, constraints)?;
            for exc in &rule.exceptions {
                check_term(&exc.guard, constraints)?;
                check_term(&exc.body, constraints)?;
            }
        }

        Term::DefeatElim { rule } => {
            check_term(rule, constraints)?;
        }

        Term::Hole(hole) => {
            check_term(&hole.ty, constraints)?;
        }

        Term::HoleFill { filler, pcauth, .. } => {
            check_term(filler, constraints)?;
            check_term(pcauth, constraints)?;
        }

        Term::PrincipleBalance(step) => {
            check_term(&step.verdict, constraints)?;
            check_term(&step.rationale, constraints)?;
        }

        Term::Unlock { effect_row, body } => {
            check_term(effect_row, constraints)?;
            check_term(body, constraints)?;
        }

        Term::Lift0 { time } => {
            check_term(time, constraints)?;
        }

        Term::Derive1 { time, witness } => {
            check_term(time, constraints)?;
            check_term(witness, constraints)?;
        }
    }
    Ok(())
}

fn check_branch(branch: &Branch, constraints: &mut Vec<LevelConstraint>) -> Result<(), LevelError> {
    check_term(&branch.body, constraints)
}

fn check_sort_finite(sort: &Sort) -> Result<(), LevelError> {
    match sort {
        Sort::Type(level) => check_level_finite(level),
        Sort::Prop => Ok(()),
        Sort::Rule(level) => check_level_finite(level),
        Sort::Time0 | Sort::Time1 => Ok(()),
    }
}

fn check_level_finite(level: &Level) -> Result<(), LevelError> {
    match level {
        Level::Nat(n) if *n >= OMEGA_LIMIT => Err(LevelError::OmegaLimitViolation {
            expr: format!("Type_{}", n),
        }),
        Level::Nat(_) => Ok(()),
        Level::Var(_) => Ok(()),
        Level::Succ(base, n) => {
            check_level_finite(base)?;
            if let Level::Nat(b) = base.as_ref() {
                if b.saturating_add(*n) >= OMEGA_LIMIT {
                    return Err(LevelError::OmegaLimitViolation {
                        expr: format!("{} + {}", fmt_level(base), n),
                    });
                }
            }
            Ok(())
        }
        Level::Max(a, b) => {
            check_level_finite(a)?;
            check_level_finite(b)?;
            Ok(())
        }
    }
}

// ---------------------------------------------------------------------------
// sort_of_sort -- infer the type of a sort
// ---------------------------------------------------------------------------

/// Given a sort, return its type in the universe hierarchy.
///
/// - `Type_l : Type_{l+1}`
/// - `Prop : Type_0`
/// - `Rule_l : Type_{l+1}`
pub fn sort_of_sort(sort: &Sort) -> Sort {
    match sort {
        Sort::Type(level) => Sort::Type(succ(level.clone(), 1)),
        Sort::Prop => Sort::Type(lit(0)),
        Sort::Rule(level) => Sort::Type(succ(level.clone(), 1)),
        Sort::Time0 | Sort::Time1 => Sort::Type(lit(0)),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn v(idx: u32) -> LevelVar {
        LevelVar { index: idx }
    }

    // -- Test 1: Simple level assignment

    #[test]
    fn simple_level_assignment() {
        let constraints = vec![
            LevelConstraint::Le(lvar(0), lit(3)),
            LevelConstraint::Le(lit(2), lvar(0)),
        ];
        let solution = solve_levels(&constraints).unwrap();
        assert_eq!(solution.assignment[&v(0)], 2);
    }

    // -- Test 2: Max of two levels

    #[test]
    fn max_of_two_levels() {
        let constraints = vec![
            LevelConstraint::Le(lit(2), lvar(0)),
            LevelConstraint::Le(lit(3), lvar(1)),
            LevelConstraint::Le(level_max(lvar(0), lvar(1)), lit(5)),
        ];
        let solution = solve_levels(&constraints).unwrap();
        let l0 = solution.assignment[&v(0)];
        let l1 = solution.assignment[&v(1)];
        assert!(l0 >= 2);
        assert!(l1 >= 3);
        assert!(l0.max(l1) <= 5);
    }

    // -- Test 3: Constraint satisfaction

    #[test]
    fn constraint_satisfaction() {
        let constraints = vec![
            LevelConstraint::Lt(lvar(0), lvar(1)),
            LevelConstraint::Le(lvar(1), lit(4)),
        ];
        let solution = solve_levels(&constraints).unwrap();
        let l0 = solution.assignment[&v(0)];
        let l1 = solution.assignment[&v(1)];
        assert!(l0 < l1);
        assert!(l1 <= 4);
        assert_eq!(l0, 0);
        assert_eq!(l1, 1);
    }

    // -- Test 4: Unsatisfiable constraints (cyclic)

    #[test]
    fn unsatisfiable_cyclic() {
        let constraints = vec![
            LevelConstraint::Lt(lvar(0), lvar(1)),
            LevelConstraint::Lt(lvar(1), lvar(0)),
        ];
        let result = solve_levels(&constraints);
        assert!(result.is_err());
        match result.unwrap_err() {
            LevelError::CyclicDependency { cycle } => {
                assert!(!cycle.is_empty());
            }
            other => panic!("expected CyclicDependency, got {:?}", other),
        }
    }

    // -- Test 5: Level variable substitution

    #[test]
    fn level_variable_substitution() {
        let level = succ(lvar(0), 2);
        let substituted = subst_level(&level, v(0), &lit(3));
        let env = HashMap::new();
        assert_eq!(eval_level(&substituted, &env), Some(5));
    }

    // -- Test 6: Type_0 : Type_1

    #[test]
    fn type_0_in_type_1() {
        let sort = Sort::Type(lit(0));
        let container = sort_of_sort(&sort);
        assert_eq!(container, Sort::Type(succ(lit(0), 1)));
    }

    // -- Test 7: Rule_0 : Type_1

    #[test]
    fn rule_0_in_type_1() {
        let sort = Sort::Rule(lit(0));
        let container = sort_of_sort(&sort);
        assert_eq!(container, Sort::Type(succ(lit(0), 1)));
    }

    // -- Test 8: Meta-rule level check (valid)

    #[test]
    fn meta_rule_level_check_valid() {
        // Pi(r : Rule_1). Type_3 -- valid (1 < 3).
        let term = Term::Pi {
            binder: ident("r"),
            domain: Box::new(Term::Sort(Sort::Rule(lit(1)))),
            effect_row: None,
            codomain: Box::new(Term::Sort(Sort::Type(lit(3)))),
        };
        assert!(check_universe_consistency(&term).is_ok());
    }

    // -- Test 9: Meta-rule level check (invalid)

    #[test]
    fn meta_rule_level_check_invalid() {
        // Pi(r : Rule_2). Type_2 -- invalid (2 < 2 is false).
        let term = Term::Pi {
            binder: ident("r"),
            domain: Box::new(Term::Sort(Sort::Rule(lit(2)))),
            effect_row: None,
            codomain: Box::new(Term::Sort(Sort::Type(lit(2)))),
        };
        let result = check_universe_consistency(&term);
        assert!(result.is_err());
    }

    // -- Test 10: Multiple level variables

    #[test]
    fn multiple_level_variables() {
        let constraints = vec![
            LevelConstraint::Lt(lvar(0), lvar(1)),
            LevelConstraint::Lt(lvar(1), lvar(2)),
            LevelConstraint::Le(lvar(2), lit(5)),
        ];
        let solution = solve_levels(&constraints).unwrap();
        let l0 = solution.assignment[&v(0)];
        let l1 = solution.assignment[&v(1)];
        let l2 = solution.assignment[&v(2)];
        assert!(l0 < l1);
        assert!(l1 < l2);
        assert!(l2 <= 5);
        assert_eq!(l0, 0);
        assert_eq!(l1, 1);
        assert_eq!(l2, 2);
    }

    // -- Test 11: No omega-limit (Type_omega rejected)

    #[test]
    fn omega_limit_rejected() {
        let term = Term::Sort(Sort::Type(lit(OMEGA_LIMIT)));
        let result = check_universe_consistency(&term);
        assert!(result.is_err());
        match result.unwrap_err() {
            LevelError::OmegaLimitViolation { expr } => {
                assert!(expr.contains(&OMEGA_LIMIT.to_string()));
            }
            other => panic!("expected OmegaLimitViolation, got {:?}", other),
        }
    }

    // -- Test 12: Prop in Type_0

    #[test]
    fn prop_in_type_0() {
        let sort = Sort::Prop;
        let container = sort_of_sort(&sort);
        assert_eq!(container, Sort::Type(lit(0)));
    }

    // -- Test 13: Level evaluation

    #[test]
    fn level_evaluation() {
        let mut env = HashMap::new();
        env.insert(v(0), 3);
        env.insert(v(1), 5);

        let level = level_max(succ(lvar(0), 1), lvar(1));
        assert_eq!(eval_level(&level, &env), Some(5));

        let level2 = lvar(2);
        assert_eq!(eval_level(&level2, &env), None);
    }

    // -- Test 14: Empty constraints

    #[test]
    fn empty_constraints() {
        let solution = solve_levels(&[]).unwrap();
        assert!(solution.assignment.is_empty());
    }

    // -- Test 15: Equality constraint

    #[test]
    fn equality_constraint() {
        let constraints = vec![
            LevelConstraint::Eq(lvar(0), lvar(1)),
            LevelConstraint::Eq(lvar(1), lit(3)),
        ];
        let solution = solve_levels(&constraints).unwrap();
        assert_eq!(solution.assignment[&v(0)], 3);
        assert_eq!(solution.assignment[&v(1)], 3);
    }

    // -- Test 16: Successor level in constraint

    #[test]
    fn successor_level_constraint() {
        let constraints = vec![
            LevelConstraint::Le(succ(lvar(0), 1), lvar(1)),
            LevelConstraint::Le(lvar(1), lit(3)),
        ];
        let solution = solve_levels(&constraints).unwrap();
        let l0 = solution.assignment[&v(0)];
        let l1 = solution.assignment[&v(1)];
        assert!(l0 + 1 <= l1);
        assert!(l1 <= 3);
    }

    // -- Test 17: Free variables collection

    #[test]
    fn free_vars_collection() {
        let level = level_max(succ(lvar(0), 1), level_max(lvar(1), lvar(0)));
        let vars = free_level_vars(&level);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&v(0)));
        assert!(vars.contains(&v(1)));
    }

    // -- Test 18: Literal-only unsatisfiable

    #[test]
    fn literal_only_unsatisfiable() {
        let constraints = vec![LevelConstraint::Lt(lit(5), lit(3))];
        let result = solve_levels(&constraints);
        assert!(result.is_err());
    }

    // -- Test 19: Nested term consistency check

    #[test]
    fn nested_term_consistency() {
        let term = Term::Pi {
            binder: ident("x"),
            domain: Box::new(Term::Sort(Sort::Type(lit(0)))),
            effect_row: None,
            codomain: Box::new(Term::Sort(Sort::Type(lit(1)))),
        };
        assert!(check_universe_consistency(&term).is_ok());
    }

    // -- Test 20: Meta-rule with variables

    #[test]
    fn meta_rule_with_variables() {
        let term = Term::Pi {
            binder: ident("r"),
            domain: Box::new(Term::Sort(Sort::Rule(lvar(0)))),
            effect_row: None,
            codomain: Box::new(Term::Sort(Sort::Rule(lvar(1)))),
        };
        assert!(check_universe_consistency(&term).is_ok());
    }
}
