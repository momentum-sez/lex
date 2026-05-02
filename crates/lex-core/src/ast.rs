//! Abstract syntax tree types for Core Lex.
//!
//! Defines the `Term` enum and all supporting types for the core calculus as
//! specified in `docs/language-reference.md`.
//!
//! All binders carry explicit domain annotations. There are no implicit
//! arguments in core form. Variables carry a De Bruijn index populated
//! by `debruijn::assign_indices`.

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Ident — a single identifier name
// ---------------------------------------------------------------------------

/// A single identifier name (not qualified).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Ident {
    /// The identifier string.
    pub name: String,
}

impl Ident {
    /// Create a new identifier.
    pub fn new(s: &str) -> Self {
        Self {
            name: s.to_string(),
        }
    }
}

// ---------------------------------------------------------------------------
// QualIdent — qualified identifier (e.g., "Mod.sub.name")
// ---------------------------------------------------------------------------

/// A dot-separated qualified identifier.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct QualIdent {
    /// The segments of the qualified name.
    pub segments: Vec<String>,
}

impl QualIdent {
    /// Create a simple (single-segment) qualified identifier.
    pub fn simple(s: &str) -> Self {
        Self {
            segments: vec![s.to_string()],
        }
    }

    /// Create a multi-segment qualified identifier.
    pub fn new<'a>(segs: impl Iterator<Item = &'a str>) -> Self {
        Self {
            segments: segs.map(|s| s.to_string()).collect(),
        }
    }
}

// ---------------------------------------------------------------------------
// Blake3Hash — a 64-hex-char blake3 digest
// ---------------------------------------------------------------------------

/// A blake3 hash literal (64 hex characters).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Blake3Hash {
    /// The hex-encoded hash string.
    pub hex: String,
}

// ---------------------------------------------------------------------------
// ContentRef — content-addressed reference (lex://blake3:<hash>)
// ---------------------------------------------------------------------------

/// A content-addressed reference.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ContentRef {
    /// The hash of the referenced content.
    pub hash: Blake3Hash,
}

impl ContentRef {
    /// Create a new content reference from a hex hash string.
    pub fn new(hex: &str) -> Self {
        Self {
            hash: Blake3Hash {
                hex: hex.to_string(),
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Constructor — inductive type constructor
// ---------------------------------------------------------------------------

/// A reference to an inductive type constructor.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Constructor {
    /// Qualified name of the constructor.
    pub name: QualIdent,
}

impl Constructor {
    /// Create a new constructor reference.
    pub fn new(name: QualIdent) -> Self {
        Self { name }
    }
}

// ---------------------------------------------------------------------------
// Level — universe level expressions (§2)
// ---------------------------------------------------------------------------

/// A universe level variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LevelVar {
    /// Index of the level variable (ℓ0, ℓ1, …).
    pub index: u32,
}

/// Universe level expression (§2 of the grammar).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Level {
    /// A concrete natural-number level.
    Nat(u64),
    /// A level variable (`ℓ0`, `ℓ1`, …).
    Var(LevelVar),
    /// Successor: `ℓ + n`.
    Succ(Box<Level>, u64),
    /// Least upper bound: `max(ℓ₁, ℓ₂)`.
    Max(Box<Level>, Box<Level>),
}

// ---------------------------------------------------------------------------
// Sort — universe sorts (§2)
// ---------------------------------------------------------------------------

/// Sort classifiers (§2).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Sort {
    /// `Type_ℓ`
    Type(Level),
    /// `Prop` (proof-irrelevant sort, lives at `Type_0`).
    Prop,
    /// `Rule_ℓ`
    Rule(Level),
    /// `Time₀` — frozen at transition commit.
    Time0,
    /// `Time₁` — derived via rewrite.
    Time1,
}

// ---------------------------------------------------------------------------
// AuthorityRef, OracleRef, TribunalRef — reference types
// ---------------------------------------------------------------------------

/// A reference to an authority.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AuthorityRef {
    /// Named authority (qualified identifier).
    Named(QualIdent),
    /// Content-addressed authority reference.
    ContentAddressed(ContentRef),
}

/// A reference to an oracle.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum OracleRef {
    /// Named oracle (qualified identifier).
    Named(QualIdent),
    /// Content-addressed oracle reference.
    ContentAddressed(ContentRef),
}

/// A reference to a tribunal.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TribunalRef {
    /// Named tribunal (qualified identifier).
    Named(QualIdent),
    /// Content-addressed tribunal reference.
    ContentAddressed(ContentRef),
    /// Meta-tribunal reference (stratum-0 only).
    MetaTribunal(QualIdent),
}

/// A reference to a principle (for principle balancing).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PrincipleRef {
    /// Named principle (qualified identifier).
    Named(QualIdent),
    /// Content-addressed principle reference.
    ContentAddressed(ContentRef),
}

/// A reference to a precedent (pinned corpus observation).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PrecedentRef {
    /// Content-addressed reference to the precedent.
    pub content: ContentRef,
}

// ---------------------------------------------------------------------------
// Effect, EffectRow — effect types (§3.1)
// ---------------------------------------------------------------------------

/// A single effect label (§3.1).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Effect {
    /// `read`
    Read,
    /// `write(scope)` — the scope is a term.
    Write(Box<Term>),
    /// `attest(authority)`
    Attest(AuthorityRef),
    /// `authority(ref)`
    Authority(AuthorityRef),
    /// `oracle(ref)`
    Oracle(OracleRef),
    /// `fuel(level, amount)`
    Fuel(Level, u64),
    /// `sanctions_query` — distinguished effect.
    SanctionsQuery,
    /// `discretion(authority)`
    Discretion(AuthorityRef),
}

/// An effect row (§3.1).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum EffectRow {
    /// The empty effect row (`∅`): pure computation.
    Empty,
    /// A list of individual effects.
    Effects(Vec<Effect>),
    /// Effect row variable for row-polymorphic effects.
    Var(u32),
    /// Path-indexed join: `row₁ ⊕ row₂`.
    Join(Box<EffectRow>, Box<EffectRow>),
    /// `⟨branch_sensitive⟩` wrapper (privilege-creep marker).
    BranchSensitive(Box<EffectRow>),
}

// ---------------------------------------------------------------------------
// TimeTerm, TimeLiteral — temporal terms (§4)
// ---------------------------------------------------------------------------

/// A time literal (`τ{iso8601}`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TimeLiteral {
    /// ISO 8601 timestamp string.
    pub iso8601: String,
}

/// A rewrite witness for `derive₁`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RewriteWitness {
    /// The witness term.
    pub term: Box<Term>,
}

/// A temporal term (§4).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TimeTerm {
    /// A time literal (`τ{iso8601}`).
    Literal(TimeLiteral),
    /// A time variable.
    Var { name: Ident, index: u32 },
    /// `asof₀(term)` — frozen time of a transition.
    AsOf0(Box<Term>),
    /// `asof₁(term)` — derived time of a rewrite.
    AsOf1(Box<Term>),
    /// `lift₀(time)` — Time₀ → Time₁ coercion.
    Lift0(Box<TimeTerm>),
    /// `derive₁(time, witness)` — Time₁ from Time₀ + rewrite witness.
    Derive1 {
        time: Box<TimeTerm>,
        witness: RewriteWitness,
    },
}

// ---------------------------------------------------------------------------
// ScopeConstraint, ScopeField — hole scope constraints (§7)
// ---------------------------------------------------------------------------

/// A scope field within a hole's scope constraint.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ScopeField {
    /// `corridor: <qual-ident>`
    Corridor(QualIdent),
    /// `time_window: <time> .. <time>`
    TimeWindow { from: TimeTerm, to: TimeTerm },
    /// `jurisdiction: <qual-ident>`
    Jurisdiction(QualIdent),
    /// `entity_class: <term>`
    EntityClass(Box<Term>),
}

/// A scope constraint for a discretion hole.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScopeConstraint {
    /// The fields of the scope constraint.
    pub fields: Vec<ScopeField>,
}

// ---------------------------------------------------------------------------
// Exception — defeasible rule exception (§6)
// ---------------------------------------------------------------------------

/// An exception in a defeasible rule.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Exception {
    /// The guard proposition (must be decidable).
    pub guard: Box<Term>,
    /// The body of the exception.
    pub body: Box<Term>,
    /// Optional priority (higher overrides lower).
    pub priority: Option<u32>,
    /// Optional authority reference.
    pub authority: Option<AuthorityRef>,
}

// ---------------------------------------------------------------------------
// DefeasibleRule — defeasible rule with exceptions (§6)
// ---------------------------------------------------------------------------

/// A defeasible rule (§6).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DefeasibleRule {
    /// Name of the defeasible rule.
    pub name: Ident,
    /// Base type of the rule.
    pub base_ty: Box<Term>,
    /// Base body of the rule.
    pub base_body: Box<Term>,
    /// Exceptions (unless clauses).
    pub exceptions: Vec<Exception>,
    /// Content-addressed reference to the exception lattice (optional).
    pub lattice: Option<ContentRef>,
}

// ---------------------------------------------------------------------------
// Hole — typed discretion hole (§7)
// ---------------------------------------------------------------------------

/// A typed discretion hole.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Hole {
    /// Hole name (`None` for anonymous `?_`).
    pub name: Option<Ident>,
    /// Expected type.
    pub ty: Box<Term>,
    /// Authority authorized to fill this hole.
    pub authority: AuthorityRef,
    /// Optional scope constraint.
    pub scope: Option<ScopeConstraint>,
}

// ---------------------------------------------------------------------------
// PrincipleBalancingStep — principle balancing (§9)
// ---------------------------------------------------------------------------

/// A principle balancing step (§9).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrincipleBalancingStep {
    /// Principles being balanced.
    pub principles: Vec<PrincipleRef>,
    /// Cited precedents.
    pub precedents: Vec<PrecedentRef>,
    /// Verdict term.
    pub verdict: Box<Term>,
    /// Rationale term.
    pub rationale: Box<Term>,
}

// ---------------------------------------------------------------------------
// Pattern — match-branch patterns (§3)
// ---------------------------------------------------------------------------

/// Pattern in a match branch (§3).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Pattern {
    /// Constructor applied to binder names: `C x₁ x₂ …`
    Constructor {
        /// The constructor reference.
        constructor: Constructor,
        /// Bound variable names introduced by this pattern.
        binders: Vec<Ident>,
    },
    /// Wildcard `_`.
    Wildcard,
}

// ---------------------------------------------------------------------------
// Branch — a single match arm
// ---------------------------------------------------------------------------

/// A branch in a `match` expression.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Branch {
    /// The pattern for this arm.
    pub pattern: Pattern,
    /// The body of this arm.
    pub body: Term,
}

// ---------------------------------------------------------------------------
// Term — the core AST (§3)
// ---------------------------------------------------------------------------

/// Core Lex term (§3 of the grammar).
///
/// Types are terms. Every binder carries an explicit domain annotation.
/// Variables carry De Bruijn indices. After `debruijn::assign_indices`,
/// all `Var` nodes have valid indices.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Term {
    // ── Variables / constants / sorts ────────────────────────────────
    /// Named variable with De Bruijn index.
    Var {
        /// Human-readable name hint.
        name: Ident,
        /// De Bruijn index.
        index: u32,
    },

    /// Universe sort (`Type_ℓ`, `Prop`, `Rule_ℓ`).
    Sort(Sort),

    /// Qualified constant reference.
    Constant(QualIdent),

    /// Content-addressed reference: `lex://blake3:<hash>`.
    ContentRefTerm(ContentRef),

    /// Integer literal.
    IntLit(i64),

    /// Rational literal (`numerator / denominator`).
    RatLit(i64, u64),

    /// String literal.
    StringLit(String),

    /// Axiom use: `axiom <qual-ident>`.
    AxiomUse {
        /// The axiom being invoked.
        axiom: QualIdent,
    },

    // ── Pair / projections ──────────────────────────────────────────
    /// Pair introduction: `⟨a, b⟩`.
    Pair { fst: Box<Term>, snd: Box<Term> },

    /// Projection: `π₁` or `π₂`.
    Proj {
        /// `true` for first projection, `false` for second.
        first: bool,
        /// The pair being projected.
        pair: Box<Term>,
    },

    // ── Application / introduction ──────────────────────────────────
    /// Application: `f a`.
    App { func: Box<Term>, arg: Box<Term> },

    /// Inductive constructor application: `C a₁ a₂ …`.
    InductiveIntro {
        /// The constructor.
        constructor: Constructor,
        /// Constructor arguments.
        args: Vec<Term>,
    },

    // ── Temporal (application level) ────────────────────────────────
    /// `sanctions-dominance(proof)`.
    SanctionsDominance {
        /// The proof of sanctions non-compliance.
        proof: Box<Term>,
    },

    /// `defeat rule` — defeasibility eliminator.
    DefeatElim {
        /// The defeasible rule being eliminated.
        rule: Box<Term>,
    },

    /// `lift₀(time)` — Time₀ coercion.
    Lift0 {
        /// The time term being lifted.
        time: Box<Term>,
    },

    /// `derive₁(time, witness)` — Time₁ derivation.
    Derive1 {
        /// The time₀ term.
        time: Box<Term>,
        /// The rewrite witness.
        witness: Box<Term>,
    },

    // ── Binders ─────────────────────────────────────────────────────
    /// Lambda abstraction: `λ(x : A). b`.
    Lambda {
        /// Binder name.
        binder: Ident,
        /// Domain type annotation.
        domain: Box<Term>,
        /// Body (under the binder).
        body: Box<Term>,
    },

    /// Dependent function type: `Π(x : A) [ρ]. B`.
    Pi {
        /// Binder name (`_` for non-dependent arrow).
        binder: Ident,
        /// Domain type.
        domain: Box<Term>,
        /// Optional effect row.
        effect_row: Option<EffectRow>,
        /// Codomain type (under the binder).
        codomain: Box<Term>,
    },

    /// Dependent pair type: `Σ(x : A). B`.
    Sigma {
        /// Binder name (`_` for non-dependent product).
        binder: Ident,
        /// First component type.
        fst_ty: Box<Term>,
        /// Second component type (under the binder).
        snd_ty: Box<Term>,
    },

    /// Type annotation: `(e : τ)`.
    Annot { term: Box<Term>, ty: Box<Term> },

    /// `let x : τ := e in b`.
    Let {
        /// Binder name.
        binder: Ident,
        /// Type annotation.
        ty: Box<Term>,
        /// Bound value.
        val: Box<Term>,
        /// Body (under the binder).
        body: Box<Term>,
    },

    /// Pattern match: `match e return P with | p₁ ⇒ e₁ | …`.
    Match {
        /// Scrutinee.
        scrutinee: Box<Term>,
        /// Return type (motive).
        return_ty: Box<Term>,
        /// Branches.
        branches: Vec<Branch>,
    },

    /// Fixed point / structural recursion: `fix f : τ := e`.
    Rec {
        /// Binder name for the recursive reference.
        binder: Ident,
        /// Type of the fixed point.
        ty: Box<Term>,
        /// Body (under the binder).
        body: Box<Term>,
    },

    // ── Temporal modals ─────────────────────────────────────────────
    /// `@ time body` — temporal modality.
    ModalAt {
        /// The time term.
        time: TimeTerm,
        /// The body proposition.
        body: Box<Term>,
    },

    /// `◇ time body` — eventually modality.
    ModalEventually {
        /// The time term.
        time: TimeTerm,
        /// The body proposition.
        body: Box<Term>,
    },

    /// `□[from, to] body` — always in interval.
    ModalAlways {
        /// Start of the interval.
        from: TimeTerm,
        /// End of the interval.
        to: TimeTerm,
        /// The body proposition.
        body: Box<Term>,
    },

    // ── Tribunal modal ──────────────────────────────────────────────
    /// `⟦T⟧ body` — tribunal modal introduction.
    ModalIntro {
        /// The tribunal under which the body is evaluated.
        tribunal: TribunalRef,
        /// The body.
        body: Box<Term>,
    },

    /// `coerce[T₁ ⇒ T₂](e, w)` — tribunal modal coercion.
    ModalElim {
        /// Source tribunal.
        from_tribunal: TribunalRef,
        /// Target tribunal.
        to_tribunal: TribunalRef,
        /// The term being coerced.
        term: Box<Term>,
        /// The canon bridge witness.
        witness: Box<Term>,
    },

    // ── Defeasible / Holes / Balance ────────────────────────────────
    /// A defeasible rule (§6).
    Defeasible(DefeasibleRule),

    /// A typed discretion hole (§7).
    Hole(Hole),

    /// `fill(h, e, pcauth)` — hole filling.
    HoleFill {
        /// The hole name being filled (`None` for anonymous).
        hole_name: Option<Ident>,
        /// The filler term.
        filler: Box<Term>,
        /// The PCAuth witness.
        pcauth: Box<Term>,
    },

    /// A principle balancing step (§9).
    PrincipleBalance(PrincipleBalancingStep),

    /// `unlock row in body` — unlock a branch-sensitive effect row.
    Unlock {
        /// The effect row being unlocked (expressed as a term).
        effect_row: Box<Term>,
        /// The body after unlock.
        body: Box<Term>,
    },
}

// ---------------------------------------------------------------------------
// Convenience constructors (for tests and downstream crates)
// ---------------------------------------------------------------------------

impl Term {
    /// Named variable with a De Bruijn index.
    pub fn var(name: &str, index: u32) -> Self {
        Term::Var {
            name: Ident::new(name),
            index,
        }
    }

    /// Lambda abstraction.
    pub fn lam(binder: &str, domain: Term, body: Term) -> Self {
        Term::Lambda {
            binder: Ident::new(binder),
            domain: Box::new(domain),
            body: Box::new(body),
        }
    }

    /// Dependent function type (Pi type), pure (no effects).
    pub fn pi(binder: &str, domain: Term, codomain: Term) -> Self {
        Term::Pi {
            binder: Ident::new(binder),
            domain: Box::new(domain),
            effect_row: None,
            codomain: Box::new(codomain),
        }
    }

    /// Dependent pair type (Sigma type).
    pub fn sigma(binder: &str, fst_ty: Term, snd_ty: Term) -> Self {
        Term::Sigma {
            binder: Ident::new(binder),
            fst_ty: Box::new(fst_ty),
            snd_ty: Box::new(snd_ty),
        }
    }

    /// Application.
    pub fn app(func: Term, arg: Term) -> Self {
        Term::App {
            func: Box::new(func),
            arg: Box::new(arg),
        }
    }

    /// Let binding.
    pub fn let_in(binder: &str, ty: Term, val: Term, body: Term) -> Self {
        Term::Let {
            binder: Ident::new(binder),
            ty: Box::new(ty),
            val: Box::new(val),
            body: Box::new(body),
        }
    }

    /// Fixed point (Rec).
    pub fn rec(binder: &str, ty: Term, body: Term) -> Self {
        Term::Rec {
            binder: Ident::new(binder),
            ty: Box::new(ty),
            body: Box::new(body),
        }
    }

    /// Pair introduction.
    pub fn pair(fst: Term, snd: Term) -> Self {
        Term::Pair {
            fst: Box::new(fst),
            snd: Box::new(snd),
        }
    }

    /// Type annotation.
    pub fn annot(term: Term, ty: Term) -> Self {
        Term::Annot {
            term: Box::new(term),
            ty: Box::new(ty),
        }
    }

    /// Match expression.
    pub fn match_expr(scrutinee: Term, return_ty: Term, branches: Vec<Branch>) -> Self {
        Term::Match {
            scrutinee: Box::new(scrutinee),
            return_ty: Box::new(return_ty),
            branches,
        }
    }

    /// Qualified constant.
    pub fn constant(name: &str) -> Self {
        Term::Constant(QualIdent::simple(name))
    }

    /// Prop sort.
    pub fn prop() -> Self {
        Term::Sort(Sort::Prop)
    }

    /// Type sort at a given level.
    pub fn type_sort(level: u64) -> Self {
        Term::Sort(Sort::Type(Level::Nat(level)))
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ident_basics() {
        let id = Ident::new("x");
        assert_eq!(id.name, "x");
    }

    #[test]
    fn qual_ident_simple() {
        let qi = QualIdent::simple("Nat");
        assert_eq!(qi.segments, vec!["Nat"]);
    }

    #[test]
    fn qual_ident_multi() {
        let qi = QualIdent::new(["regulator", "sec"].iter().copied());
        assert_eq!(qi.segments, vec!["regulator", "sec"]);
    }

    #[test]
    fn content_ref() {
        let cr = ContentRef::new("abc123");
        assert_eq!(cr.hash.hex, "abc123");
    }

    #[test]
    fn term_var_constructor() {
        let t = Term::var("x", 0);
        match t {
            Term::Var { name, index } => {
                assert_eq!(name.name, "x");
                assert_eq!(index, 0);
            }
            _ => panic!("expected Var"),
        }
    }

    #[test]
    fn term_lam_constructor() {
        let t = Term::lam("x", Term::prop(), Term::var("x", 0));
        match t {
            Term::Lambda { binder, .. } => assert_eq!(binder.name, "x"),
            _ => panic!("expected Lambda"),
        }
    }

    #[test]
    fn term_clone_eq() {
        let t = Term::lam("x", Term::prop(), Term::var("x", 0));
        assert_eq!(t, t.clone());
    }
}
