//! Pretty printer: AST → source text (round-trip property).
//!
//! Reconstructs valid Lex source text from an AST using Unicode symbols
//! (λ, Π, Σ, →, ×, ⟨⟩, ⇒). Applies minimal parenthesization — only
//! where needed for disambiguation — and indents nested terms with 2 spaces.

use std::fmt;

use crate::ast::{
    AuthorityRef, Branch, Constructor, ContentRef, DefeasibleRule, Effect, EffectRow, Exception,
    Hole, Level, LevelVar, OracleRef, Pattern, PrecedentRef, PrincipleBalancingStep, PrincipleRef,
    QualIdent, ScopeConstraint, ScopeField, Sort, Term, TimeLiteral, TimeTerm, TribunalRef,
};

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Pretty-print a [`Term`] to valid Lex source text.
///
/// Uses Unicode symbols, minimal parenthesization, 2-space indentation for
/// nested terms, De Bruijn indices shown as `@n` suffix, and subscript
/// notation for temporal terms.
pub fn pretty_print(term: &Term) -> String {
    let mut pp = PrettyPrinter::new();
    pp.print_term(term, Prec::Top);
    pp.finish()
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", pretty_print(self))
    }
}

// ---------------------------------------------------------------------------
// Precedence levels for minimal parenthesization
// ---------------------------------------------------------------------------

/// Precedence levels from loosest to tightest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Prec {
    /// Top level — no parens needed.
    Top = 0,
    /// Let, match, fix, defeasible — low binding.
    Binder = 1,
    /// Arrow / product (right-associative).
    #[allow(dead_code)]
    Arrow = 2,
    /// Application (left-associative).
    App = 3,
    /// Atomic — variables, constants, literals, grouped expressions.
    Atom = 4,
}

// ---------------------------------------------------------------------------
// PrettyPrinter state
// ---------------------------------------------------------------------------

struct PrettyPrinter {
    buf: String,
    indent: usize,
}

impl PrettyPrinter {
    fn new() -> Self {
        Self {
            buf: String::new(),
            indent: 0,
        }
    }

    fn finish(self) -> String {
        self.buf
    }

    fn push(&mut self, s: &str) {
        self.buf.push_str(s);
    }

    #[allow(dead_code)]
    fn push_char(&mut self, c: char) {
        self.buf.push(c);
    }

    fn newline(&mut self) {
        self.buf.push('\n');
        for _ in 0..self.indent {
            self.buf.push(' ');
        }
    }

    fn indent(&mut self) {
        self.indent += 2;
    }

    fn dedent(&mut self) {
        self.indent = self.indent.saturating_sub(2);
    }

    // -- Helpers for wrapping in parens when needed --

    fn parens_if(&mut self, needed: bool, inner_prec: Prec, term: &Term) {
        if needed {
            self.push("(");
            self.print_term(term, inner_prec);
            self.push(")");
        } else {
            self.print_term(term, inner_prec);
        }
    }

    /// Returns the precedence of a term (its own natural binding strength).
    fn term_prec(term: &Term) -> Prec {
        match term {
            Term::Var { .. }
            | Term::Sort(_)
            | Term::Constant(_)
            | Term::Pair { .. }
            | Term::ContentRefTerm(_)
            | Term::IntLit(_)
            | Term::RatLit(_, _)
            | Term::StringLit(_)
            | Term::AxiomUse { .. } => Prec::Atom,

            Term::App { .. }
            | Term::Proj { .. }
            | Term::SanctionsDominance { .. }
            | Term::InductiveIntro { .. }
            | Term::DefeatElim { .. }
            | Term::Lift0 { .. }
            | Term::Derive1 { .. } => Prec::App,

            // Pi used as non-dependent arrow (binder name "_") behaves like arrow
            // but we treat all Pi as binder-level
            Term::Pi { .. } => Prec::Binder,

            Term::Lambda { .. }
            | Term::Sigma { .. }
            | Term::Annot { .. }
            | Term::Let { .. }
            | Term::Match { .. }
            | Term::Rec { .. }
            | Term::Defeasible(_)
            | Term::Hole(_)
            | Term::HoleFill { .. }
            | Term::ModalAt { .. }
            | Term::ModalEventually { .. }
            | Term::ModalAlways { .. }
            | Term::ModalIntro { .. }
            | Term::ModalElim { .. }
            | Term::PrincipleBalance(_)
            | Term::Unlock { .. } => Prec::Binder,
        }
    }

    /// Check if a Pi type looks like a non-dependent arrow (binder is "_").
    fn is_nondep_arrow(term: &Term) -> bool {
        matches!(term, Term::Pi { binder, effect_row, .. }
            if binder.name == "_" && (effect_row.is_none() || matches!(effect_row, Some(EffectRow::Empty))))
    }

    /// Check if a Sigma looks like a non-dependent product (binder is "_").
    fn is_nondep_product(term: &Term) -> bool {
        matches!(term, Term::Sigma { binder, .. } if binder.name == "_")
    }

    // -- Level printing --

    fn print_level(&mut self, level: &Level) {
        match level {
            Level::Nat(n) => {
                self.push(&n.to_string());
            }
            Level::Var(LevelVar { index }) => {
                self.push("ℓ");
                self.push(&index.to_string());
            }
            Level::Succ(base, n) => {
                self.print_level(base);
                self.push(" + ");
                self.push(&n.to_string());
            }
            Level::Max(a, b) => {
                self.push("max(");
                self.print_level(a);
                self.push(", ");
                self.print_level(b);
                self.push(")");
            }
        }
    }

    // -- Sort printing --

    fn print_sort(&mut self, sort: &Sort) {
        match sort {
            Sort::Type(level) => {
                self.push("Type_");
                self.print_level(level);
            }
            Sort::Prop => {
                self.push("Prop");
            }
            Sort::Rule(level) => {
                self.push("Rule_");
                self.print_level(level);
            }
            Sort::Time0 => {
                self.push("Time0");
            }
            Sort::Time1 => {
                self.push("Time1");
            }
        }
    }

    // -- Qualified identifier printing --

    fn print_qual_ident(&mut self, qi: &QualIdent) {
        for (i, seg) in qi.segments.iter().enumerate() {
            if i > 0 {
                self.push(".");
            }
            self.push(seg);
        }
    }

    // -- Authority / Oracle / Tribunal reference printing --

    fn print_authority_ref(&mut self, aref: &AuthorityRef) {
        match aref {
            AuthorityRef::Named(qi) => self.print_qual_ident(qi),
            AuthorityRef::ContentAddressed(cr) => self.print_content_ref(cr),
        }
    }

    fn print_oracle_ref(&mut self, oref: &OracleRef) {
        match oref {
            OracleRef::Named(qi) => self.print_qual_ident(qi),
            OracleRef::ContentAddressed(cr) => self.print_content_ref(cr),
        }
    }

    fn print_tribunal_ref(&mut self, tref: &TribunalRef) {
        match tref {
            TribunalRef::Named(qi) => self.print_qual_ident(qi),
            TribunalRef::ContentAddressed(cr) => self.print_content_ref(cr),
            TribunalRef::MetaTribunal(qi) => {
                self.push("meta-tribunal.");
                self.print_qual_ident(qi);
            }
        }
    }

    fn print_content_ref(&mut self, cr: &ContentRef) {
        self.push("lex://blake3:");
        self.push(&cr.hash.hex);
    }

    // -- Effect printing --

    fn print_effect(&mut self, eff: &Effect) {
        match eff {
            Effect::Read => self.push("read"),
            Effect::Write(scope) => {
                self.push("write(");
                self.print_term(scope, Prec::Top);
                self.push(")");
            }
            Effect::Attest(aref) => {
                self.push("attest(");
                self.print_authority_ref(aref);
                self.push(")");
            }
            Effect::Authority(aref) => {
                self.push("authority(");
                self.print_authority_ref(aref);
                self.push(")");
            }
            Effect::Oracle(oref) => {
                self.push("oracle(");
                self.print_oracle_ref(oref);
                self.push(")");
            }
            Effect::Fuel(level, amount) => {
                self.push("fuel(");
                self.print_level(level);
                self.push(", ");
                self.push(&amount.to_string());
                self.push(")");
            }
            Effect::SanctionsQuery => self.push("sanctions_query"),
            Effect::Discretion(aref) => {
                self.push("discretion(");
                self.print_authority_ref(aref);
                self.push(")");
            }
        }
    }

    fn print_effect_row(&mut self, row: &EffectRow) {
        match row {
            EffectRow::Empty => {
                self.push("[∅]");
            }
            EffectRow::Effects(effs) => {
                self.push("[");
                for (i, eff) in effs.iter().enumerate() {
                    if i > 0 {
                        self.push(", ");
                    }
                    self.print_effect(eff);
                }
                self.push("]");
            }
            EffectRow::Var(index) => {
                self.push("ρ");
                self.push(&index.to_string());
            }
            EffectRow::Join(a, b) => {
                self.print_effect_row(a);
                self.push(" ⊕ ");
                self.print_effect_row(b);
            }
            EffectRow::BranchSensitive(inner) => {
                self.push("⟨branch_sensitive⟩ ");
                self.print_effect_row(inner);
            }
        }
    }

    // -- TimeTerm printing --

    fn print_time_term(&mut self, tt: &TimeTerm) {
        match tt {
            TimeTerm::Literal(TimeLiteral { iso8601 }) => {
                self.push("τ{");
                self.push(iso8601);
                self.push("}");
            }
            TimeTerm::Var { name, index } => {
                self.push(&name.name);
                self.push("@");
                self.push(&index.to_string());
            }
            TimeTerm::AsOf0(inner) => {
                self.push("asof₀ ");
                self.parens_if(Self::term_prec(inner) < Prec::Atom, Prec::Top, inner);
            }
            TimeTerm::AsOf1(inner) => {
                self.push("asof₁ ");
                self.parens_if(Self::term_prec(inner) < Prec::Atom, Prec::Top, inner);
            }
            TimeTerm::Lift0(inner) => {
                self.push("lift₀(");
                self.print_time_term(inner);
                self.push(")");
            }
            TimeTerm::Derive1 { time, witness } => {
                self.push("derive₁(");
                self.print_time_term(time);
                self.push(", ");
                self.print_term(&witness.term, Prec::Top);
                self.push(")");
            }
        }
    }

    // -- Pattern printing --

    fn print_pattern(&mut self, pat: &Pattern) {
        match pat {
            Pattern::Constructor {
                constructor,
                binders,
            } => {
                self.print_constructor(constructor);
                for b in binders {
                    self.push(" ");
                    self.push(&b.name);
                }
            }
            Pattern::Wildcard => {
                self.push("_");
            }
        }
    }

    fn print_constructor(&mut self, ctor: &Constructor) {
        self.print_qual_ident(&ctor.name);
    }

    // -- Scope constraint printing --

    fn print_scope_constraint(&mut self, sc: &ScopeConstraint) {
        self.push(" scope {");
        self.indent();
        for field in &sc.fields {
            self.newline();
            match field {
                ScopeField::Corridor(qi) => {
                    self.push("corridor: ");
                    self.print_qual_ident(qi);
                }
                ScopeField::TimeWindow { from, to } => {
                    self.push("time_window: ");
                    self.print_time_term(from);
                    self.push(" .. ");
                    self.print_time_term(to);
                }
                ScopeField::Jurisdiction(qi) => {
                    self.push("jurisdiction: ");
                    self.print_qual_ident(qi);
                }
                ScopeField::EntityClass(term) => {
                    self.push("entity_class: ");
                    self.print_term(term, Prec::Top);
                }
            }
        }
        self.dedent();
        self.newline();
        self.push("}");
    }

    // -- Principle / Precedent ref printing --

    fn print_principle_ref(&mut self, pref: &PrincipleRef) {
        match pref {
            PrincipleRef::Named(qi) => self.print_qual_ident(qi),
            PrincipleRef::ContentAddressed(cr) => self.print_content_ref(cr),
        }
    }

    fn print_precedent_ref(&mut self, pref: &PrecedentRef) {
        self.print_content_ref(&pref.content);
    }

    // -- Main term printer --

    fn print_term(&mut self, term: &Term, ctx_prec: Prec) {
        let own_prec = Self::term_prec(term);
        let needs_parens = own_prec < ctx_prec;

        match term {
            // ── Atoms ────────────────────────────────────────────────
            Term::Var { name, index } => {
                self.push(&name.name);
                self.push("@");
                self.push(&index.to_string());
            }

            Term::Constant(qi) => {
                self.print_qual_ident(qi);
            }

            Term::Sort(sort) => {
                self.print_sort(sort);
            }

            Term::Pair { fst, snd } => {
                self.push("⟨");
                self.print_term(fst, Prec::Top);
                self.push(", ");
                self.print_term(snd, Prec::Top);
                self.push("⟩");
            }

            Term::ContentRefTerm(cr) => {
                self.print_content_ref(cr);
            }

            Term::IntLit(value) => {
                self.push(&value.to_string());
            }

            Term::RatLit(numerator, denominator) => {
                self.push(&numerator.to_string());
                self.push("/");
                self.push(&denominator.to_string());
            }

            Term::StringLit(value) => {
                let escaped = format!("{:?}", value);
                self.push(&escaped);
            }

            Term::AxiomUse { axiom } => {
                self.push("axiom ");
                self.print_qual_ident(axiom);
            }

            // ── Application-level ────────────────────────────────────
            Term::App { func, arg } => {
                if needs_parens {
                    self.push("(");
                }
                // func is left-associative at App prec
                self.parens_if(Self::term_prec(func) < Prec::App, Prec::Top, func);
                self.push(" ");
                // arg needs parens if it's not atomic
                self.parens_if(Self::term_prec(arg) < Prec::Atom, Prec::Top, arg);
                if needs_parens {
                    self.push(")");
                }
            }

            Term::Proj { first, pair } => {
                if needs_parens {
                    self.push("(");
                }
                if *first {
                    self.push("π₁ ");
                } else {
                    self.push("π₂ ");
                }
                self.parens_if(Self::term_prec(pair) < Prec::Atom, Prec::Top, pair);
                if needs_parens {
                    self.push(")");
                }
            }

            Term::InductiveIntro { constructor, args } => {
                if needs_parens && !args.is_empty() {
                    self.push("(");
                }
                self.print_constructor(constructor);
                for a in args {
                    self.push(" ");
                    self.parens_if(Self::term_prec(a) < Prec::Atom, Prec::Top, a);
                }
                if needs_parens && !args.is_empty() {
                    self.push(")");
                }
            }

            Term::SanctionsDominance { proof } => {
                if needs_parens {
                    self.push("(");
                }
                self.push("sanctions-dominance(");
                self.print_term(proof, Prec::Top);
                self.push(")");
                if needs_parens {
                    self.push(")");
                }
            }

            Term::DefeatElim { rule } => {
                if needs_parens {
                    self.push("(");
                }
                self.push("defeat ");
                self.parens_if(Self::term_prec(rule) < Prec::Atom, Prec::Top, rule);
                if needs_parens {
                    self.push(")");
                }
            }

            Term::Lift0 { time } => {
                if needs_parens {
                    self.push("(");
                }
                self.push("lift₀(");
                self.print_term(time, Prec::Top);
                self.push(")");
                if needs_parens {
                    self.push(")");
                }
            }

            Term::Derive1 { time, witness } => {
                if needs_parens {
                    self.push("(");
                }
                self.push("derive₁(");
                self.print_term(time, Prec::Top);
                self.push(", ");
                self.print_term(witness, Prec::Top);
                self.push(")");
                if needs_parens {
                    self.push(")");
                }
            }

            // ── Binders ──────────────────────────────────────────────
            Term::Lambda {
                binder,
                domain,
                body,
            } => {
                if needs_parens {
                    self.push("(");
                }
                self.push("λ(");
                self.push(&binder.name);
                self.push(" : ");
                self.print_term(domain, Prec::Top);
                self.push("). ");
                self.print_term(body, Prec::Top);
                if needs_parens {
                    self.push(")");
                }
            }

            Term::Pi {
                binder,
                domain,
                effect_row,
                codomain,
            } => {
                if needs_parens {
                    self.push("(");
                }
                // Non-dependent arrow sugar: Π(_ : A) [∅]. B  →  A → B
                if binder.name == "_"
                    && (effect_row.is_none() || matches!(effect_row, Some(EffectRow::Empty)))
                {
                    // Left side needs parens if it's itself an arrow (right-associative)
                    self.parens_if(Self::is_nondep_arrow(domain), Prec::Top, domain);
                    self.push(" → ");
                    self.print_term(codomain, Prec::Top);
                } else {
                    self.push("Π(");
                    self.push(&binder.name);
                    self.push(" : ");
                    self.print_term(domain, Prec::Top);
                    self.push(")");
                    if let Some(row) = effect_row {
                        self.push(" ");
                        self.print_effect_row(row);
                    }
                    self.push(". ");
                    self.print_term(codomain, Prec::Top);
                }
                if needs_parens {
                    self.push(")");
                }
            }

            Term::Sigma {
                binder,
                fst_ty,
                snd_ty,
            } => {
                if needs_parens {
                    self.push("(");
                }
                // Non-dependent product sugar: Σ(_ : A). B  →  A × B
                if binder.name == "_" {
                    self.parens_if(Self::is_nondep_product(fst_ty), Prec::Top, fst_ty);
                    self.push(" × ");
                    self.print_term(snd_ty, Prec::Top);
                } else {
                    self.push("Σ(");
                    self.push(&binder.name);
                    self.push(" : ");
                    self.print_term(fst_ty, Prec::Top);
                    self.push("). ");
                    self.print_term(snd_ty, Prec::Top);
                }
                if needs_parens {
                    self.push(")");
                }
            }

            Term::Annot { term: inner, ty } => {
                // Always parenthesized: `(e : τ)`
                self.push("(");
                self.print_term(inner, Prec::Top);
                self.push(" : ");
                self.print_term(ty, Prec::Top);
                self.push(")");
            }

            Term::Let {
                binder,
                ty,
                val,
                body,
            } => {
                if needs_parens {
                    self.push("(");
                }
                self.push("let ");
                self.push(&binder.name);
                self.push(" : ");
                self.print_term(ty, Prec::Top);
                self.push(" := ");
                self.print_term(val, Prec::Top);
                self.push(" in");
                self.indent();
                self.newline();
                self.print_term(body, Prec::Top);
                self.dedent();
                if needs_parens {
                    self.push(")");
                }
            }

            Term::Match {
                scrutinee,
                return_ty,
                branches,
            } => {
                if needs_parens {
                    self.push("(");
                }
                self.push("match ");
                self.print_term(scrutinee, Prec::Top);
                self.push(" return ");
                self.print_term(return_ty, Prec::Top);
                self.push(" with");
                self.indent();
                for Branch { pattern, body } in branches {
                    self.newline();
                    self.push("| ");
                    self.print_pattern(pattern);
                    self.push(" ⇒ ");
                    self.print_term(body, Prec::Top);
                }
                self.dedent();
                self.newline();
                self.push("end");
                if needs_parens {
                    self.push(")");
                }
            }

            Term::Rec { binder, ty, body } => {
                if needs_parens {
                    self.push("(");
                }
                self.push("fix ");
                self.push(&binder.name);
                self.push(" : ");
                self.print_term(ty, Prec::Top);
                self.push(" := ");
                self.print_term(body, Prec::Top);
                if needs_parens {
                    self.push(")");
                }
            }

            // ── Temporal modals ──────────────────────────────────────
            Term::ModalAt { time, body } => {
                if needs_parens {
                    self.push("(");
                }
                self.push("@");
                self.print_time_term_parens(time);
                self.push(" ");
                self.print_term(body, Prec::Top);
                if needs_parens {
                    self.push(")");
                }
            }

            Term::ModalEventually { time, body } => {
                if needs_parens {
                    self.push("(");
                }
                self.push("◇");
                self.print_time_term_parens(time);
                self.push(" ");
                self.print_term(body, Prec::Top);
                if needs_parens {
                    self.push(")");
                }
            }

            Term::ModalAlways { from, to, body } => {
                if needs_parens {
                    self.push("(");
                }
                self.push("□[");
                self.print_time_term(from);
                self.push(", ");
                self.print_time_term(to);
                self.push("] ");
                self.print_term(body, Prec::Top);
                if needs_parens {
                    self.push(")");
                }
            }

            // ── Tribunal modal ───────────────────────────────────────
            Term::ModalIntro { tribunal, body } => {
                if needs_parens {
                    self.push("(");
                }
                self.push("⟦");
                self.print_tribunal_ref(tribunal);
                self.push("⟧ ");
                self.print_term(body, Prec::Top);
                if needs_parens {
                    self.push(")");
                }
            }

            Term::ModalElim {
                from_tribunal,
                to_tribunal,
                term: inner,
                witness,
            } => {
                if needs_parens {
                    self.push("(");
                }
                self.push("coerce[");
                self.print_tribunal_ref(from_tribunal);
                self.push(" ⇒ ");
                self.print_tribunal_ref(to_tribunal);
                self.push("](");
                self.print_term(inner, Prec::Top);
                self.push(", ");
                self.print_term(witness, Prec::Top);
                self.push(")");
                if needs_parens {
                    self.push(")");
                }
            }

            // ── Defeasible ───────────────────────────────────────────
            Term::Defeasible(DefeasibleRule {
                name,
                base_ty,
                base_body,
                exceptions,
                lattice: _,
            }) => {
                if needs_parens {
                    self.push("(");
                }
                self.push("defeasible ");
                self.push(&name.name);
                self.push(" : ");
                self.print_term(base_ty, Prec::Top);
                self.push(" with");
                self.indent();
                self.newline();
                self.print_term(base_body, Prec::Top);
                for Exception {
                    guard,
                    body,
                    priority,
                    authority,
                } in exceptions
                {
                    self.newline();
                    self.push("unless ");
                    self.print_term(guard, Prec::Top);
                    self.push(" ⇒ ");
                    self.print_term(body, Prec::Top);
                    if let Some(p) = priority {
                        self.indent();
                        self.newline();
                        self.push("priority ");
                        self.push(&p.to_string());
                        self.dedent();
                    }
                    if let Some(auth) = authority {
                        self.indent();
                        self.newline();
                        self.push("authority ");
                        self.print_authority_ref(auth);
                        self.dedent();
                    }
                }
                self.dedent();
                self.newline();
                self.push("end");
                if needs_parens {
                    self.push(")");
                }
            }

            // ── Holes ────────────────────────────────────────────────
            Term::Hole(Hole {
                name,
                ty,
                authority,
                scope,
            }) => {
                if needs_parens {
                    self.push("(");
                }
                self.push("? ");
                match name {
                    Some(ident) => self.push(&ident.name),
                    None => self.push("_"),
                }
                self.push(" : ");
                self.print_term(ty, Prec::Top);
                self.push(" @ ");
                self.print_authority_ref(authority);
                if let Some(sc) = scope {
                    self.print_scope_constraint(sc);
                }
                if needs_parens {
                    self.push(")");
                }
            }

            Term::HoleFill {
                hole_name,
                filler,
                pcauth,
            } => {
                if needs_parens {
                    self.push("(");
                }
                self.push("fill(");
                match hole_name {
                    Some(ident) => self.push(&ident.name),
                    None => self.push("_"),
                }
                self.push(", ");
                self.print_term(filler, Prec::Top);
                self.push(", ");
                self.print_term(pcauth, Prec::Top);
                self.push(")");
                if needs_parens {
                    self.push(")");
                }
            }

            // ── Principle balance ────────────────────────────────────
            Term::PrincipleBalance(PrincipleBalancingStep {
                principles,
                precedents,
                verdict,
                rationale,
            }) => {
                if needs_parens {
                    self.push("(");
                }
                self.push("balance {");
                self.indent();
                self.newline();
                self.push("principles: [");
                for (i, p) in principles.iter().enumerate() {
                    if i > 0 {
                        self.push(", ");
                    }
                    self.print_principle_ref(p);
                }
                self.push("],");
                self.newline();
                self.push("precedents: [");
                for (i, p) in precedents.iter().enumerate() {
                    if i > 0 {
                        self.push(", ");
                    }
                    self.print_precedent_ref(p);
                }
                self.push("],");
                self.newline();
                self.push("verdict: ");
                self.print_term(verdict, Prec::Top);
                self.push(",");
                self.newline();
                self.push("rationale: ");
                self.print_term(rationale, Prec::Top);
                self.dedent();
                self.newline();
                self.push("}");
                if needs_parens {
                    self.push(")");
                }
            }

            // ── Unlock ──────────────────────────────────────────────
            Term::Unlock { effect_row, body } => {
                if needs_parens {
                    self.push("(");
                }
                self.push("unlock ");
                self.parens_if(
                    Self::term_prec(effect_row) < Prec::Atom,
                    Prec::Top,
                    effect_row,
                );
                self.push(" in ");
                self.print_term(body, Prec::Top);
                if needs_parens {
                    self.push(")");
                }
            }
        }
    }

    /// Print a time term, wrapping in parens if it's compound.
    fn print_time_term_parens(&mut self, tt: &TimeTerm) {
        match tt {
            TimeTerm::Literal(_) | TimeTerm::Var { .. } => {
                self.print_time_term(tt);
            }
            _ => {
                self.push("(");
                self.print_time_term(tt);
                self.push(")");
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;

    // -- Helpers --

    fn ident(s: &str) -> Ident {
        Ident::new(s)
    }

    fn qi(s: &str) -> QualIdent {
        QualIdent::simple(s)
    }

    fn qi_multi(segs: &[&str]) -> QualIdent {
        QualIdent::new(segs.iter().copied())
    }

    fn var(name: &str, index: u32) -> Term {
        Term::Var {
            name: ident(name),
            index,
        }
    }

    fn constant(name: &str) -> Term {
        Term::Constant(qi(name))
    }

    fn type_sort(level: u64) -> Term {
        Term::Sort(Sort::Type(Level::Nat(level)))
    }

    fn b(t: Term) -> Box<Term> {
        Box::new(t)
    }

    // -- Test 1: Lambda round-trip --

    #[test]
    fn lambda_round_trip() {
        let term = Term::Lambda {
            binder: ident("x"),
            domain: b(type_sort(0)),
            body: b(var("x", 0)),
        };
        let out = pretty_print(&term);
        assert_eq!(out, "λ(x : Type_0). x@0");
    }

    // -- Test 2: Pi with effects --

    #[test]
    fn pi_with_effects() {
        let term = Term::Pi {
            binder: ident("e"),
            domain: b(constant("Entity")),
            effect_row: Some(EffectRow::Effects(vec![
                Effect::Read,
                Effect::Oracle(OracleRef::Named(qi("ownership_oracle"))),
            ])),
            codomain: b(constant("Prop")),
        };
        let out = pretty_print(&term);
        assert_eq!(out, "Π(e : Entity) [read, oracle(ownership_oracle)]. Prop");
    }

    // -- Test 3: Nested application — minimal parens --

    #[test]
    fn nested_application_minimal_parens() {
        // f x y  — no parens needed (left-associative)
        let term = Term::App {
            func: b(Term::App {
                func: b(var("f", 2)),
                arg: b(var("x", 1)),
            }),
            arg: b(var("y", 0)),
        };
        let out = pretty_print(&term);
        assert_eq!(out, "f@2 x@1 y@0");
    }

    // -- Test 4: Application where arg is application (needs parens) --

    #[test]
    fn application_arg_needs_parens() {
        // f (g x)
        let term = Term::App {
            func: b(var("f", 1)),
            arg: b(Term::App {
                func: b(var("g", 2)),
                arg: b(var("x", 0)),
            }),
        };
        let out = pretty_print(&term);
        assert_eq!(out, "f@1 (g@2 x@0)");
    }

    // -- Test 5: Let binding with indentation --

    #[test]
    fn let_binding() {
        let term = Term::Let {
            binder: ident("y"),
            ty: b(type_sort(0)),
            val: b(var("x", 0)),
            body: b(var("y", 0)),
        };
        let out = pretty_print(&term);
        assert_eq!(out, "let y : Type_0 := x@0 in\n  y@0");
    }

    // -- Test 6: Match arms with indentation --

    #[test]
    fn match_arms() {
        let term = Term::Match {
            scrutinee: b(var("n", 0)),
            return_ty: b(constant("Nat")),
            branches: vec![
                Branch {
                    pattern: Pattern::Constructor {
                        constructor: Constructor::new(qi("Zero")),
                        binders: vec![],
                    },
                    body: Term::Var {
                        name: ident("zero"),
                        index: 0,
                    },
                },
                Branch {
                    pattern: Pattern::Constructor {
                        constructor: Constructor::new(qi("Succ")),
                        binders: vec![ident("m")],
                    },
                    body: var("m", 0),
                },
            ],
        };
        let out = pretty_print(&term);
        let expected = "match n@0 return Nat with\n  | Zero ⇒ zero@0\n  | Succ m ⇒ m@0\nend";
        assert_eq!(out, expected);
    }

    // -- Test 7: Defeasible with exceptions --

    #[test]
    fn defeasible_with_exceptions() {
        let term = Term::Defeasible(DefeasibleRule {
            name: ident("r"),
            base_ty: b(constant("report_required")),
            base_body: b(constant("base_rule")),
            exceptions: vec![Exception {
                guard: b(constant("is_market_maker")),
                body: b(constant("mm_exception")),
                priority: Some(10),
                authority: Some(AuthorityRef::Named(qi_multi(&["regulator", "sec"]))),
            }],
            lattice: None,
        });
        let out = pretty_print(&term);
        let expected = "\
defeasible r : report_required with
  base_rule
  unless is_market_maker ⇒ mm_exception
    priority 10
    authority regulator.sec
end";
        assert_eq!(out, expected);
    }

    // -- Test 8: Hole with scope --

    #[test]
    fn hole_with_scope() {
        let term = Term::Hole(Hole {
            name: Some(ident("h_beyond")),
            ty: b(constant("BeyondHorizonClaim")),
            authority: AuthorityRef::Named(qi_multi(&["regulator", "fincen"])),
            scope: Some(ScopeConstraint {
                fields: vec![
                    ScopeField::Jurisdiction(qi("us")),
                    ScopeField::EntityClass(b(constant("Entity.LLC"))),
                ],
            }),
        });
        let out = pretty_print(&term);
        let expected = "\
? h_beyond : BeyondHorizonClaim @ regulator.fincen scope {
  jurisdiction: us
  entity_class: Entity.LLC
}";
        assert_eq!(out, expected);
    }

    // -- Test 9: Temporal term --

    #[test]
    fn temporal_at_time() {
        let term = Term::ModalAt {
            time: TimeTerm::AsOf0(b(var("txn", 0))),
            body: b(constant("compliant")),
        };
        let out = pretty_print(&term);
        assert_eq!(out, "@(asof₀ txn@0) compliant");
    }

    // -- Test 10: Content ref --

    #[test]
    fn content_ref() {
        let hash = "abcdef1234567890abcdef1234567890abcdef1234567890abcdef1234567890";
        let term = Term::ContentRefTerm(ContentRef::new(hash));
        let out = pretty_print(&term);
        assert_eq!(
            out,
            "lex://blake3:abcdef1234567890abcdef1234567890abcdef1234567890abcdef1234567890"
        );
    }

    // -- Test 11: Empty effect row on Pi --

    #[test]
    fn empty_effect_row() {
        let term = Term::Pi {
            binder: ident("x"),
            domain: b(constant("A")),
            effect_row: Some(EffectRow::Empty),
            codomain: b(constant("B")),
        };
        let out = pretty_print(&term);
        assert_eq!(out, "Π(x : A) [∅]. B");
    }

    // -- Test 12: Non-dependent arrow (right-associative) --

    #[test]
    fn arrow_right_assoc() {
        // A → B → C  (right-associative, no parens)
        let term = Term::Pi {
            binder: ident("_"),
            domain: b(constant("A")),
            effect_row: None,
            codomain: b(Term::Pi {
                binder: ident("_"),
                domain: b(constant("B")),
                effect_row: None,
                codomain: b(constant("C")),
            }),
        };
        let out = pretty_print(&term);
        assert_eq!(out, "A → B → C");
    }

    // -- Test 13: Non-dependent arrow left needs parens --

    #[test]
    fn arrow_left_associativity_parens() {
        // (A → B) → C  needs parens on the left
        let term = Term::Pi {
            binder: ident("_"),
            domain: b(Term::Pi {
                binder: ident("_"),
                domain: b(constant("A")),
                effect_row: None,
                codomain: b(constant("B")),
            }),
            effect_row: None,
            codomain: b(constant("C")),
        };
        let out = pretty_print(&term);
        assert_eq!(out, "(A → B) → C");
    }

    // -- Test 14: Tribunal intro --

    #[test]
    fn tribunal_intro() {
        let term = Term::ModalIntro {
            tribunal: TribunalRef::Named(qi_multi(&["regulator", "sec_13d"])),
            body: b(constant("report_required")),
        };
        let out = pretty_print(&term);
        assert_eq!(out, "⟦regulator.sec_13d⟧ report_required");
    }

    // -- Test 15: Display trait delegates to pretty_print --

    #[test]
    fn display_delegates() {
        let term = var("x", 42);
        assert_eq!(format!("{}", term), "x@42");
    }

    // -- Test 16: Pair --

    #[test]
    fn pair_pretty() {
        let term = Term::Pair {
            fst: b(var("a", 0)),
            snd: b(var("b", 1)),
        };
        let out = pretty_print(&term);
        assert_eq!(out, "⟨a@0, b@1⟩");
    }

    // -- Test 17: Sigma type --

    #[test]
    fn sigma_type() {
        let term = Term::Sigma {
            binder: ident("owners"),
            fst_ty: b(constant("List")),
            snd_ty: b(constant("Valid")),
        };
        let out = pretty_print(&term);
        assert_eq!(out, "Σ(owners : List). Valid");
    }

    // -- Test 18: Fix (Rec) --

    #[test]
    fn fix_term() {
        let term = Term::Rec {
            binder: ident("traverse"),
            ty: b(constant("OwnershipGraph")),
            body: b(var("traverse", 0)),
        };
        let out = pretty_print(&term);
        assert_eq!(out, "fix traverse : OwnershipGraph := traverse@0");
    }

    // -- Test 19: Non-dependent product sugar --

    #[test]
    fn product_sugar() {
        let term = Term::Sigma {
            binder: ident("_"),
            fst_ty: b(constant("A")),
            snd_ty: b(constant("B")),
        };
        let out = pretty_print(&term);
        assert_eq!(out, "A × B");
    }
}
