//! Recursive descent parser for Core Lex.
//!
//! Consumes a token stream (from `crate::token`) and produces AST nodes
//! from `crate::ast`. Implements the grammar documented in
//! `docs/language-reference.md`.
//!
//! ## Precedence (tightest to loosest)
//!
//! 1. Atoms / parenthesised / binders / prefix operators
//! 2. Application (left-associative, juxtaposition)
//! 3. `×` / `*` product (left-associative)
//! 4. `→` / arrow (right-associative)
//!
//! ## Design choices
//!
//! - The parser is intentionally zero-copy over the token slice.
//! - De Bruijn indices are set to 0 at parse time; the `debruijn` module
//!   assigns real indices in a subsequent pass.
//! - `Term` nodes carry no spans (the AST is span-free for structural
//!   equality). The parser tracks spans internally for error reporting.
//!   Callers needing spans should wrap with `ast::Spanned<Term>` in a
//!   future enhancement.
//! - Comments are filtered from the token stream before parsing.

use crate::ast::{
    AuthorityRef, Branch, Constructor, ContentRef, DefeasibleRule, Effect, EffectRow, Exception,
    Hole, Ident, Level, OracleRef, Pattern, PrecedentRef, PrincipleBalancingStep, PrincipleRef,
    QualIdent, ScopeConstraint, ScopeField, Sort, Term, TimeTerm, TribunalRef,
};
use crate::token::{Span, Spanned, Token};
use std::fmt;

const MAX_DEPTH: usize = 192;

// ═══════════════════════════════════════════════════════════════════════
// Parse errors
// ═══════════════════════════════════════════════════════════════════════

/// Error produced by the parser.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    /// Span where the error was detected.
    pub span: Span,
    /// What the parser expected at this position.
    pub expected: String,
    /// What was actually found.
    pub found: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "parse error at {}:{}: expected {}, found {}",
            self.span.line, self.span.col, self.expected, self.found
        )
    }
}

impl std::error::Error for ParseError {}

// ═══════════════════════════════════════════════════════════════════════
// Parser state
// ═══════════════════════════════════════════════════════════════════════

/// Recursive descent parser for Core Lex.
struct Parser<'a> {
    tokens: &'a [Spanned<Token>],
    pos: usize,
}

impl<'a> Parser<'a> {
    fn new(tokens: &'a [Spanned<Token>]) -> Self {
        Self { tokens, pos: 0 }
    }

    // ── Token access ────────────────────────────────────────────────

    /// Peek at the current token without consuming.
    fn peek(&self) -> &Token {
        if self.pos < self.tokens.len() {
            &self.tokens[self.pos].0
        } else {
            &Token::Eof
        }
    }

    /// Peek at the current token's span.
    fn peek_span(&self) -> Span {
        if self.pos < self.tokens.len() {
            self.tokens[self.pos].1
        } else if !self.tokens.is_empty() {
            let last = self.tokens[self.tokens.len() - 1].1;
            Span::new(last.end, last.end, last.line, last.col + 1)
        } else {
            Span::new(0, 0, 1, 1)
        }
    }

    /// Advance past the current token and return it with its span.
    fn advance(&mut self) -> Spanned<Token> {
        if self.pos < self.tokens.len() {
            let tok = self.tokens[self.pos].clone();
            self.pos += 1;
            tok
        } else {
            (Token::Eof, self.peek_span())
        }
    }

    /// Consume the current token if it matches `expected`, else error.
    fn expect(&mut self, expected: &Token) -> Result<Span, ParseError> {
        let (tok, sp) = self.advance();
        if std::mem::discriminant(&tok) == std::mem::discriminant(expected) {
            Ok(sp)
        } else {
            Err(ParseError {
                span: sp,
                expected: format!("{}", expected),
                found: format!("{}", tok),
            })
        }
    }

    /// Consume and return the current token if it is an Ident.
    fn expect_ident(&mut self) -> Result<(String, Span), ParseError> {
        let (tok, sp) = self.advance();
        match tok {
            Token::Ident(s) => Ok((s, sp)),
            other => Err(ParseError {
                span: sp,
                expected: "identifier".to_string(),
                found: format!("{}", other),
            }),
        }
    }

    /// Consume an identifier and require that it matches `expected`.
    fn expect_named_ident(&mut self, expected: &str) -> Result<Span, ParseError> {
        let (name, span) = self.expect_ident()?;
        if name == expected {
            Ok(span)
        } else {
            Err(ParseError {
                span,
                expected: format!("identifier `{expected}`"),
                found: name,
            })
        }
    }

    /// Consume and return the current token if it is a Nat literal.
    fn expect_nat(&mut self) -> Result<(u64, Span), ParseError> {
        let (tok, sp) = self.advance();
        match tok {
            Token::Nat(n) => Ok((n, sp)),
            other => Err(ParseError {
                span: sp,
                expected: "natural number".to_string(),
                found: format!("{}", other),
            }),
        }
    }

    /// Check if current token matches without consuming.
    fn check(&self, tok: &Token) -> bool {
        std::mem::discriminant(self.peek()) == std::mem::discriminant(tok)
    }

    /// Consume if current token matches, returning true.
    fn eat(&mut self, tok: &Token) -> bool {
        if self.check(tok) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Build an error at the current position.
    fn error(&self, expected: &str) -> ParseError {
        ParseError {
            span: self.peek_span(),
            expected: expected.to_string(),
            found: format!("{}", self.peek()),
        }
    }

    fn next_depth(&self, depth: usize) -> Result<usize, ParseError> {
        if depth >= MAX_DEPTH {
            return Err(ParseError {
                span: self.peek_span(),
                expected: format!("term nesting depth <= {MAX_DEPTH}"),
                found: format!("recursion depth {depth} exceeded"),
            });
        }
        Ok(depth + 1)
    }

    // ── Parsing entry point ─────────────────────────────────────────

    /// Parse a complete term. This is the top-level entry.
    fn parse_term(&mut self, depth: usize) -> Result<Term, ParseError> {
        let next_depth = self.next_depth(depth)?;
        self.parse_arrow(next_depth)
    }

    // ── Precedence level: arrow (right-associative, loosest) ────────

    fn parse_arrow(&mut self, depth: usize) -> Result<Term, ParseError> {
        let next_depth = self.next_depth(depth)?;
        let lhs = self.parse_product(next_depth)?;

        if self.check(&Token::Arrow) {
            self.advance();
            let rhs = self.parse_arrow(next_depth)?; // right-associative
            Ok(Term::Pi {
                binder: Ident::new("_"),
                domain: Box::new(lhs),
                effect_row: None,
                codomain: Box::new(rhs),
            })
        } else {
            Ok(lhs)
        }
    }

    // ── Precedence level: product (left-associative) ────────────────

    fn parse_product(&mut self, depth: usize) -> Result<Term, ParseError> {
        let next_depth = self.next_depth(depth)?;
        let mut lhs = self.parse_app(next_depth)?;

        while self.check(&Token::Times) {
            self.advance();
            let rhs = self.parse_app(next_depth)?;
            lhs = Term::Sigma {
                binder: Ident::new("_"),
                fst_ty: Box::new(lhs),
                snd_ty: Box::new(rhs),
            };
        }

        Ok(lhs)
    }

    // ── Precedence level: application (left-associative, tightest) ──

    fn parse_app(&mut self, depth: usize) -> Result<Term, ParseError> {
        let next_depth = self.next_depth(depth)?;
        let mut func = self.parse_atom(next_depth)?;

        while self.is_atom_start() {
            let arg = self.parse_atom(next_depth)?;
            func = Term::App {
                func: Box::new(func),
                arg: Box::new(arg),
            };
        }

        Ok(func)
    }

    /// Returns true if the current token can start an atom.
    fn is_atom_start(&self) -> bool {
        matches!(
            self.peek(),
            Token::Ident(_)
                | Token::Nat(_)
                | Token::Int(_)
                | Token::Rat(_, _)
                | Token::StringLit(_)
                | Token::Hash(_)
                | Token::ContentRef(_)
                | Token::LevelVar(_)
                | Token::Lparen
                | Token::Langle
                | Token::Type
                | Token::Prop
                | Token::Rule
                | Token::Time0
                | Token::Time1
                | Token::Proj1
                | Token::Proj2
                | Token::Underscore
        )
    }

    // ── Atoms ───────────────────────────────────────────────────────

    fn parse_atom(&mut self, depth: usize) -> Result<Term, ParseError> {
        match self.peek().clone() {
            // ── Binders and keywords ────────────────────────────────
            Token::Lambda => self.parse_lambda(self.next_depth(depth)?),
            Token::Pi => self.parse_pi(self.next_depth(depth)?),
            Token::Sigma => self.parse_sigma(self.next_depth(depth)?),
            Token::Let => self.parse_let(self.next_depth(depth)?),
            Token::Match => self.parse_match(self.next_depth(depth)?),
            Token::Fix => self.parse_fix(self.next_depth(depth)?),
            Token::Defeasible => self.parse_defeasible(self.next_depth(depth)?),
            Token::Question => self.parse_hole(self.next_depth(depth)?),
            Token::Coerce => self.parse_coerce(self.next_depth(depth)?),
            Token::Axiom => self.parse_axiom_use(),
            Token::Fill => self.parse_fill(self.next_depth(depth)?),
            Token::Balance => self.parse_principle_balance(self.next_depth(depth)?),
            Token::Unlock => self.parse_unlock(self.next_depth(depth)?),
            Token::Defeat => self.parse_defeat(self.next_depth(depth)?),
            Token::SanctionsDominance => self.parse_sanctions_dominance(self.next_depth(depth)?),
            Token::AsOf0 => self.parse_asof0(self.next_depth(depth)?),
            Token::AsOf1 => self.parse_asof1(self.next_depth(depth)?),
            Token::Lift0 => self.parse_lift0(self.next_depth(depth)?),
            Token::Derive1 => self.parse_derive1(self.next_depth(depth)?),
            Token::Proj1 => self.parse_projection(self.next_depth(depth)?, true),
            Token::Proj2 => self.parse_projection(self.next_depth(depth)?, false),

            // ── Sorts ───────────────────────────────────────────────
            Token::Type => {
                self.advance();
                Ok(Term::Sort(Sort::Type(self.parse_sort_level()?)))
            }
            Token::Prop => {
                self.advance();
                Ok(Term::Sort(Sort::Prop))
            }
            Token::Rule => {
                self.advance();
                Ok(Term::Sort(Sort::Rule(self.parse_sort_level()?)))
            }

            // ── Temporal sorts ──────────────────────────────────────
            Token::Time0 | Token::Time1 => {
                // Time sorts are not Term variants directly; represent
                // as a constant for the parser. The type checker resolves.
                let tok = self.peek().clone();
                self.advance();
                let name = match tok {
                    Token::Time0 => "Time0",
                    Token::Time1 => "Time1",
                    _ => unreachable!(),
                };
                Ok(Term::Constant(QualIdent::simple(name)))
            }

            // ── Literals / constants ────────────────────────────────
            Token::Nat(_) | Token::Int(_) | Token::Rat(_, _) | Token::StringLit(_) => {
                // Literals are not first-class AST Term variants.
                // Represent as constants for now; the elaborator resolves.
                let (tok, _sp) = self.advance();
                let name = match tok {
                    Token::Nat(n) => format!("{}", n),
                    Token::Int(n) => format!("{}", n),
                    Token::Rat(p, q) => format!("{}/{}", p, q),
                    Token::StringLit(s) => format!("\"{}\"", s),
                    _ => unreachable!(),
                };
                Ok(Term::Constant(QualIdent::simple(&name)))
            }
            Token::Hash(h) => {
                let h = h.clone();
                self.advance();
                Ok(Term::ContentRefTerm(ContentRef::new(&h)))
            }
            Token::ContentRef(r) => {
                let r = r.clone();
                self.advance();
                Ok(Term::ContentRefTerm(ContentRef::new(&r)))
            }
            Token::LevelVar(_) => {
                let (tok, _sp) = self.advance();
                if let Token::LevelVar(v) = tok {
                    Ok(Term::Constant(QualIdent::simple(&v)))
                } else {
                    unreachable!()
                }
            }

            // ── Wildcard ────────────────────────────────────────────
            Token::Underscore => {
                self.advance();
                // Represent wildcard as a variable named "_" with index 0.
                Ok(Term::Var {
                    name: Ident::new("_"),
                    index: 0,
                })
            }

            // ── Identifier (possibly qualified, with De Bruijn) ─────
            Token::Ident(_) => self.parse_var_or_qual(),

            // ── Parenthesised expr or annotation ────────────────────
            Token::Lparen => self.parse_paren(self.next_depth(depth)?),

            // ── Tribunal modal introduction ────────────────────────
            Token::Lbracket
                if self.pos + 1 < self.tokens.len()
                    && matches!(self.tokens[self.pos + 1].0, Token::Lbracket) =>
            {
                self.parse_modal_intro(self.next_depth(depth)?)
            }

            // ── Angle-bracket pair ⟨a, b⟩ ───────────────────────────
            Token::Langle => self.parse_pair(self.next_depth(depth)?),

            // ── Unexpected token ────────────────────────────────────
            other => Err(ParseError {
                span: self.peek_span(),
                expected: "term".to_string(),
                found: format!("{}", other),
            }),
        }
    }

    fn parse_sort_level(&mut self) -> Result<Level, ParseError> {
        if self.eat(&Token::Underscore) {
            let (level, _) = self.expect_nat()?;
            Ok(Level::Nat(level))
        } else {
            Ok(Level::Nat(0))
        }
    }

    // ── Lambda ──────────────────────────────────────────────────────

    /// `λ(x : T). body`
    fn parse_lambda(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Lambda)?;
        self.expect(&Token::Lparen)?;
        let (binder, _) = self.expect_ident()?;
        self.expect(&Token::Colon)?;
        let next_depth = self.next_depth(depth)?;
        let domain = self.parse_term(next_depth)?;
        self.expect(&Token::Rparen)?;
        self.expect(&Token::Dot)?;
        let body = self.parse_term(next_depth)?;
        Ok(Term::Lambda {
            binder: Ident::new(&binder),
            domain: Box::new(domain),
            body: Box::new(body),
        })
    }

    // ── Pi type ─────────────────────────────────────────────────────

    /// `Π(x : T)[effects]. body`
    fn parse_pi(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Pi)?;
        self.expect(&Token::Lparen)?;
        let (binder, _) = self.expect_ident()?;
        self.expect(&Token::Colon)?;
        let next_depth = self.next_depth(depth)?;
        let domain = self.parse_term(next_depth)?;
        self.expect(&Token::Rparen)?;

        // Optional effect row: [effects]
        let effect_row = if self.check(&Token::Lbracket) {
            self.advance();
            let row = self.parse_effect_row(next_depth)?;
            self.expect(&Token::Rbracket)?;
            Some(row)
        } else {
            None
        };

        self.expect(&Token::Dot)?;
        let codomain = self.parse_term(next_depth)?;
        Ok(Term::Pi {
            binder: Ident::new(&binder),
            domain: Box::new(domain),
            effect_row,
            codomain: Box::new(codomain),
        })
    }

    // ── Sigma type ──────────────────────────────────────────────────

    /// `Σ(x : T). body`
    fn parse_sigma(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Sigma)?;
        self.expect(&Token::Lparen)?;
        let (binder, _) = self.expect_ident()?;
        self.expect(&Token::Colon)?;
        let next_depth = self.next_depth(depth)?;
        let fst_ty = self.parse_term(next_depth)?;
        self.expect(&Token::Rparen)?;
        self.expect(&Token::Dot)?;
        let snd_ty = self.parse_term(next_depth)?;
        Ok(Term::Sigma {
            binder: Ident::new(&binder),
            fst_ty: Box::new(fst_ty),
            snd_ty: Box::new(snd_ty),
        })
    }

    // ── Let ─────────────────────────────────────────────────────────

    /// `let x : T := e in body`
    fn parse_let(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Let)?;
        let (name, _) = self.expect_ident()?;
        self.expect(&Token::Colon)?;
        let next_depth = self.next_depth(depth)?;
        let ty = self.parse_term(next_depth)?;
        self.expect(&Token::ColonEq)?;
        let val = self.parse_term(next_depth)?;
        self.expect(&Token::In)?;
        let body = self.parse_term(next_depth)?;
        Ok(Term::Let {
            binder: Ident::new(&name),
            ty: Box::new(ty),
            val: Box::new(val),
            body: Box::new(body),
        })
    }

    // ── Match ───────────────────────────────────────────────────────

    /// `match e return T with | pat => body ...`
    fn parse_match(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Match)?;
        let next_depth = self.next_depth(depth)?;
        let scrutinee = self.parse_atom(next_depth)?;
        self.expect(&Token::Return)?;
        let return_ty = self.parse_atom(next_depth)?;
        self.expect(&Token::With)?;

        let mut branches = Vec::new();
        while self.check(&Token::Pipe) {
            branches.push(self.parse_branch(next_depth)?);
        }

        if branches.is_empty() {
            return Err(self.error("at least one match branch"));
        }

        // Optional `end` terminator.
        self.eat(&Token::End);

        Ok(Term::Match {
            scrutinee: Box::new(scrutinee),
            return_ty: Box::new(return_ty),
            branches,
        })
    }

    /// `| pattern => body`
    fn parse_branch(&mut self, depth: usize) -> Result<Branch, ParseError> {
        self.expect(&Token::Pipe)?;
        let pattern = self.parse_pattern()?;
        self.expect(&Token::DoubleArrow)?;
        let body = self.parse_term(self.next_depth(depth)?)?;
        Ok(Branch { pattern, body })
    }

    /// Pattern: `Constructor x y z` or `_`.
    fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        if self.check(&Token::Underscore) {
            self.advance();
            return Ok(Pattern::Wildcard);
        }

        let (name, _) = self.expect_ident()?;
        let mut binders = Vec::new();

        // Collect binder identifiers until we see `⇒`.
        while let Token::Ident(_) = self.peek() {
            let (b, _) = self.expect_ident()?;
            binders.push(Ident::new(&b));
        }

        Ok(Pattern::Constructor {
            constructor: Constructor::new(QualIdent::simple(&name)),
            binders,
        })
    }

    // ── Fix (Rec) ───────────────────────────────────────────────────

    /// `fix f : T := body`
    fn parse_fix(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Fix)?;
        let (name, _) = self.expect_ident()?;
        self.expect(&Token::Colon)?;
        let next_depth = self.next_depth(depth)?;
        let ty = self.parse_term(next_depth)?;
        self.expect(&Token::ColonEq)?;
        let body = self.parse_term(next_depth)?;
        Ok(Term::Rec {
            binder: Ident::new(&name),
            ty: Box::new(ty),
            body: Box::new(body),
        })
    }

    // ── Defeasible ──────────────────────────────────────────────────

    /// `defeasible r : T with unless g => e priority p ... end`
    fn parse_defeasible(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Defeasible)?;
        let (name, _) = self.expect_ident()?;
        self.expect(&Token::Colon)?;
        let next_depth = self.next_depth(depth)?;
        let base_ty = self.parse_term(next_depth)?;
        self.expect(&Token::With)?;

        let mut exceptions = Vec::new();
        while self.check(&Token::Unless) {
            exceptions.push(self.parse_exception(next_depth)?);
        }

        self.expect(&Token::End)?;

        // The base body is implicit from the defeasible declaration;
        // at parse time we represent it as a Var referencing the rule name.
        let base_body = Term::Var {
            name: Ident::new(&name),
            index: 0,
        };

        Ok(Term::Defeasible(DefeasibleRule {
            name: Ident::new(&name),
            base_ty: Box::new(base_ty),
            base_body: Box::new(base_body),
            exceptions,
            lattice: None,
        }))
    }

    fn parse_axiom_use(&mut self) -> Result<Term, ParseError> {
        self.expect(&Token::Axiom)?;
        let axiom = self.parse_qual_ident()?;
        Ok(Term::AxiomUse { axiom })
    }

    fn parse_fill(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Fill)?;
        self.expect(&Token::Lparen)?;
        let hole_name = if self.check(&Token::Underscore) {
            self.advance();
            None
        } else {
            let (name, _) = self.expect_ident()?;
            Some(Ident::new(&name))
        };
        self.expect(&Token::Comma)?;
        let next_depth = self.next_depth(depth)?;
        let filler = self.parse_term(next_depth)?;
        self.expect(&Token::Comma)?;
        let pcauth = self.parse_term(next_depth)?;
        self.expect(&Token::Rparen)?;
        Ok(Term::HoleFill {
            hole_name,
            filler: Box::new(filler),
            pcauth: Box::new(pcauth),
        })
    }

    /// `unless guard => body priority n authority A`
    fn parse_exception(&mut self, depth: usize) -> Result<Exception, ParseError> {
        self.expect(&Token::Unless)?;
        let next_depth = self.next_depth(depth)?;
        let guard = self.parse_atom(next_depth)?;
        self.expect(&Token::DoubleArrow)?;
        let body = self.parse_term(next_depth)?;

        let priority = if self.check(&Token::Priority) {
            self.advance();
            let (n, _) = self.expect_nat()?;
            Some(n as u32)
        } else {
            None
        };

        let authority = if let Token::Ident(ref s) = self.peek() {
            if s == "authority" {
                self.advance();
                let (a, _) = self.expect_ident()?;
                Some(AuthorityRef::Named(QualIdent::simple(&a)))
            } else {
                None
            }
        } else {
            None
        };

        Ok(Exception {
            guard: Box::new(guard),
            body: Box::new(body),
            priority,
            authority,
        })
    }

    // ── Hole ────────────────────────────────────────────────────────

    /// `? h : T @ A scope { ... }` or `?_ : T @ A`
    fn parse_hole(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Question)?;

        // Hole name: either an identifier or `_` (anonymous).
        let name = if self.check(&Token::Underscore) {
            self.advance();
            None
        } else if let Token::Ident(_) = self.peek() {
            let (n, _) = self.expect_ident()?;
            Some(Ident::new(&n))
        } else {
            None
        };

        self.expect(&Token::Colon)?;
        let next_depth = self.next_depth(depth)?;
        let ty = self.parse_term(next_depth)?;
        self.expect(&Token::At)?;
        let (authority_name, _) = self.expect_ident()?;
        let authority = AuthorityRef::Named(QualIdent::simple(&authority_name));

        // Optionally parse `scope { ... }`.
        let scope = if let Token::Ident(ref s) = self.peek() {
            if s == "scope" {
                self.advance();
                Some(self.parse_scope_constraint(next_depth)?)
            } else {
                None
            }
        } else {
            None
        };

        Ok(Term::Hole(Hole {
            name,
            ty: Box::new(ty),
            authority,
            scope,
        }))
    }

    /// `{ corridor : X, jurisdiction : Y, ... }`
    fn parse_scope_constraint(&mut self, depth: usize) -> Result<ScopeConstraint, ParseError> {
        self.expect(&Token::Lbrace)?;
        let mut fields = Vec::new();

        while !self.check(&Token::Rbrace) && !self.check(&Token::Eof) {
            let (field_name, _) = self.expect_ident()?;
            self.expect(&Token::Colon)?;
            let field = match field_name.as_str() {
                "corridor" => {
                    let (v, _) = self.expect_ident()?;
                    ScopeField::Corridor(QualIdent::simple(&v))
                }
                "jurisdiction" => {
                    let (v, _) = self.expect_ident()?;
                    ScopeField::Jurisdiction(QualIdent::simple(&v))
                }
                "entity_class" => {
                    let term = self.parse_atom(self.next_depth(depth)?)?;
                    ScopeField::EntityClass(Box::new(term))
                }
                "time_window" => {
                    let next_depth = self.next_depth(depth)?;
                    let start_term = self.parse_atom(next_depth)?;
                    self.expect(&Token::Dot)?;
                    self.expect(&Token::Dot)?;
                    let end_term = self.parse_atom(next_depth)?;
                    // Wrap terms as TimeTerm::AsOf0 as a reasonable default
                    // for parsed time terms. The type checker resolves.
                    ScopeField::TimeWindow {
                        from: TimeTerm::AsOf0(Box::new(start_term)),
                        to: TimeTerm::AsOf0(Box::new(end_term)),
                    }
                }
                _ => {
                    return Err(ParseError {
                        span: self.peek_span(),
                        expected: "scope field (corridor, jurisdiction, entity_class, time_window)"
                            .to_string(),
                        found: field_name,
                    });
                }
            };
            fields.push(field);
            self.eat(&Token::Comma);
        }

        self.expect(&Token::Rbrace)?;
        Ok(ScopeConstraint { fields })
    }

    fn parse_principle_balance(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Balance)?;
        self.expect(&Token::Lbrace)?;

        self.expect_named_ident("principles")?;
        self.expect(&Token::Colon)?;
        let principles = self.parse_principle_refs()?;
        self.expect(&Token::Comma)?;

        self.expect_named_ident("precedents")?;
        self.expect(&Token::Colon)?;
        let precedents = self.parse_precedent_refs()?;
        self.expect(&Token::Comma)?;

        self.expect_named_ident("verdict")?;
        self.expect(&Token::Colon)?;
        let next_depth = self.next_depth(depth)?;
        let verdict = self.parse_term(next_depth)?;
        self.expect(&Token::Comma)?;

        self.expect_named_ident("rationale")?;
        self.expect(&Token::Colon)?;
        let rationale = self.parse_term(next_depth)?;

        self.expect(&Token::Rbrace)?;
        Ok(Term::PrincipleBalance(PrincipleBalancingStep {
            principles,
            precedents,
            verdict: Box::new(verdict),
            rationale: Box::new(rationale),
        }))
    }

    // ── Modal coercion ──────────────────────────────────────────────

    fn parse_modal_intro(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Lbracket)?;
        self.expect(&Token::Lbracket)?;
        let tribunal = self.parse_tribunal_ref()?;
        self.expect(&Token::Rbracket)?;
        self.expect(&Token::Rbracket)?;
        let body = self.parse_term(self.next_depth(depth)?)?;
        Ok(Term::ModalIntro {
            tribunal,
            body: Box::new(body),
        })
    }

    /// `coerce[T ⇒ T'] e`
    fn parse_coerce(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Coerce)?;
        self.expect(&Token::Lbracket)?;
        let (from_name, _) = self.expect_ident()?;
        self.expect(&Token::DoubleArrow)?;
        let (to_name, _) = self.expect_ident()?;
        self.expect(&Token::Rbracket)?;
        let body = self.parse_atom(self.next_depth(depth)?)?;

        // The witness is the second argument; for now parse one arg.
        // Full form: `coerce[T ⇒ T'](e, witness)`. We support both the
        // simplified `coerce[T ⇒ T'] e` (witness is implicit) and can be
        // extended later.
        Ok(Term::ModalElim {
            from_tribunal: TribunalRef::Named(QualIdent::simple(&from_name)),
            to_tribunal: TribunalRef::Named(QualIdent::simple(&to_name)),
            term: Box::new(body),
            witness: Box::new(Term::Var {
                name: Ident::new("_coerce_witness"),
                index: 0,
            }),
        })
    }

    /// `π₁ e` or `π₂ e`
    fn parse_projection(&mut self, depth: usize, first: bool) -> Result<Term, ParseError> {
        if first {
            self.expect(&Token::Proj1)?;
        } else {
            self.expect(&Token::Proj2)?;
        }
        let pair = self.parse_atom(self.next_depth(depth)?)?;
        Ok(Term::Proj {
            first,
            pair: Box::new(pair),
        })
    }

    // ── Temporal terms ──────────────────────────────────────────────

    /// `asof₀ e`
    fn parse_asof0(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::AsOf0)?;
        let body = self.parse_atom(self.next_depth(depth)?)?;
        // asof₀ is a temporal operation that produces a ModalAt term
        // with the AsOf0 time. We represent it directly in the term.
        Ok(Term::ModalAt {
            time: TimeTerm::AsOf0(Box::new(body)),
            body: Box::new(Term::Sort(Sort::Prop)),
        })
    }

    /// `asof₁ e`
    fn parse_asof1(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::AsOf1)?;
        let body = self.parse_atom(self.next_depth(depth)?)?;
        Ok(Term::ModalAt {
            time: TimeTerm::AsOf1(Box::new(body)),
            body: Box::new(Term::Sort(Sort::Prop)),
        })
    }

    /// `lift₀(e)`
    fn parse_lift0(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Lift0)?;
        self.expect(&Token::Lparen)?;
        let body = self.parse_term(self.next_depth(depth)?)?;
        self.expect(&Token::Rparen)?;
        Ok(Term::Lift0 {
            time: Box::new(body),
        })
    }

    /// `derive₁(e, w)`
    fn parse_derive1(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Derive1)?;
        self.expect(&Token::Lparen)?;
        let next_depth = self.next_depth(depth)?;
        let time_term = self.parse_term(next_depth)?;
        self.expect(&Token::Comma)?;
        let witness = self.parse_term(next_depth)?;
        self.expect(&Token::Rparen)?;
        Ok(Term::Derive1 {
            time: Box::new(time_term),
            witness: Box::new(witness),
        })
    }

    fn parse_unlock(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Unlock)?;
        let next_depth = self.next_depth(depth)?;
        let effect_row = self.parse_term(next_depth)?;
        self.expect(&Token::In)?;
        let body = self.parse_term(next_depth)?;
        Ok(Term::Unlock {
            effect_row: Box::new(effect_row),
            body: Box::new(body),
        })
    }

    fn parse_defeat(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Defeat)?;
        let rule = self.parse_atom(self.next_depth(depth)?)?;
        Ok(Term::DefeatElim {
            rule: Box::new(rule),
        })
    }

    fn parse_sanctions_dominance(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::SanctionsDominance)?;
        self.expect(&Token::Lparen)?;
        let proof = self.parse_term(self.next_depth(depth)?)?;
        self.expect(&Token::Rparen)?;
        Ok(Term::SanctionsDominance {
            proof: Box::new(proof),
        })
    }

    // ── Variable / qualified identifier ─────────────────────────────

    fn parse_qual_ident(&mut self) -> Result<QualIdent, ParseError> {
        let (name, _) = self.expect_ident()?;
        Ok(QualIdent::new(name.split('.')))
    }

    fn parse_tribunal_ref(&mut self) -> Result<TribunalRef, ParseError> {
        let (tok, span) = self.advance();
        match tok {
            Token::Ident(name) => {
                if let Some(rest) = name.strip_prefix("meta-tribunal.") {
                    Ok(TribunalRef::MetaTribunal(QualIdent::new(rest.split('.'))))
                } else {
                    Ok(TribunalRef::Named(QualIdent::new(name.split('.'))))
                }
            }
            Token::ContentRef(content) => Ok(TribunalRef::ContentAddressed(ContentRef::new(
                &content,
            ))),
            other => Err(ParseError {
                span,
                expected: "tribunal reference".to_string(),
                found: format!("{}", other),
            }),
        }
    }

    fn parse_principle_ref(&mut self) -> Result<PrincipleRef, ParseError> {
        let (tok, span) = self.advance();
        match tok {
            Token::Ident(name) => Ok(PrincipleRef::Named(QualIdent::new(name.split('.')))),
            Token::ContentRef(content) => {
                Ok(PrincipleRef::ContentAddressed(ContentRef::new(&content)))
            }
            other => Err(ParseError {
                span,
                expected: "principle reference".to_string(),
                found: format!("{}", other),
            }),
        }
    }

    fn parse_precedent_ref(&mut self) -> Result<PrecedentRef, ParseError> {
        let (tok, span) = self.advance();
        match tok {
            Token::ContentRef(content) => Ok(PrecedentRef {
                content: ContentRef::new(&content),
            }),
            other => Err(ParseError {
                span,
                expected: "precedent reference".to_string(),
                found: format!("{}", other),
            }),
        }
    }

    fn parse_principle_refs(&mut self) -> Result<Vec<PrincipleRef>, ParseError> {
        self.expect(&Token::Lbracket)?;
        let mut principles = Vec::new();
        if !self.check(&Token::Rbracket) {
            principles.push(self.parse_principle_ref()?);
            while self.check(&Token::Comma) {
                self.advance();
                if self.check(&Token::Rbracket) {
                    break;
                }
                principles.push(self.parse_principle_ref()?);
            }
        }
        self.expect(&Token::Rbracket)?;
        Ok(principles)
    }

    fn parse_precedent_refs(&mut self) -> Result<Vec<PrecedentRef>, ParseError> {
        self.expect(&Token::Lbracket)?;
        let mut precedents = Vec::new();
        if !self.check(&Token::Rbracket) {
            precedents.push(self.parse_precedent_ref()?);
            while self.check(&Token::Comma) {
                self.advance();
                if self.check(&Token::Rbracket) {
                    break;
                }
                precedents.push(self.parse_precedent_ref()?);
            }
        }
        self.expect(&Token::Rbracket)?;
        Ok(precedents)
    }

    /// Parse `ident` possibly with `@n` De Bruijn annotation, or a qualified
    /// identifier `A.B.C`.
    fn parse_var_or_qual(&mut self) -> Result<Term, ParseError> {
        let (name, _) = self.expect_ident()?;

        // Check for De Bruijn annotation: `x@3`.
        if self.check(&Token::At) {
            self.advance();
            let (idx, _) = self.expect_nat()?;
            return Ok(Term::Var {
                name: Ident::new(&name),
                index: idx as u32,
            });
        }

        // Check for qualified identifier: `A.B.C`.
        if self.check(&Token::Dot) {
            let mut segments = vec![name.clone()];
            while self.check(&Token::Dot) {
                // Look-ahead: only consume Dot if next is Ident.
                if self.pos + 1 < self.tokens.len() {
                    if let Token::Ident(_) = &self.tokens[self.pos + 1].0 {
                        self.advance(); // consume Dot
                        let (seg, _) = self.expect_ident()?;
                        segments.push(seg);
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }

            if segments.len() > 1 {
                return Ok(Term::Constant(QualIdent::new(
                    segments.iter().map(|s| s.as_str()),
                )));
            }
        }

        // Simple variable — De Bruijn index 0 (debruijn pass assigns real index).
        Ok(Term::Var {
            name: Ident::new(&name),
            index: 0,
        })
    }

    // ── Parenthesised expression or annotation ──────────────────────

    /// `( term )` or `( term : type )`.
    fn parse_paren(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Lparen)?;
        let next_depth = self.next_depth(depth)?;
        let inner = self.parse_term(next_depth)?;

        if self.check(&Token::Colon) {
            self.advance();
            let ty = self.parse_term(next_depth)?;
            self.expect(&Token::Rparen)?;
            Ok(Term::Annot {
                term: Box::new(inner),
                ty: Box::new(ty),
            })
        } else {
            self.expect(&Token::Rparen)?;
            Ok(inner)
        }
    }

    // ── Pair ────────────────────────────────────────────────────────

    /// `⟨a, b⟩`
    fn parse_pair(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Langle)?;
        let next_depth = self.next_depth(depth)?;
        let fst = self.parse_term(next_depth)?;
        self.expect(&Token::Comma)?;
        let snd = self.parse_term(next_depth)?;
        self.expect(&Token::Rangle)?;
        Ok(Term::Pair {
            fst: Box::new(fst),
            snd: Box::new(snd),
        })
    }

    // ── Effect rows ─────────────────────────────────────────────────

    /// Parse an effect row (comma-separated effects within brackets).
    fn parse_effect_row(&mut self, depth: usize) -> Result<EffectRow, ParseError> {
        // Handle empty row.
        if self.check(&Token::Rbracket) {
            return Ok(EffectRow::Empty);
        }

        let mut effects = Vec::new();
        let next_depth = self.next_depth(depth)?;
        effects.push(self.parse_single_effect(next_depth)?);
        while self.check(&Token::Comma) {
            self.advance();
            if self.check(&Token::Rbracket) {
                break; // trailing comma
            }
            effects.push(self.parse_single_effect(next_depth)?);
        }

        Ok(EffectRow::Effects(effects))
    }

    /// Parse a single effect.
    fn parse_single_effect(&mut self, depth: usize) -> Result<Effect, ParseError> {
        match self.peek() {
            Token::Ident(ref s) => {
                let name = s.clone();
                match name.as_str() {
                    "read" => {
                        self.advance();
                        Ok(Effect::Read)
                    }
                    "write" => {
                        self.advance();
                        self.expect(&Token::Lparen)?;
                        let scope = self.parse_atom(self.next_depth(depth)?)?;
                        self.expect(&Token::Rparen)?;
                        Ok(Effect::Write(Box::new(scope)))
                    }
                    "attest" => {
                        self.advance();
                        self.expect(&Token::Lparen)?;
                        let (auth, _) = self.expect_ident()?;
                        self.expect(&Token::Rparen)?;
                        Ok(Effect::Attest(AuthorityRef::Named(QualIdent::simple(
                            &auth,
                        ))))
                    }
                    "authority" => {
                        self.advance();
                        self.expect(&Token::Lparen)?;
                        let (auth, _) = self.expect_ident()?;
                        self.expect(&Token::Rparen)?;
                        Ok(Effect::Authority(AuthorityRef::Named(QualIdent::simple(
                            &auth,
                        ))))
                    }
                    "oracle" => {
                        self.advance();
                        self.expect(&Token::Lparen)?;
                        let (oref, _) = self.expect_ident()?;
                        self.expect(&Token::Rparen)?;
                        Ok(Effect::Oracle(OracleRef::Named(QualIdent::simple(&oref))))
                    }
                    "fuel" => {
                        self.advance();
                        self.expect(&Token::Lparen)?;
                        let (level_name, _) = self.expect_ident()?;
                        // Parse level: extract numeric suffix from e.g. "l0" or "l_0"
                        let level_num: u64 = level_name
                            .chars()
                            .filter(|c| c.is_ascii_digit())
                            .collect::<String>()
                            .parse()
                            .unwrap_or(0);
                        self.expect(&Token::Comma)?;
                        let (n, _) = self.expect_nat()?;
                        self.expect(&Token::Rparen)?;
                        Ok(Effect::Fuel(Level::Nat(level_num), n))
                    }
                    "sanctions_query" => {
                        self.advance();
                        Ok(Effect::SanctionsQuery)
                    }
                    "discretion" => {
                        self.advance();
                        self.expect(&Token::Lparen)?;
                        let (auth, _) = self.expect_ident()?;
                        self.expect(&Token::Rparen)?;
                        Ok(Effect::Discretion(AuthorityRef::Named(QualIdent::simple(
                            &auth,
                        ))))
                    }
                    _ => Err(ParseError {
                        span: self.peek_span(),
                        expected:
                            "known effect (read, write, attest, authority, oracle, fuel, sanctions_query, discretion)"
                                .to_string(),
                        found: name,
                    }),
                }
            }
            other => Err(ParseError {
                span: self.peek_span(),
                expected: "effect".to_string(),
                found: format!("{}", other),
            }),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Public API
// ═══════════════════════════════════════════════════════════════════════

/// Parse a token stream into a Core Lex `Term`.
///
/// This is the main entry point for the parser. The token stream should
/// include the final `Token::Eof`. Comment tokens are filtered
/// automatically.
///
/// # Errors
///
/// Returns a `ParseError` with span information and expected/found
/// diagnostics if the input does not conform to the Core Lex grammar.
pub fn parse(tokens: &[Spanned<Token>]) -> Result<Term, ParseError> {
    // Filter out comments.
    let filtered: Vec<Spanned<Token>> = tokens
        .iter()
        .filter(|(tok, _)| !matches!(tok, Token::Comment(_)))
        .cloned()
        .collect();

    let mut parser = Parser::new(&filtered);
    let term = parser.parse_term(0)?;

    // Ensure we consumed everything (except possibly Eof).
    if !matches!(parser.peek(), Token::Eof) {
        return Err(ParseError {
            span: parser.peek_span(),
            expected: "end of input".to_string(),
            found: format!("{}", parser.peek()),
        });
    }

    Ok(term)
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::token::{Span, Token};

    /// Helper to create a spanned token with a dummy span.
    fn tok(t: Token, offset: usize) -> Spanned<Token> {
        (t, Span::new(offset, offset + 1, 1, (offset + 1) as u32))
    }

    /// Shorthand for Ident tokens.
    fn ident(s: &str, offset: usize) -> Spanned<Token> {
        tok(Token::Ident(s.to_string()), offset)
    }

    // ── Test 1: Simple lambda ───────────────────────────────────────

    #[test]
    fn test_simple_lambda() {
        // λ(x : Type). x
        let tokens = vec![
            tok(Token::Lambda, 0),
            tok(Token::Lparen, 1),
            ident("x", 2),
            tok(Token::Colon, 3),
            tok(Token::Type, 4),
            tok(Token::Rparen, 5),
            tok(Token::Dot, 6),
            ident("x", 7),
            tok(Token::Eof, 8),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Lambda {
                binder,
                domain,
                body,
            } => {
                assert_eq!(binder.name, "x");
                assert!(matches!(domain.as_ref(), Term::Sort(Sort::Type(_))));
                assert!(matches!(body.as_ref(), Term::Var { name, .. } if name.name == "x"));
            }
            other => panic!("expected Lambda, got {:?}", other),
        }
    }

    // ── Test 2: Pi type with effects ────────────────────────────────

    #[test]
    fn test_pi_with_effects() {
        // Π(x : Type)[read, write(db)]. x
        let tokens = vec![
            tok(Token::Pi, 0),
            tok(Token::Lparen, 1),
            ident("x", 2),
            tok(Token::Colon, 3),
            tok(Token::Type, 4),
            tok(Token::Rparen, 5),
            tok(Token::Lbracket, 6),
            ident("read", 7),
            tok(Token::Comma, 8),
            ident("write", 9),
            tok(Token::Lparen, 10),
            ident("db", 11),
            tok(Token::Rparen, 12),
            tok(Token::Rbracket, 13),
            tok(Token::Dot, 14),
            ident("x", 15),
            tok(Token::Eof, 16),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Pi {
                binder, effect_row, ..
            } => {
                assert_eq!(binder.name, "x");
                let row = effect_row.as_ref().unwrap();
                match row {
                    EffectRow::Effects(effs) => {
                        assert_eq!(effs.len(), 2);
                        assert!(matches!(effs[0], Effect::Read));
                        assert!(matches!(&effs[1], Effect::Write(_)));
                    }
                    _ => panic!("expected Effects row"),
                }
            }
            other => panic!("expected Pi, got {:?}", other),
        }
    }

    // ── Test 3: Let binding ─────────────────────────────────────────

    #[test]
    fn test_let_binding() {
        // let x : Type := Prop in x
        let tokens = vec![
            tok(Token::Let, 0),
            ident("x", 1),
            tok(Token::Colon, 2),
            tok(Token::Type, 3),
            tok(Token::ColonEq, 4),
            tok(Token::Prop, 5),
            tok(Token::In, 6),
            ident("x", 7),
            tok(Token::Eof, 8),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Let {
                binder,
                ty,
                val,
                body,
            } => {
                assert_eq!(binder.name, "x");
                assert!(matches!(ty.as_ref(), Term::Sort(Sort::Type(_))));
                assert!(matches!(val.as_ref(), Term::Sort(Sort::Prop)));
                assert!(matches!(body.as_ref(), Term::Var { name, .. } if name.name == "x"));
            }
            other => panic!("expected Let, got {:?}", other),
        }
    }

    // ── Test 4: Pattern match ───────────────────────────────────────

    #[test]
    fn test_pattern_match() {
        // match x return Type with | Zero => Prop | Succ n => Type
        let tokens = vec![
            tok(Token::Match, 0),
            ident("x", 1),
            tok(Token::Return, 2),
            tok(Token::Type, 3),
            tok(Token::With, 4),
            tok(Token::Pipe, 5),
            ident("Zero", 6),
            tok(Token::DoubleArrow, 7),
            tok(Token::Prop, 8),
            tok(Token::Pipe, 9),
            ident("Succ", 10),
            ident("n", 11),
            tok(Token::DoubleArrow, 12),
            tok(Token::Type, 13),
            tok(Token::Eof, 14),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Match { branches, .. } => {
                assert_eq!(branches.len(), 2);
                match &branches[0].pattern {
                    Pattern::Constructor {
                        constructor,
                        binders,
                    } => {
                        assert_eq!(constructor.name.segments, vec!["Zero"]);
                        assert!(binders.is_empty());
                    }
                    other => panic!("expected Constructor, got {:?}", other),
                }
                match &branches[1].pattern {
                    Pattern::Constructor {
                        constructor,
                        binders,
                    } => {
                        assert_eq!(constructor.name.segments, vec!["Succ"]);
                        assert_eq!(binders.len(), 1);
                        assert_eq!(binders[0].name, "n");
                    }
                    other => panic!("expected Constructor, got {:?}", other),
                }
            }
            other => panic!("expected Match, got {:?}", other),
        }
    }

    // ── Test 5: Defeasible rule ─────────────────────────────────────

    #[test]
    fn test_defeasible_rule() {
        // defeasible r : Prop with unless g => Prop priority 10 end
        let tokens = vec![
            tok(Token::Defeasible, 0),
            ident("r", 1),
            tok(Token::Colon, 2),
            tok(Token::Prop, 3),
            tok(Token::With, 4),
            tok(Token::Unless, 5),
            ident("g", 6),
            tok(Token::DoubleArrow, 7),
            tok(Token::Prop, 8),
            tok(Token::Priority, 9),
            tok(Token::Nat(10), 10),
            tok(Token::End, 11),
            tok(Token::Eof, 12),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Defeasible(rule) => {
                assert_eq!(rule.name.name, "r");
                assert_eq!(rule.exceptions.len(), 1);
                assert_eq!(rule.exceptions[0].priority, Some(10));
            }
            other => panic!("expected Defeasible, got {:?}", other),
        }
    }

    // ── Test 6: Nested application (left-associative) ───────────────

    #[test]
    fn test_nested_application() {
        // f x y  =>  App(App(f, x), y)
        let tokens = vec![
            ident("f", 0),
            ident("x", 1),
            ident("y", 2),
            tok(Token::Eof, 3),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::App { func, arg } => {
                // arg should be y
                assert!(matches!(arg.as_ref(), Term::Var { name, .. } if name.name == "y"));
                // func should be App(f, x)
                match func.as_ref() {
                    Term::App {
                        func: inner_f,
                        arg: inner_a,
                    } => {
                        assert!(
                            matches!(inner_f.as_ref(), Term::Var { name, .. } if name.name == "f")
                        );
                        assert!(
                            matches!(inner_a.as_ref(), Term::Var { name, .. } if name.name == "x")
                        );
                    }
                    other => panic!("expected inner App, got {:?}", other),
                }
            }
            other => panic!("expected App, got {:?}", other),
        }
    }

    // ── Test 7: Type annotation ─────────────────────────────────────

    #[test]
    fn test_type_annotation() {
        // (x : Type)
        let tokens = vec![
            tok(Token::Lparen, 0),
            ident("x", 1),
            tok(Token::Colon, 2),
            tok(Token::Type, 3),
            tok(Token::Rparen, 4),
            tok(Token::Eof, 5),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Annot { term, ty } => {
                assert!(matches!(term.as_ref(), Term::Var { name, .. } if name.name == "x"));
                assert!(matches!(ty.as_ref(), Term::Sort(Sort::Type(_))));
            }
            other => panic!("expected Annot, got {:?}", other),
        }
    }

    // ── Test 8: Temporal term (asof₀) ───────────────────────────────

    #[test]
    fn test_temporal_asof0() {
        // asof₀ x
        let tokens = vec![tok(Token::AsOf0, 0), ident("x", 1), tok(Token::Eof, 2)];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::ModalAt { time, .. } => {
                assert!(matches!(time, TimeTerm::AsOf0(_)));
            }
            other => panic!("expected ModalAt with AsOf0, got {:?}", other),
        }
    }

    // ── Test 9: lift₀(x) ───────────────────────────────────────────

    #[test]
    fn test_temporal_lift0() {
        // lift₀(x)
        let tokens = vec![
            tok(Token::Lift0, 0),
            tok(Token::Lparen, 1),
            ident("x", 2),
            tok(Token::Rparen, 3),
            tok(Token::Eof, 4),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Lift0 { time } => {
                assert!(matches!(time.as_ref(), Term::Var { name, .. } if name.name == "x"));
            }
            other => panic!("expected Lift0, got {:?}", other),
        }
    }

    // ── Test 10: derive₁(t, w) ─────────────────────────────────────

    #[test]
    fn test_temporal_derive1() {
        // derive₁(t, w)
        let tokens = vec![
            tok(Token::Derive1, 0),
            tok(Token::Lparen, 1),
            ident("t", 2),
            tok(Token::Comma, 3),
            ident("w", 4),
            tok(Token::Rparen, 5),
            tok(Token::Eof, 6),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Derive1 { time, witness } => {
                assert!(matches!(time.as_ref(), Term::Var { name, .. } if name.name == "t"));
                assert!(matches!(witness.as_ref(), Term::Var { name, .. } if name.name == "w"));
            }
            other => panic!("expected Derive1, got {:?}", other),
        }
    }

    #[test]
    fn test_projection_prefix_atom() {
        // f π₁ p
        let tokens = vec![
            ident("f", 0),
            tok(Token::Proj1, 1),
            ident("p", 2),
            tok(Token::Eof, 3),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::App { func, arg } => {
                assert!(matches!(func.as_ref(), Term::Var { name, .. } if name.name == "f"));
                match arg.as_ref() {
                    Term::Proj { first, pair } => {
                        assert!(*first);
                        assert!(
                            matches!(pair.as_ref(), Term::Var { name, .. } if name.name == "p")
                        );
                    }
                    other => panic!("expected projection arg, got {:?}", other),
                }
            }
            other => panic!("expected App, got {:?}", other),
        }
    }

    // ── Test 11: Parse error on unexpected token ────────────────────

    #[test]
    fn test_parse_error_unexpected_token() {
        let tokens = vec![tok(Token::Pipe, 0), tok(Token::Eof, 1)];

        let result = parse(&tokens);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.expected, "term");
        assert!(err.found.contains("|"));
    }

    // ── Test 12: Arrow right-associativity ──────────────────────────

    #[test]
    fn test_arrow_right_associative() {
        // A → B → C  =>  Pi(_, A, Pi(_, B, C))
        let tokens = vec![
            ident("A", 0),
            tok(Token::Arrow, 1),
            ident("B", 2),
            tok(Token::Arrow, 3),
            ident("C", 4),
            tok(Token::Eof, 5),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Pi {
                binder,
                domain,
                codomain,
                ..
            } => {
                assert_eq!(binder.name, "_");
                assert!(matches!(domain.as_ref(), Term::Var { name, .. } if name.name == "A"));
                match codomain.as_ref() {
                    Term::Pi {
                        domain: inner_d,
                        codomain: inner_c,
                        ..
                    } => {
                        assert!(
                            matches!(inner_d.as_ref(), Term::Var { name, .. } if name.name == "B")
                        );
                        assert!(
                            matches!(inner_c.as_ref(), Term::Var { name, .. } if name.name == "C")
                        );
                    }
                    other => panic!("expected inner Pi (arrow), got {:?}", other),
                }
            }
            other => panic!("expected Pi (arrow), got {:?}", other),
        }
    }

    // ── Test 13: Sigma type ─────────────────────────────────────────

    #[test]
    fn test_sigma_type() {
        // Σ(x : Type). x
        let tokens = vec![
            tok(Token::Sigma, 0),
            tok(Token::Lparen, 1),
            ident("x", 2),
            tok(Token::Colon, 3),
            tok(Token::Type, 4),
            tok(Token::Rparen, 5),
            tok(Token::Dot, 6),
            ident("x", 7),
            tok(Token::Eof, 8),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Sigma { binder, snd_ty, .. } => {
                assert_eq!(binder.name, "x");
                assert!(matches!(snd_ty.as_ref(), Term::Var { name, .. } if name.name == "x"));
            }
            other => panic!("expected Sigma, got {:?}", other),
        }
    }

    // ── Test 14: Fix (Rec) ──────────────────────────────────────────

    #[test]
    fn test_fix() {
        // fix f : Type := f
        let tokens = vec![
            tok(Token::Fix, 0),
            ident("f", 1),
            tok(Token::Colon, 2),
            tok(Token::Type, 3),
            tok(Token::ColonEq, 4),
            ident("f", 5),
            tok(Token::Eof, 6),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Rec { binder, body, .. } => {
                assert_eq!(binder.name, "f");
                assert!(matches!(body.as_ref(), Term::Var { name, .. } if name.name == "f"));
            }
            other => panic!("expected Rec (fix), got {:?}", other),
        }
    }

    // ── Test 15: Hole with scope ────────────────────────────────────

    #[test]
    fn test_hole_with_scope() {
        // ? h : Prop @ regulator scope { jurisdiction : us }
        let tokens = vec![
            tok(Token::Question, 0),
            ident("h", 1),
            tok(Token::Colon, 2),
            tok(Token::Prop, 3),
            tok(Token::At, 4),
            ident("regulator", 5),
            ident("scope", 6),
            tok(Token::Lbrace, 7),
            ident("jurisdiction", 8),
            tok(Token::Colon, 9),
            ident("us", 10),
            tok(Token::Rbrace, 11),
            tok(Token::Eof, 12),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Hole(hole) => {
                assert_eq!(hole.name.as_ref().unwrap().name, "h");
                assert!(
                    matches!(&hole.authority, AuthorityRef::Named(q) if q.segments == vec!["regulator"])
                );
                let sc = hole.scope.as_ref().unwrap();
                assert_eq!(sc.fields.len(), 1);
                assert!(
                    matches!(&sc.fields[0], ScopeField::Jurisdiction(q) if q.segments == vec!["us"])
                );
            }
            other => panic!("expected Hole, got {:?}", other),
        }
    }

    // ── Test 16: Coerce modal ───────────────────────────────────────

    #[test]
    fn test_coerce_modal() {
        // coerce[T1 ⇒ T2] x
        let tokens = vec![
            tok(Token::Coerce, 0),
            tok(Token::Lbracket, 1),
            ident("T1", 2),
            tok(Token::DoubleArrow, 3),
            ident("T2", 4),
            tok(Token::Rbracket, 5),
            ident("x", 6),
            tok(Token::Eof, 7),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::ModalElim {
                from_tribunal,
                to_tribunal,
                term,
                ..
            } => {
                assert!(matches!(from_tribunal, TribunalRef::Named(q) if q.segments == vec!["T1"]));
                assert!(matches!(to_tribunal, TribunalRef::Named(q) if q.segments == vec!["T2"]));
                assert!(matches!(term.as_ref(), Term::Var { name, .. } if name.name == "x"));
            }
            other => panic!("expected ModalElim, got {:?}", other),
        }
    }

    // ── Test 17: Pair ⟨a, b⟩ ───────────────────────────────────────

    #[test]
    fn test_pair() {
        // ⟨a, b⟩
        let tokens = vec![
            tok(Token::Langle, 0),
            ident("a", 1),
            tok(Token::Comma, 2),
            ident("b", 3),
            tok(Token::Rangle, 4),
            tok(Token::Eof, 5),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Pair { fst, snd } => {
                assert!(matches!(fst.as_ref(), Term::Var { name, .. } if name.name == "a"));
                assert!(matches!(snd.as_ref(), Term::Var { name, .. } if name.name == "b"));
            }
            other => panic!("expected Pair, got {:?}", other),
        }
    }

    // ── Test 18: Product type A × B ─────────────────────────────────

    #[test]
    fn test_product_type() {
        // A × B  =>  Sigma { binder: "_", fst_ty: A, snd_ty: B }
        let tokens = vec![
            ident("A", 0),
            tok(Token::Times, 1),
            ident("B", 2),
            tok(Token::Eof, 3),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Sigma {
                binder,
                fst_ty,
                snd_ty,
            } => {
                assert_eq!(binder.name, "_");
                assert!(matches!(fst_ty.as_ref(), Term::Var { name, .. } if name.name == "A"));
                assert!(matches!(snd_ty.as_ref(), Term::Var { name, .. } if name.name == "B"));
            }
            other => panic!("expected Sigma (product), got {:?}", other),
        }
    }

    // ── Test 19: Pi without effects ─────────────────────────────────

    #[test]
    fn test_pi_without_effects() {
        // Π(x : Type). x
        let tokens = vec![
            tok(Token::Pi, 0),
            tok(Token::Lparen, 1),
            ident("x", 2),
            tok(Token::Colon, 3),
            tok(Token::Type, 4),
            tok(Token::Rparen, 5),
            tok(Token::Dot, 6),
            ident("x", 7),
            tok(Token::Eof, 8),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Pi {
                binder, effect_row, ..
            } => {
                assert_eq!(binder.name, "x");
                assert!(effect_row.is_none());
            }
            other => panic!("expected Pi, got {:?}", other),
        }
    }

    // ── Test 20: ParseError has span info ───────────────────────────

    #[test]
    fn test_parse_error_has_span_info() {
        // Missing `)` in lambda
        let tokens = vec![
            tok(Token::Lambda, 0),
            tok(Token::Lparen, 1),
            ident("x", 2),
            tok(Token::Colon, 3),
            tok(Token::Type, 4),
            tok(Token::Dot, 5),
            ident("x", 6),
            tok(Token::Eof, 7),
        ];

        let result = parse(&tokens);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.span.line > 0);
        assert!(err.span.col > 0);
        assert!(err.expected.contains(")"));
        assert!(!err.found.is_empty());
    }

    // ── Test 21: Wildcard pattern in match ──────────────────────────

    #[test]
    fn test_wildcard_pattern() {
        // match x return Type with | _ => Prop
        let tokens = vec![
            tok(Token::Match, 0),
            ident("x", 1),
            tok(Token::Return, 2),
            tok(Token::Type, 3),
            tok(Token::With, 4),
            tok(Token::Pipe, 5),
            tok(Token::Underscore, 6),
            tok(Token::DoubleArrow, 7),
            tok(Token::Prop, 8),
            tok(Token::Eof, 9),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Match { branches, .. } => {
                assert_eq!(branches.len(), 1);
                assert!(matches!(&branches[0].pattern, Pattern::Wildcard));
            }
            other => panic!("expected Match, got {:?}", other),
        }
    }

    // ── Test 22: Variable with De Bruijn index ──────────────────────

    #[test]
    fn test_var_with_debruijn() {
        // x@3
        let tokens = vec![
            ident("x", 0),
            tok(Token::At, 1),
            tok(Token::Nat(3), 2),
            tok(Token::Eof, 3),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Var { name, index } => {
                assert_eq!(name.name, "x");
                assert_eq!(*index, 3);
            }
            other => panic!("expected Var with debruijn, got {:?}", other),
        }
    }

    // ── Test 23: Comments are skipped ───────────────────────────────

    #[test]
    fn test_comments_skipped() {
        let tokens = vec![
            tok(Token::Comment("a comment".to_string()), 0),
            ident("x", 1),
            tok(Token::Eof, 2),
        ];

        let result = parse(&tokens).unwrap();
        assert!(matches!(result, Term::Var { name, .. } if name.name == "x"));
    }

    // ── Test 24: Sorts ──────────────────────────────────────────────

    #[test]
    fn test_sorts() {
        for (token, check) in [
            (
                Token::Type,
                Box::new(|t: &Term| matches!(t, Term::Sort(Sort::Type(_))))
                    as Box<dyn Fn(&Term) -> bool>,
            ),
            (
                Token::Prop,
                Box::new(|t: &Term| matches!(t, Term::Sort(Sort::Prop))),
            ),
            (
                Token::Rule,
                Box::new(|t: &Term| matches!(t, Term::Sort(Sort::Rule(_)))),
            ),
        ] {
            let tokens = vec![tok(token, 0), tok(Token::Eof, 1)];
            let result = parse(&tokens).unwrap();
            assert!(check(&result), "sort check failed for {:?}", result);
        }
    }

    #[test]
    fn test_sort_subscripts() {
        let type_tokens = vec![
            tok(Token::Type, 0),
            tok(Token::Underscore, 1),
            tok(Token::Nat(42), 2),
            tok(Token::Eof, 3),
        ];
        let rule_tokens = vec![
            tok(Token::Rule, 0),
            tok(Token::Underscore, 1),
            tok(Token::Nat(3), 2),
            tok(Token::Eof, 3),
        ];

        let parsed_type = parse(&type_tokens).unwrap();
        let parsed_rule = parse(&rule_tokens).unwrap();

        assert!(matches!(
            parsed_type,
            Term::Sort(Sort::Type(Level::Nat(42)))
        ));
        assert!(matches!(parsed_rule, Term::Sort(Sort::Rule(Level::Nat(3)))));
    }

    // ── Test 25: Trailing tokens are an error ───────────────────────

    #[test]
    fn test_trailing_tokens_error() {
        let tokens = vec![ident("x", 0), tok(Token::Rparen, 1), tok(Token::Eof, 2)];

        let result = parse(&tokens);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.expected.contains("end of input"));
    }

    // ── Test 26: Effect row with fuel ───────────────────────────────

    #[test]
    fn test_pi_with_fuel_effect() {
        // Π(x : Type)[fuel(l0, 100)]. x
        let tokens = vec![
            tok(Token::Pi, 0),
            tok(Token::Lparen, 1),
            ident("x", 2),
            tok(Token::Colon, 3),
            tok(Token::Type, 4),
            tok(Token::Rparen, 5),
            tok(Token::Lbracket, 6),
            ident("fuel", 7),
            tok(Token::Lparen, 8),
            ident("l0", 9),
            tok(Token::Comma, 10),
            tok(Token::Nat(100), 11),
            tok(Token::Rparen, 12),
            tok(Token::Rbracket, 13),
            tok(Token::Dot, 14),
            ident("x", 15),
            tok(Token::Eof, 16),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Pi { effect_row, .. } => {
                let row = effect_row.as_ref().unwrap();
                match row {
                    EffectRow::Effects(effs) => {
                        assert_eq!(effs.len(), 1);
                        assert!(matches!(&effs[0], Effect::Fuel(Level::Nat(0), 100)));
                    }
                    _ => panic!("expected Effects row"),
                }
            }
            other => panic!("expected Pi, got {:?}", other),
        }
    }

    #[test]
    fn test_unknown_effect_is_error() {
        let tokens = vec![
            tok(Token::Pi, 0),
            tok(Token::Lparen, 1),
            ident("x", 2),
            tok(Token::Colon, 3),
            tok(Token::Type, 4),
            tok(Token::Rparen, 5),
            tok(Token::Lbracket, 6),
            ident("mystery", 7),
            tok(Token::Rbracket, 8),
            tok(Token::Dot, 9),
            ident("x", 10),
            tok(Token::Eof, 11),
        ];

        let err = parse(&tokens).unwrap_err();
        assert_eq!(
            err.expected,
            "known effect (read, write, attest, authority, oracle, fuel, sanctions_query, discretion)"
        );
        assert_eq!(err.found, "mystery");
    }

    // ── Test 27: Content reference ──────────────────────────────────

    #[test]
    fn test_content_ref() {
        let hash = "a".repeat(64);
        let tokens = vec![tok(Token::ContentRef(hash.clone()), 0), tok(Token::Eof, 1)];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::ContentRefTerm(cr) => {
                assert_eq!(cr.hash.hex, hash);
            }
            other => panic!("expected ContentRefTerm, got {:?}", other),
        }
    }

    // ── Test 28: Qualified identifier ───────────────────────────────

    #[test]
    fn test_qualified_ident() {
        // regulator.sec_13d
        let tokens = vec![
            ident("regulator", 0),
            tok(Token::Dot, 1),
            ident("sec_13d", 2),
            tok(Token::Eof, 3),
        ];

        let result = parse(&tokens).unwrap();
        match &result {
            Term::Constant(qi) => {
                assert_eq!(qi.segments, vec!["regulator", "sec_13d"]);
            }
            other => panic!("expected Constant (qualified), got {:?}", other),
        }
    }
}
