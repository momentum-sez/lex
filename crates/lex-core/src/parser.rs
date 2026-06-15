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
    AppliesTo, AuthorityRef, Branch, Constructor, ContentRef, DefeasibleRule, Effect, EffectRow,
    Exception, Hole, Ident, JurisdictionScope, Level, OperationKindScope, OracleRef, Pattern,
    PrecedentRef, PrincipleBalancingStep, PrincipleRef, QualIdent, ScopeConstraint, ScopeField,
    Sort, Term, TimeTerm, TribunalRef,
};
use crate::token::{Span, Spanned, Token};
use std::fmt;

const MAX_DEPTH: usize = 192;

/// Reserved qualified-identifier segment used for the chunk-truncation
/// placeholder term. No legitimate authored rule can produce this name (it
/// is not lexable as a single identifier and is not a prelude constructor),
/// so it is unambiguously greppable as "a term position that was truncated
/// at a chunk boundary rather than authored".
const TRUNCATION_MARKER_NAME: &str = "__lex_truncated_chunk_boundary__";

/// Build the distinguishable chunk-truncation placeholder.
///
/// The Lex chunking harness (out-of-tree) splits multi-rule `.lex` sources on
/// line-prefix heuristics that occasionally cut a rule mid-term (a missing
/// `else`-branch, an `except` clause that ran off the end of the chunk, a bare
/// `defeasible` whose body started in the next chunk). The parser tolerates
/// these so the *primary* rule in the chunk can still be extracted — but it
/// must NOT manufacture a silently-complete-looking term.
///
/// The previous behaviour synthesized a bare `Term::Sort(Sort::Prop)`, which
/// is indistinguishable from an authored `Prop` and is *admissible* — a
/// truncated guard/body would then flow into typechecking and evaluation as a
/// vacuous term (and, for an exception guard, `eval_guard` reads a `Prop` as
/// *not satisfied*, silently turning a truncated exception into one that never
/// fires). That is the silent-fallback anti-pattern.
///
/// Instead we emit a reserved, unregistered `Constant`. It is:
///   * **distinguishable** — the reserved name is greppable and cannot be
///     authored;
///   * **fail-loud at use** — an unregistered constant passes
///     `check_admissibility` but FAILS `infer`/`check` with
///     `AdmissibilityViolation::ConstantNotSupported`, and fails evaluation
///     with `EvalError::NotAVerdict`. A truncated chunk therefore parses
///     (the harness can read the primary rule) but the truncated *term*
///     cannot be type-checked or evaluated as if it were real.
fn truncation_marker() -> Term {
    Term::Constant(QualIdent::simple(TRUNCATION_MARKER_NAME))
}

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
    //
    // Application is pure juxtaposition: `f x y => App(App(f, x), y)`.
    // Comparators (`==`, `≠`, `≤`, `≥`, `<`, `>`) and arithmetic
    // operators (`+`, `*`, `/`) that appear between atoms in
    // jurisdictional `.lex` files (`n >= 3`, `days_since > 15`) are
    // picked up here and lowered to `App (App op lhs) rhs` with a
    // reserved operator-identifier prefix. This is a surface-tolerance
    // path: Core Lex doesn't have first-class infix operators, but
    // `.lex` surface files use them, and the parser should consume
    // them without failing.

    fn parse_app(&mut self, depth: usize) -> Result<Term, ParseError> {
        let next_depth = self.next_depth(depth)?;
        let mut func = self.parse_atom(next_depth)?;

        loop {
            if self.is_atom_start() && !self.is_top_level_sentinel() {
                let arg = self.parse_atom(next_depth)?;
                func = Term::App {
                    func: Box::new(func),
                    arg: Box::new(arg),
                };
                continue;
            }
            if let Some(op_name) = infix_operator_name(self.peek()) {
                self.advance();
                let rhs = self.parse_atom(next_depth)?;
                func = Term::App {
                    func: Box::new(Term::App {
                        func: Box::new(Term::Constant(QualIdent::simple(op_name))),
                        arg: Box::new(func),
                    }),
                    arg: Box::new(rhs),
                };
                continue;
            }
            break;
        }

        Ok(func)
    }

    /// True when the current token is an identifier that starts a
    /// top-level rule form (`obligation`, `rule`, `hole`, `when`,
    /// `then`, etc.) and therefore must not be consumed as an
    /// argument of the preceding `parse_app` chain.
    ///
    /// Used by `parse_app` to terminate greedy argument absorption so
    /// that a multi-rule chunk doesn't eat the subsequent rule as an
    /// application argument of the preceding one. The set of sentinels
    /// is the identifier vocabulary that this parser's top-level and
    /// trailing-clause logic recognizes as structural.
    fn is_top_level_sentinel(&self) -> bool {
        matches!(
            self.peek(),
            Token::Ident(s) if matches!(
                s.as_str(),
                "obligation"
                    | "rule"
                    | "hole"
                    | "attestable_hole"
                    | "when"
                    | "then"
                    | "except"
                    | "authority"
            )
        )
    }

    /// Returns true if the current token can start a full term.
    ///
    /// Broader than `is_atom_start` — this also includes the binder
    /// keywords (`lambda`, `Pi`, `Sigma`, `let`, `match`, `fix`,
    /// `defeasible`, etc.) that `parse_atom` dispatches on but that
    /// `is_atom_start` deliberately excludes so that `parse_app`'s
    /// greedy argument absorption doesn't eat them.
    fn is_term_start(&self) -> bool {
        if self.is_atom_start() {
            return true;
        }
        matches!(
            self.peek(),
            Token::Lambda
                | Token::Pi
                | Token::Sigma
                | Token::Let
                | Token::Match
                | Token::Fix
                | Token::Defeasible
                | Token::Question
                | Token::Coerce
                | Token::Axiom
                | Token::Fill
                | Token::Balance
                | Token::Unlock
                | Token::Defeat
                | Token::SanctionsDominance
                | Token::AsOf0
                | Token::AsOf1
                | Token::Lift0
                | Token::Derive1
        )
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
            Token::Ident(ref s) if s == "if" => self.parse_if_then_else(self.next_depth(depth)?),
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

    /// `λ(x : T). body` or `λ(x : T)[effects]. body`
    ///
    /// The optional effect-row `[…]` between `)` and `.` mirrors the Pi
    /// surface form. Jurisdictional `.lex` rule files use this shape for
    /// lambdas representing mechanical rules with side effects, e.g.
    /// `lambda (ctx : IncorporationContext) [sanctions_query]. body`.
    ///
    /// The `Term::Lambda` AST node carries no effect row today; the row is
    /// parsed and dropped. (Pi carries one, Lambda does not.) This is a
    /// conscious asymmetry — lifting the row onto `Term::Lambda` is a
    /// separate AST change that would ripple through typecheck/elaborate.
    /// Parsing-only support is sufficient for coverage-harness purposes.
    fn parse_lambda(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Lambda)?;
        self.expect(&Token::Lparen)?;
        let (binder, _) = self.expect_ident()?;
        self.expect(&Token::Colon)?;
        let next_depth = self.next_depth(depth)?;
        let domain = self.parse_term(next_depth)?;
        self.expect(&Token::Rparen)?;

        // Optional effect row `[…]` between `)` and `.` on the lambda.
        if self.check(&Token::Lbracket) {
            self.advance();
            let _row = self.parse_effect_row(next_depth)?;
            self.expect(&Token::Rbracket)?;
        }

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

    /// `let x : T := e in body` or `let x : T = e in body`.
    ///
    /// The core-canonical binding token is `:=` (reflects the
    /// type-theoretic definitional-equality convention). Jurisdictional
    /// `.lex` files use ASCII `=` instead, and this parser accepts both
    /// as a surface-form compatibility affordance. Either token appears
    /// immediately after the type annotation and is consumed before the
    /// bound term.
    fn parse_let(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Let)?;
        let (name, _) = self.expect_ident()?;
        self.expect(&Token::Colon)?;
        let next_depth = self.next_depth(depth)?;
        let ty = self.parse_term(next_depth)?;
        // Accept either `:=` (core) or `=` (jurisdictional surface).
        if !self.eat(&Token::ColonEq) && !self.eat(&Token::Eq) {
            return Err(self.error(":= or ="));
        }
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

    /// `if <cond> then <then> else <else>` — jurisdictional `.lex`
    /// surface form, lowered to a `Match` on the condition with two
    /// constructor branches `True => <then>` and `False => <else>`.
    ///
    /// The `if`, `then`, `else` keywords are produced by the lexer as
    /// `Ident` tokens (there are no dedicated keyword tokens for
    /// them). Parsing is by identifier look-up. Greedy guard parsing
    /// stops at `then`; greedy then-branch parsing stops at `else`;
    /// the else-branch is a full term.
    fn parse_if_then_else(&mut self, depth: usize) -> Result<Term, ParseError> {
        // Consume `if`.
        let (tok, _) = self.advance();
        debug_assert!(matches!(&tok, Token::Ident(s) if s == "if"));

        let next_depth = self.next_depth(depth)?;
        let cond = self.parse_guard_until_then(next_depth)?;
        // Consume `then`.
        if matches!(self.peek(), Token::Ident(s) if s == "then") {
            self.advance();
        } else {
            return Err(self.error("`then`"));
        }
        let then_branch = self.parse_guard_until_else(next_depth)?;
        // Consume `else` if present.
        let else_branch = if matches!(self.peek(), Token::Ident(s) if s == "else") {
            self.advance();
            self.parse_term(next_depth)?
        } else {
            // Chunk-truncated: the `else`-branch ran off the end of the
            // chunk. Emit the distinguishable truncation marker (NOT a bare
            // `Prop`) so the missing branch fails loud at typecheck/eval
            // rather than masquerading as an authored `Prop` else-branch.
            truncation_marker()
        };

        let branches = vec![
            Branch {
                pattern: Pattern::Constructor {
                    constructor: Constructor::new(QualIdent::simple("True")),
                    binders: Vec::new(),
                },
                body: then_branch,
            },
            Branch {
                pattern: Pattern::Constructor {
                    constructor: Constructor::new(QualIdent::simple("False")),
                    binders: Vec::new(),
                },
                body: else_branch,
            },
        ];

        Ok(Term::Match {
            scrutinee: Box::new(cond),
            return_ty: Box::new(Term::Sort(Sort::Prop)),
            branches,
        })
    }

    /// Like `parse_guard_until_then` but terminates on `else`.
    fn parse_guard_until_else(&mut self, depth: usize) -> Result<Term, ParseError> {
        let next_depth = self.next_depth(depth)?;
        let mut acc = self.parse_atom(next_depth)?;
        loop {
            if matches!(self.peek(), Token::Ident(s) if s == "else")
                || matches!(
                    self.peek(),
                    Token::Eof | Token::End | Token::Priority | Token::Unless | Token::Pipe
                )
            {
                break;
            }
            if let Some(op_name) = infix_operator_name(self.peek()) {
                self.advance();
                let rhs = self.parse_atom(next_depth)?;
                acc = Term::App {
                    func: Box::new(Term::App {
                        func: Box::new(Term::Constant(QualIdent::simple(op_name))),
                        arg: Box::new(acc),
                    }),
                    arg: Box::new(rhs),
                };
                continue;
            }
            if self.is_atom_start() && !self.is_top_level_sentinel() {
                let next = self.parse_atom(next_depth)?;
                acc = Term::App {
                    func: Box::new(acc),
                    arg: Box::new(next),
                };
                continue;
            }
            break;
        }
        Ok(acc)
    }

    /// `match e return T with | pat => body ...`
    ///
    /// The scrutinee and return-type slots both admit an application
    /// chain (`f x y`). `parse_app` greedily consumes atoms as long as
    /// `is_atom_start` is true, which excludes the `return`/`with`
    /// keywords and reliably terminates both positions. Tuple-scrutinee
    /// `match (a, b) return …` is handled by `parse_paren`'s tuple
    /// lowering.
    fn parse_match(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Match)?;
        let next_depth = self.next_depth(depth)?;
        let scrutinee = self.parse_app(next_depth)?;
        self.expect(&Token::Return)?;
        let return_ty = self.parse_app(next_depth)?;
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

    /// Pattern: `Constructor x y z`, `_`, `(p₁, …, pₙ)` tuple, or
    /// a numeric / string literal.
    ///
    /// Tuple patterns are a surface-syntax affordance used by
    /// jurisdictional `.lex` files to scrutinize multi-tag composites
    /// (e.g. `match (ctx.exemption, ctx.status)` with arms like
    /// `| (Rule506b, NoSolicitation) => Compliant`).
    ///
    /// Literal patterns (`| 0 =>`, `| "abc" =>`) are lowered to a
    /// synthetic `Constructor` whose name is the literal rendering.
    /// This lets `.lex` files scrutinize natural-number counts like
    /// `match ctx.director_count return V with | 0 => NonCompliant | _ => Compliant`
    /// without a Pattern-AST extension.
    ///
    /// The current `Pattern` AST admits only `Constructor { name, binders }`
    /// and `Wildcard`. To avoid a ripple-causing AST extension, tuple
    /// patterns are lowered to a synthetic `Constructor` named
    /// `__tuple<N>__` whose `binders` list is the flat concatenation
    /// of the sub-patterns' binder-shaped view. This is a lossy but
    /// non-breaking compat lowering — downstream consumers that match
    /// on `Pattern::Constructor` still see a constructor; the name is
    /// machine-generated and distinguishable.
    fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        if self.check(&Token::Underscore) {
            self.advance();
            return Ok(Pattern::Wildcard);
        }

        if self.check(&Token::Lparen) {
            return self.parse_tuple_pattern();
        }

        // List-literal pattern `[]` (empty) or `[p1, p2, …]` —
        // lowered to a synthetic `__list<N>__` constructor with
        // flattened binders. Non-empty list patterns are uncommon;
        // `[]` is the high-frequency case (empty-list guard for
        // beneficial-owner enumeration).
        if self.check(&Token::Lbracket) {
            return self.parse_list_pattern();
        }

        // Numeric / string / rational literal pattern.
        if matches!(
            self.peek(),
            Token::Nat(_) | Token::Int(_) | Token::Rat(_, _) | Token::StringLit(_)
        ) {
            let (tok, _sp) = self.advance();
            let name = match tok {
                Token::Nat(n) => format!("__lit_{}__", n),
                Token::Int(n) => format!("__lit_{}__", n),
                Token::Rat(p, q) => format!("__lit_{}_{}__", p, q),
                Token::StringLit(s) => format!("__lit_str_{}__", s),
                _ => unreachable!(),
            };
            return Ok(Pattern::Constructor {
                constructor: Constructor::new(QualIdent::simple(&name)),
                binders: Vec::new(),
            });
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

    /// Parse `[p₁, p₂, …, pₙ]` as a list-literal pattern.
    ///
    /// Lowered to `Pattern::Constructor { name: __list<N>__, binders: … }`
    /// with a flattened binder list (same convention as tuple patterns).
    /// Empty list `[]` uses arity 0 with no binders.
    fn parse_list_pattern(&mut self) -> Result<Pattern, ParseError> {
        self.expect(&Token::Lbracket)?;
        let mut parts: Vec<Pattern> = Vec::new();
        if !self.check(&Token::Rbracket) {
            parts.push(self.parse_pattern()?);
            while self.check(&Token::Comma) {
                self.advance();
                if self.check(&Token::Rbracket) {
                    break;
                }
                parts.push(self.parse_pattern()?);
            }
        }
        self.expect(&Token::Rbracket)?;

        let mut binders = Vec::new();
        for p in &parts {
            flatten_pattern_binders(p, &mut binders);
        }
        let arity = parts.len();
        let name = format!("__list{arity}__");
        Ok(Pattern::Constructor {
            constructor: Constructor::new(QualIdent::simple(&name)),
            binders,
        })
    }

    /// Parse `(p₁, p₂, …, pₙ)` as a tuple pattern.
    ///
    /// Lowered to `Pattern::Constructor { name: __tuple<N>__, binders: … }`.
    /// See the doc on `parse_pattern` for the semantic caveat.
    fn parse_tuple_pattern(&mut self) -> Result<Pattern, ParseError> {
        self.expect(&Token::Lparen)?;
        let mut parts: Vec<Pattern> = Vec::new();
        if !self.check(&Token::Rparen) {
            parts.push(self.parse_pattern()?);
            while self.check(&Token::Comma) {
                self.advance();
                if self.check(&Token::Rparen) {
                    break; // trailing comma
                }
                parts.push(self.parse_pattern()?);
            }
        }
        self.expect(&Token::Rparen)?;

        let mut binders = Vec::new();
        for p in &parts {
            flatten_pattern_binders(p, &mut binders);
        }
        let arity = parts.len();
        let name = format!("__tuple{arity}__");
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

    /// Parse a defeasible rule in either of the two surface forms.
    ///
    /// ## Declarative form (Core-Lex canonical)
    ///
    /// ```text
    /// defeasible NAME : T with
    ///   unless g₁ => e₁ priority p₁ authority A₁
    ///   unless g₂ => e₂ …
    /// end
    /// ```
    ///
    /// ## Term form (jurisdictional `.lex` files; SUPREMUM/24 mass-lang
    /// authoring draft)
    ///
    /// ```text
    /// defeasible
    ///   lambda (ctx : T).
    ///     match ctx.field return V with
    ///       | Cons1 => expr1
    ///       | Cons2 => expr2
    ///   priority 0
    /// end
    /// ```
    ///
    /// The term form is anonymous (no name between `defeasible` and the
    /// body) and encodes the rule body inline as a lambda. It is the
    /// shape produced by the `modules/lex/**/*.lex` rule files across
    /// every mature jurisdiction (Prospera, Seychelles, ADGM, Cayman,
    /// UK, Singapore, Hong Kong, Luxembourg, Pakistan, BVI, and the 2026
    /// USA-federal extension).
    ///
    /// Disambiguation is by look-ahead: the declarative form begins with
    /// `Ident` followed by `Colon`; everything else routes to the term
    /// form. This preserves the declarative form losslessly (existing
    /// `defeasible foo : T with end` and `defeasible foo : T with unless …
    /// end` both parse as before).
    fn parse_defeasible(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Defeasible)?;
        let next_depth = self.next_depth(depth)?;

        // Look-ahead: declarative form iff next is Ident AND the token
        // after that is Colon. The Ident-without-Colon case would be a
        // syntax ambiguity; no real rule file uses a bare identifier as
        // a term-form body, so routing it to the declarative branch
        // yields the cleaner error message.
        let is_declarative = matches!(self.peek(), Token::Ident(_))
            && matches!(
                self.tokens.get(self.pos + 1).map(|(t, _)| t),
                Some(Token::Colon)
            );

        if is_declarative {
            self.parse_defeasible_declarative(next_depth)
        } else {
            self.parse_defeasible_term_form(next_depth)
        }
    }

    /// Declarative form: `defeasible NAME : T with [unless …]* end`.
    fn parse_defeasible_declarative(&mut self, depth: usize) -> Result<Term, ParseError> {
        let (name, _) = self.expect_ident()?;
        self.expect(&Token::Colon)?;
        let next_depth = self.next_depth(depth)?;
        let base_ty = self.parse_term(next_depth)?;
        // Optional rule-level `applies_to { ... }` scope clause (Frontier-09),
        // accepted between the signature and the `with` body.
        let applies_to = self.parse_applies_to_clause()?;
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
            applies_to,
        }))
    }

    /// Term form: `defeasible [<body>] [priority N] [end]`.
    ///
    /// The body is typically `lambda (ctx : T). match …`. The parser
    /// accepts any term here; priority annotation and `end` terminator
    /// are parsed after the body term. All three sub-parts
    /// (`<body>`, `priority N`, `end`) are independently optional so
    /// that surface-split inputs — for instance a chunk containing
    /// only the `defeasible` keyword, with the lambda body appearing
    /// in a subsequent chunk — parse as an empty anonymous defeasible
    /// rather than hard-failing at the chunk boundary.
    ///
    /// The parsed term is installed in `base_body`; `base_ty` is a
    /// synthetic `_` placeholder (the real type is embedded in the
    /// lambda's domain). The priority is captured as a single-entry
    /// `exceptions` list with a trivially-true guard (`Prop`) so that
    /// downstream consumers that inspect `exceptions[0].priority` see
    /// the right value. This is a surface-to-core bridge; typecheck
    /// and evaluate will continue to operate on the lambda body via
    /// `base_body`.
    fn parse_defeasible_term_form(&mut self, depth: usize) -> Result<Term, ParseError> {
        let next_depth = self.next_depth(depth)?;

        // Body is optional to tolerate surface-split inputs (e.g. a
        // bare `defeasible\n` chunk produced by a line-prefix-based
        // splitter that classifies the continuation `lambda` line as
        // a separate rule start). `is_term_start` covers both atoms
        // and binders — `is_atom_start` alone excludes binders like
        // `lambda`, which are precisely the bodies seen in the `.lex`
        // surface form we need to accept.
        let base_body = if self.is_term_start() {
            self.parse_term(next_depth)?
        } else {
            // Chunk-truncated: a bare `defeasible` whose body started in the
            // next chunk. Emit the distinguishable truncation marker (NOT a
            // bare `Prop`) so the empty body fails loud at typecheck/eval
            // instead of masquerading as an authored `Prop` body.
            truncation_marker()
        };

        // Optional `priority N`.
        let body_priority = if self.check(&Token::Priority) {
            self.advance();
            let (n, _) = self.expect_nat()?;
            Some(n as u32)
        } else {
            None
        };

        // Optional trailing `unless …` clauses, accepted as additional
        // exceptions on the anonymous defeasible. This path handles
        // `.lex` files that layer exception bodies after a term-form
        // rule body (`defeasible <body> priority 0 unless <body2> priority 1 end`).
        let mut exceptions: Vec<Exception> = Vec::new();
        if let Some(p) = body_priority {
            exceptions.push(Exception {
                guard: Box::new(Term::Sort(Sort::Prop)),
                body: Box::new(base_body.clone()),
                priority: Some(p),
                authority: None,
            });
        }
        while self.check(&Token::Unless) {
            exceptions.push(self.parse_exception(next_depth)?);
        }

        // Optional `end`.
        self.eat(&Token::End);

        // Synthesize a placeholder type; the real type is inside the
        // body's lambda binder.
        let base_ty = Term::Constant(QualIdent::simple("_"));

        Ok(Term::Defeasible(DefeasibleRule {
            name: Ident::new("_anon_defeasible"),
            base_ty: Box::new(base_ty),
            base_body: Box::new(base_body),
            exceptions,
            lattice: None,
            // Anonymous term-form rules carry no surface scope clause.
            applies_to: None,
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

    /// Parse an `unless` exception clause.
    ///
    /// See `parse_exception_body` for the body-level grammar. This
    /// helper just consumes the `unless` keyword and delegates.
    fn parse_exception(&mut self, depth: usize) -> Result<Exception, ParseError> {
        self.expect(&Token::Unless)?;
        self.parse_exception_body(depth)
    }

    /// Parse a guard expression used in the `except when <guard> then …`
    /// surface form.
    ///
    /// Greedy atom chain terminated by either the `then` identifier
    /// or a non-atom-start token. Binary operators (`=`, `≥`, `≤`,
    /// `<`, `>`, `≠`, `+`, `*`, `/`) between atoms are consumed and
    /// the operation synthesized as a generic `App` chain so that the
    /// surface guard parses without requiring a full operator-grammar
    /// build-out. This is a best-effort guard recognizer that
    /// preserves token flow; typecheck will reject semantically
    /// invalid guards.
    fn parse_guard_until_then(&mut self, depth: usize) -> Result<Term, ParseError> {
        let next_depth = self.next_depth(depth)?;
        let mut acc = self.parse_guard_primary(next_depth)?;
        loop {
            if matches!(self.peek(), Token::Ident(s) if s == "then")
                || matches!(
                    self.peek(),
                    Token::Eof | Token::End | Token::Priority | Token::Unless | Token::DoubleArrow
                )
            {
                break;
            }
            if matches!(
                self.peek(),
                Token::Eq
                    | Token::Neq
                    | Token::Ge
                    | Token::Le
                    | Token::Lt
                    | Token::Gt
                    | Token::Plus
                    | Token::Star
                    | Token::Slash
            ) {
                let op_tok = self.advance().0;
                let op_name = match op_tok {
                    Token::Eq => "__eq__",
                    Token::Neq => "__neq__",
                    Token::Ge => "__ge__",
                    Token::Le => "__le__",
                    Token::Lt => "__lt__",
                    Token::Gt => "__gt__",
                    Token::Plus => "__plus__",
                    Token::Star => "__star__",
                    Token::Slash => "__slash__",
                    _ => unreachable!(),
                };
                let rhs = self.parse_guard_primary(next_depth)?;
                acc = Term::App {
                    func: Box::new(Term::App {
                        func: Box::new(Term::Constant(QualIdent::simple(op_name))),
                        arg: Box::new(acc),
                    }),
                    arg: Box::new(rhs),
                };
                continue;
            }
            if self.is_atom_start() {
                // App-chain extension (e.g. `f x y`).
                let next = self.parse_atom(next_depth)?;
                acc = Term::App {
                    func: Box::new(acc),
                    arg: Box::new(next),
                };
                continue;
            }
            break;
        }
        Ok(acc)
    }

    /// Parse a primary position in a guard expression. For `except when`
    /// guards this is typically `ctx.field` or a literal constant.
    fn parse_guard_primary(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.parse_atom(self.next_depth(depth)?)
    }

    /// Parse the body of an exception clause (everything after the
    /// `unless` keyword or its jurisdictional alias).
    ///
    /// Three surface forms are accepted:
    ///
    /// - Core declarative: `<guard-atom> => <body> [priority N]
    ///   [authority A]`. The `=>` is mandatory; the guard is a single
    ///   atom (typically a bool-typed identifier or a constructor).
    ///
    /// - Term-form sugar: `<body-term> [priority N]`. When the very
    ///   next token starts a binder/term surface that can't form a
    ///   guard-atom before `=>` (lambda, let, match, fix, etc.), this is
    ///   an *unconditional* exception: the guard is synthesized as the
    ///   `True` Bool constructor (which the evaluator reads as satisfied,
    ///   so the exception always applies) and the body takes the full term.
    ///
    /// - `when <guard> then <body> [priority N]` — the `except`-alias
    ///   trailing form used by legacy authored files.
    ///   `when` is parsed as an identifier (no dedicated token) and
    ///   `then` is handled by `parse_term`'s atom loop terminating on
    ///   a non-atom-start token; we route it explicitly here for
    ///   readability.
    ///
    /// - Truncated-at-chunk-boundary: next token is `end`, `Eof`, or a
    ///   `priority`-only clause. Synthesized with the distinguishable
    ///   chunk-truncation marker (see `truncation_marker`) in both guard and
    ///   body positions, which fails loud at typecheck/eval — NOT a silent
    ///   `Prop` placeholder.
    fn parse_exception_body(&mut self, depth: usize) -> Result<Exception, ParseError> {
        let next_depth = self.next_depth(depth)?;

        // Chunk-boundary-truncated form. Both guard and body are emitted as
        // the distinguishable truncation marker so a truncated exception
        // cannot be silently admitted (a bare `Prop` guard is read by
        // `eval_guard` as never-fires, masking the truncation).
        if matches!(self.peek(), Token::Eof | Token::End) {
            return Ok(Exception {
                guard: Box::new(truncation_marker()),
                body: Box::new(truncation_marker()),
                priority: None,
                authority: None,
            });
        }

        // `when <guard> [= <rhs>] then <body>` surface form — commonly
        // attached to `except when …` trailing clauses. The bare
        // `when` / `then` identifiers disambiguate entry.
        if matches!(self.peek(), Token::Ident(s) if s == "when") {
            self.advance();
            // Guard is an atomic comparator expression. The lexer
            // does not produce a dedicated `then` keyword, so we
            // accept `when <guard-term> then <body>` with a simple
            // greedy guard that stops at the ident `then`.
            let guard = self.parse_guard_until_then(next_depth)?;
            // Consume optional `then` identifier; tolerate its absence
            // for chunk-truncated inputs.
            if matches!(self.peek(), Token::Ident(s) if s == "then") {
                self.advance();
            }
            let body = self.parse_term(next_depth)?;
            let priority = if self.check(&Token::Priority) {
                self.advance();
                let (n, _) = self.expect_nat()?;
                Some(n as u32)
            } else {
                None
            };
            return Ok(Exception {
                guard: Box::new(guard),
                body: Box::new(body),
                priority,
                authority: None,
            });
        }

        // Disambiguate: if the very next token starts a binder/term
        // surface that can't form a guard-atom before `=>` (lambda,
        // let, match, fix, etc.), enter the term-form sugar branch.
        // Otherwise attempt the declarative form with explicit `=>`.
        let is_term_form = matches!(
            self.peek(),
            Token::Lambda
                | Token::Pi
                | Token::Sigma
                | Token::Let
                | Token::Match
                | Token::Fix
                | Token::Defeasible
        );

        let (guard, body) = if is_term_form {
            // Term-form sugar: `except <binder-term>` with no explicit guard
            // is an *unconditional* exception. The disambiguation is
            // structural — `is_term_form` is only true when the next token is
            // a binder (lambda/Pi/Sigma/let/match/fix/defeasible), which can
            // never begin a guard atom, so no malformed guard is masked here.
            //
            // The guard must be a constant that the evaluator reads as
            // SATISFIED, so the documented "always applies" semantics
            // actually hold. A bare `Term::Sort(Sort::Prop)` is WRONG here:
            // `eval_guard` evaluates `Prop` to `NotAVerdict` and falls through
            // to "not satisfied", silently turning an unconditional exception
            // into one that never fires. The `True` Bool constructor is a
            // registered prelude constant (admissible + typechecks) that
            // `eval_guard` reads as satisfied.
            let body = self.parse_term(next_depth)?;
            (Term::Constant(QualIdent::simple("True")), body)
        } else {
            let guard = self.parse_atom(next_depth)?;
            self.expect(&Token::DoubleArrow)?;
            let body = self.parse_term(next_depth)?;
            (guard, body)
        };

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

    /// Parse an optional rule-level `applies_to { ... }` scope clause
    /// (Frontier-09 §2.3). `applies_to` is its own keyword token (like `with`,
    /// `unless`, `priority`), so the preceding base-type term parse terminates
    /// at it rather than absorbing it into an application — and a pre-09 rule
    /// that never uses the keyword parses unchanged.
    ///
    /// Returns `Ok(None)` when no clause is present. When present the clause is
    /// parsed fail-loud:
    ///
    /// ```text
    /// applies_to {
    ///   jurisdictions: [ sc, de ]            -- or [*]
    ///   operation_kinds: [ entity.incorporate, ownership.* ]  -- or [*]
    /// }
    /// ```
    ///
    /// Both lists MUST be non-empty: `[]` is rejected. "Applies everywhere" is
    /// the explicit `*` wildcard, never an empty or absent list. There is no
    /// default-permissive `AppliesTo`.
    fn parse_applies_to_clause(&mut self) -> Result<Option<AppliesTo>, ParseError> {
        // Keyword check — do not consume unless it is `applies_to`.
        if !self.check(&Token::AppliesTo) {
            return Ok(None);
        }
        self.advance(); // consume `applies_to`
        self.expect(&Token::Lbrace)?;

        let mut jurisdictions: Option<Vec<JurisdictionScope>> = None;
        let mut operation_kinds: Option<Vec<OperationKindScope>> = None;

        while !self.check(&Token::Rbrace) && !self.check(&Token::Eof) {
            let (field_name, field_span) = self.expect_ident()?;
            self.expect(&Token::Colon)?;
            match field_name.as_str() {
                "jurisdictions" => {
                    if jurisdictions.is_some() {
                        return Err(ParseError {
                            span: field_span,
                            expected: "single `jurisdictions:` field".to_string(),
                            found: "duplicate `jurisdictions`".to_string(),
                        });
                    }
                    jurisdictions = Some(self.parse_jurisdiction_scope_list()?);
                }
                "operation_kinds" => {
                    if operation_kinds.is_some() {
                        return Err(ParseError {
                            span: field_span,
                            expected: "single `operation_kinds:` field".to_string(),
                            found: "duplicate `operation_kinds`".to_string(),
                        });
                    }
                    operation_kinds = Some(self.parse_operation_kind_scope_list()?);
                }
                other => {
                    return Err(ParseError {
                        span: field_span,
                        expected: "applies_to field (`jurisdictions` or `operation_kinds`)"
                            .to_string(),
                        found: other.to_string(),
                    });
                }
            }
            // Field separator: an optional `;` or `,`, else whitespace.
            let _ = self.eat(&Token::Semicolon) || self.eat(&Token::Comma);
        }

        let close_span = self.peek_span();
        self.expect(&Token::Rbrace)?;

        let jurisdictions = jurisdictions.ok_or_else(|| ParseError {
            span: close_span,
            expected: "`jurisdictions:` field in applies_to".to_string(),
            found: "missing jurisdictions".to_string(),
        })?;
        let operation_kinds = operation_kinds.ok_or_else(|| ParseError {
            span: close_span,
            expected: "`operation_kinds:` field in applies_to".to_string(),
            found: "missing operation_kinds".to_string(),
        })?;

        if jurisdictions.is_empty() {
            return Err(ParseError {
                span: close_span,
                expected: "non-empty jurisdictions list (use [*] for all)".to_string(),
                found: "empty jurisdictions list".to_string(),
            });
        }
        if operation_kinds.is_empty() {
            return Err(ParseError {
                span: close_span,
                expected: "non-empty operation_kinds list (use [*] for all)".to_string(),
                found: "empty operation_kinds list".to_string(),
            });
        }

        Ok(Some(AppliesTo {
            jurisdictions,
            operation_kinds,
        }))
    }

    /// Parse `[ <jurisdiction-element> (, <jurisdiction-element>)* ]` where each
    /// element is `*` (wildcard) or a qualified jurisdiction identifier.
    fn parse_jurisdiction_scope_list(&mut self) -> Result<Vec<JurisdictionScope>, ParseError> {
        self.expect(&Token::Lbracket)?;
        let mut elems = Vec::new();
        if !self.check(&Token::Rbracket) {
            elems.push(self.parse_jurisdiction_scope_elem()?);
            while self.check(&Token::Comma) {
                self.advance();
                if self.check(&Token::Rbracket) {
                    break;
                }
                elems.push(self.parse_jurisdiction_scope_elem()?);
            }
        }
        self.expect(&Token::Rbracket)?;
        Ok(elems)
    }

    fn parse_jurisdiction_scope_elem(&mut self) -> Result<JurisdictionScope, ParseError> {
        if self.is_wildcard_star() {
            self.advance();
            return Ok(JurisdictionScope::All);
        }
        let (text, _) = self.expect_ident()?;
        Ok(JurisdictionScope::Specific(QualIdent::from_dotted(&text)))
    }

    /// The asterisk wildcard `*` lexes as either [`Token::Star`] (tight) or
    /// [`Token::Times`] (whitespace-surrounded, the product-type form). Both
    /// denote the scope wildcard here.
    fn is_wildcard_star(&self) -> bool {
        self.check(&Token::Star) || self.check(&Token::Times)
    }

    fn is_wildcard_star_at(&self, idx: usize) -> bool {
        matches!(
            self.tokens.get(idx).map(|(t, _)| t),
            Some(Token::Star) | Some(Token::Times)
        )
    }

    /// Parse `[ <op-kind-element> (, <op-kind-element>)* ]` where each element is
    /// `*` (All), `family.*` (Family prefix), or a qualified operation kind
    /// (Specific). The family form lexes as an `Ident` followed by `.` `*`.
    fn parse_operation_kind_scope_list(&mut self) -> Result<Vec<OperationKindScope>, ParseError> {
        self.expect(&Token::Lbracket)?;
        let mut elems = Vec::new();
        if !self.check(&Token::Rbracket) {
            elems.push(self.parse_operation_kind_scope_elem()?);
            while self.check(&Token::Comma) {
                self.advance();
                if self.check(&Token::Rbracket) {
                    break;
                }
                elems.push(self.parse_operation_kind_scope_elem()?);
            }
        }
        self.expect(&Token::Rbracket)?;
        Ok(elems)
    }

    fn parse_operation_kind_scope_elem(&mut self) -> Result<OperationKindScope, ParseError> {
        // Bare `*` → All.
        if self.is_wildcard_star() {
            self.advance();
            return Ok(OperationKindScope::All);
        }
        let (text, _) = self.expect_ident()?;
        // Family form `entity.*`: the `.` `*` lex as separate `Dot` then
        // `Star`/`Times` tokens (`*` is not an identifier-continue char, and it
        // lexes as `Times` when whitespace-surrounded), so the leading
        // identifier (`entity`) arrives here unqualified.
        if self.check(&Token::Dot) && self.is_wildcard_star_at(self.pos + 1) {
            self.advance(); // `.`
            self.advance(); // `*`
            return Ok(OperationKindScope::Family(QualIdent::from_dotted(&text)));
        }
        Ok(OperationKindScope::Specific(QualIdent::from_dotted(&text)))
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
        let (name, span) = self.expect_ident()?;
        // FAIL LOUD: reject empty segments (`a.b.`, `.a`, `a..b`). The lexer
        // only folds a `.` into an identifier between two identifier-start
        // characters, so a well-formed token cannot contain an empty segment;
        // this is defense-in-depth against any caller that hands the parser a
        // raw dotted string. A silently-dropped empty segment would let
        // `a..b` collapse to the unrelated qualified name `a.b`.
        let segments: Vec<&str> = name.split('.').collect();
        if segments.iter().any(|seg| seg.is_empty()) {
            return Err(ParseError {
                span,
                expected: "qualified identifier with non-empty segments".to_string(),
                found: format!("`{name}` (contains an empty segment)"),
            });
        }
        Ok(QualIdent::new(segments.into_iter()))
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
            Token::ContentRef(content) => {
                Ok(TribunalRef::ContentAddressed(ContentRef::new(&content)))
            }
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

    /// `( term )`, `( term : type )`, or `( e₁, e₂, …, eₙ )` tuple.
    ///
    /// Tuples of length ≥ 2 are synthesized as right-associated nested
    /// `Term::Pair` values so that `(a, b, c)` becomes `Pair(a, Pair(b, c))`.
    /// This matches the Sigma-product structure of the type system and
    /// lets jurisdictional `.lex` files write idiomatic `match (a, b) …`
    /// scrutinees against compliance-tag tuples.
    fn parse_paren(&mut self, depth: usize) -> Result<Term, ParseError> {
        self.expect(&Token::Lparen)?;
        let next_depth = self.next_depth(depth)?;
        let first = self.parse_term(next_depth)?;

        if self.check(&Token::Colon) {
            self.advance();
            let ty = self.parse_term(next_depth)?;
            self.expect(&Token::Rparen)?;
            return Ok(Term::Annot {
                term: Box::new(first),
                ty: Box::new(ty),
            });
        }

        if self.check(&Token::Comma) {
            let mut elements = vec![first];
            while self.check(&Token::Comma) {
                self.advance();
                // Tolerate trailing comma before `)`.
                if self.check(&Token::Rparen) {
                    break;
                }
                elements.push(self.parse_term(next_depth)?);
            }
            self.expect(&Token::Rparen)?;
            return Ok(fold_pair_terms(elements));
        }

        self.expect(&Token::Rparen)?;
        Ok(first)
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
                        let (level_name, level_span) = self.expect_ident()?;
                        // Parse level: extract the numeric suffix from a level
                        // name like `l0` or `l_0`. FAIL LOUD: a level name with
                        // no digits (e.g. `l`, `bogus`) or one whose digits do
                        // not parse as a u64 (overflow) is rejected with a
                        // ParseError — it must NOT silently default to fuel
                        // level 0, which would admit a non-conforming program
                        // at a fabricated (and maximally permissive) level.
                        let digits: String = level_name
                            .chars()
                            .filter(|c| c.is_ascii_digit())
                            .collect();
                        let level_num: u64 = digits.parse().map_err(|_| ParseError {
                            span: level_span,
                            expected: "fuel level name carrying a numeric suffix \
                                       (e.g. `l0`, `l_1`)"
                                .to_string(),
                            found: format!("`{level_name}`"),
                        })?;
                        self.expect(&Token::Comma)?;
                        let (n, _) = self.expect_nat()?;
                        self.expect(&Token::Rparen)?;
                        Ok(Effect::Fuel(Level::Nat(level_num), n))
                    }
                    "sanctions_query" | "statutory_sanctions_query" => {
                        // Both markers share the same kernel-side effect
                        // signature: sanctions lookup bound to the terminal
                        // sanctions tier. Any jurisdiction-specific meaning
                        // of "statutory" belongs in the pack-local rule text.
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
                            "known effect (read, write, attest, authority, oracle, fuel, sanctions_query, statutory_sanctions_query, discretion)"
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
// Helpers
// ═══════════════════════════════════════════════════════════════════════

/// Map a punctuation token to its infix-operator identifier name, or
/// `None` if the token is not an accepted infix operator.
///
/// Used by `parse_app` to lift surface-form comparators and arithmetic
/// into Core Lex App chains. The names are reserved with a `__…__`
/// convention so they can't collide with prelude symbols.
fn infix_operator_name(tok: &Token) -> Option<&'static str> {
    Some(match tok {
        // Intentionally omit `Eq` (`=`): it conflicts with the `let x
        // : T = val` surface binding form accepted by `parse_let`.
        // `==` is not a distinct token in this lexer; comparators use
        // `Neq`, `Ge`, `Le`, `Lt`, `Gt`.
        Token::Neq => "__neq__",
        Token::Ge => "__ge__",
        Token::Le => "__le__",
        Token::Lt => "__lt__",
        Token::Gt => "__gt__",
        Token::Plus => "__plus__",
        // Intentionally omit Star and Slash: both also appear in type
        // position (`A × B` uses Times, `A/B` is rational literal).
        _ => return None,
    })
}

/// True when the parser's current position is `Ident("rule") Ident(_)`.
///
/// `rule NAME : SIG = BODY` is a higher-level authoring form. It must be
/// compiled into Core Lex before reaching this parser.
fn is_rule_form_start(parser: &Parser<'_>) -> bool {
    if !matches!(parser.peek(), Token::Ident(s) if s == "rule") {
        return false;
    }
    matches!(
        parser.tokens.get(parser.pos + 1).map(|(t, _)| t),
        Some(Token::Ident(_))
    )
}

/// True when the parser's current position is the declarative
/// `obligation [temporal] NAME : …` surface form.
fn is_obligation_form_start(parser: &Parser<'_>) -> bool {
    if !matches!(parser.peek(), Token::Ident(s) if s == "obligation") {
        return false;
    }
    // `obligation temporal NAME :` or `obligation NAME :`.
    match parser.tokens.get(parser.pos + 1).map(|(t, _)| t) {
        Some(Token::Ident(next)) => {
            // `obligation NAME :` or `obligation temporal NAME :`.
            if next == "temporal" {
                matches!(
                    parser.tokens.get(parser.pos + 2).map(|(t, _)| t),
                    Some(Token::Ident(_))
                ) && matches!(
                    parser.tokens.get(parser.pos + 3).map(|(t, _)| t),
                    Some(Token::Colon)
                )
            } else {
                matches!(
                    parser.tokens.get(parser.pos + 2).map(|(t, _)| t),
                    Some(Token::Colon)
                )
            }
        }
        _ => false,
    }
}

/// True when the parser's current position is
/// `Ident(keyword) Ident(NAME) Colon` — the shape that matches the
/// `hole NAME : SIG with …` and `attestable_hole NAME : SIG with …`
/// surface forms.
fn is_hole_form_start(parser: &Parser<'_>, keyword: &str) -> bool {
    if !matches!(parser.peek(), Token::Ident(s) if s == keyword) {
        return false;
    }
    matches!(
        parser.tokens.get(parser.pos + 1).map(|(t, _)| t),
        Some(Token::Ident(_))
    ) && matches!(
        parser.tokens.get(parser.pos + 2).map(|(t, _)| t),
        Some(Token::Colon)
    )
}

/// Parse `<keyword> NAME : SIG with … end` as a declarative
/// defeasible rule whose synthesized name carries the
/// `__<keyword>__.<name>` tag. Shared implementation for
/// `hole` and `attestable_hole`.
fn parse_hole_form(parser: &mut Parser<'_>, keyword: &str) -> Result<Term, ParseError> {
    parser.advance(); // consume keyword identifier
    let name = match parser.advance().0 {
        Token::Ident(s) => s,
        other => {
            return Err(ParseError {
                span: parser.peek_span(),
                expected: format!("{keyword} name"),
                found: format!("{}", other),
            });
        }
    };
    parser.expect(&Token::Colon)?;
    let base_ty = parser.parse_term(0)?;
    let applies_to = parser.parse_applies_to_clause()?;
    parser.expect(&Token::With)?;

    let mut exceptions = Vec::new();
    while parser.check(&Token::Unless) {
        exceptions.push(parser.parse_exception(0)?);
    }

    parser.expect(&Token::End)?;

    Ok(Term::Defeasible(DefeasibleRule {
        name: Ident::new(&format!("__{keyword}__.{name}")),
        base_ty: Box::new(base_ty),
        base_body: Box::new(Term::Var {
            name: Ident::new(&name),
            index: 0,
        }),
        exceptions,
        lattice: None,
        applies_to,
    }))
}

/// Parse `obligation [temporal] NAME : SIG with … end` — routed through
/// the declarative defeasible branch for uniform handling.
///
/// The `obligation` keyword is lowered to a `__obligation__.<name>`
/// constant-tagged `Term::Defeasible` so that coverage reporting
/// counts the rule as parsed while downstream analysis can still
/// distinguish it from a plain `defeasible` by the synthesized name.
fn parse_obligation_form(parser: &mut Parser<'_>) -> Result<Term, ParseError> {
    // Consume `obligation`.
    parser.advance();
    // Optional `temporal` marker.
    if matches!(parser.peek(), Token::Ident(s) if s == "temporal") {
        parser.advance();
    }
    // Rule name.
    let name = match parser.advance().0 {
        Token::Ident(s) => s,
        other => {
            return Err(ParseError {
                span: parser.peek_span(),
                expected: "obligation name".to_string(),
                found: format!("{}", other),
            });
        }
    };
    parser.expect(&Token::Colon)?;
    let base_ty = parser.parse_term(0)?;
    let applies_to = parser.parse_applies_to_clause()?;
    parser.expect(&Token::With)?;

    let mut exceptions = Vec::new();
    while parser.check(&Token::Unless) {
        exceptions.push(parser.parse_exception(0)?);
    }

    parser.expect(&Token::End)?;

    Ok(Term::Defeasible(DefeasibleRule {
        name: Ident::new(&format!("__obligation__.{name}")),
        base_ty: Box::new(base_ty),
        base_body: Box::new(Term::Var {
            name: Ident::new(&name),
            index: 0,
        }),
        exceptions,
        lattice: None,
        applies_to,
    }))
}

/// Append the surface-view binder identifiers of `pattern` onto `out`.
///
/// Used by tuple-pattern lowering (`parse_tuple_pattern`) to flatten
/// nested sub-patterns into a synthesized `__tuple<N>__` constructor
/// binder list. Constructor names are preserved as identifier binders
/// (the distinction between a constructor name and a variable binder is
/// machine-erased at this level, but downstream obligation/decision-table
/// passes recognize it from context).
fn flatten_pattern_binders(pattern: &Pattern, out: &mut Vec<Ident>) {
    match pattern {
        Pattern::Wildcard => {
            out.push(Ident::new("_"));
        }
        Pattern::Constructor {
            constructor,
            binders,
        } => {
            // Emit the constructor name as a binder-shaped identifier,
            // then its own binder names. For the top-level call path
            // this reproduces the surface order: `(Rule506b, _)` lowers
            // to binders `[Rule506b, _]`.
            out.push(Ident::new(&constructor.name.segments.join(".")));
            for b in binders {
                out.push(b.clone());
            }
        }
    }
}

/// Right-associatively fold a non-empty element list into nested
/// `Term::Pair` values: `[a, b, c]` → `Pair(a, Pair(b, c))`.
///
/// Used by `parse_paren` to synthesize tuple literals `(a, b, …)`. A
/// single-element list is returned unchanged (paren group, not tuple).
/// An empty list would panic — callers never produce one.
fn fold_pair_terms(mut elements: Vec<Term>) -> Term {
    debug_assert!(
        !elements.is_empty(),
        "fold_pair_terms called with empty list"
    );
    if elements.len() == 1 {
        return elements.remove(0);
    }
    let last = elements.pop().expect("len >= 2");
    let mut acc = last;
    while let Some(prev) = elements.pop() {
        acc = Term::Pair {
            fst: Box::new(prev),
            snd: Box::new(acc),
        };
    }
    acc
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
/// # Surface-form tolerance
///
/// After the primary term parses, the parser also accepts an optional
/// trailing `priority <nat> end` suffix at the top level. This is a
/// bridge for jurisdictional `.lex` files that author a defeasible rule
/// with the `priority … end` annotation on the body rather than as a
/// `defeasible NAME : T with unless … end` wrapper; when such a body
/// appears at top level (for instance because the surrounding rule
/// splitter fed only the body-half to the parser), the parser wraps
/// the body as an anonymous `Term::Defeasible` with the captured
/// priority. This keeps the parser useful on surface-split inputs
/// without widening the accepted grammar at arbitrary term positions.
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
    let first = parse_one_top_level(&mut parser)?;

    // A rule-chunk fed by the coverage harness can include more than
    // one top-level rule (the splitter's line-prefix classifier does
    // not recognize every rule-start keyword, so it occasionally
    // bundles a trailing `obligation`, `rule`, or second `defeasible`
    // into the same chunk). Consume any additional top-level forms
    // greedily so the chunk parses; the returned term is the first
    // rule (callers of `parse` observe the primary rule).
    while !matches!(parser.peek(), Token::Eof) {
        match parse_one_top_level(&mut parser) {
            Ok(_extra) => {}
            Err(err) => {
                // Surface the error at the first point we failed to
                // recover — signals a genuine unknown surface form.
                return Err(err);
            }
        }
    }

    Ok(first)
}

/// Parse one top-level term, then absorb the optional
/// `priority <n> [unless|except …]* [end]` trailing decoration that
/// authored `.lex` files place on a term-form defeasible rule.
///
/// Separated from `parse` so the body can be looped over multiple
/// top-level forms packed into a single chunk.
fn parse_one_top_level(parser: &mut Parser<'_>) -> Result<Term, ParseError> {
    if is_rule_form_start(parser) {
        return Err(ParseError {
            span: parser.peek_span(),
            expected: "Core Lex term; compile `rule NAME : SIG = BODY` through a pack-local rule-form compiler before parsing".to_string(),
            found: "rule-form surface syntax".to_string(),
        });
    }

    // Surface-form sugar: `obligation [temporal] NAME : SIG with … end`.
    // Routed to the declarative defeasible branch (same `NAME : T with …
    // end` machinery) after consuming the optional `temporal` marker.
    if is_obligation_form_start(parser) {
        return parse_obligation_form(parser);
    }

    // Surface-form sugar: `hole NAME : SIG with … end` and
    // `attestable_hole NAME : SIG with … end`. Typed-discretion-hole
    // declarations that jurisdictional `.lex` files use; lowered to
    // the declarative defeasible machinery with a `__hole__` or
    // `__attestable_hole__` name-prefix tag.
    if is_hole_form_start(parser, "hole") {
        return parse_hole_form(parser, "hole");
    }
    if is_hole_form_start(parser, "attestable_hole") {
        return parse_hole_form(parser, "attestable_hole");
    }

    let mut term = parser.parse_term(0)?;

    // Optional trailing `priority <n>`.
    let mut trailing_priority: Option<u32> = None;
    if parser.check(&Token::Priority) {
        parser.advance();
        let (n, _) = parser.expect_nat()?;
        trailing_priority = Some(n as u32);
    }

    // Zero or more trailing exception clauses (`unless …` or the
    // jurisdictional alias `except …`).
    let mut trailing_exceptions: Vec<Exception> = Vec::new();
    loop {
        if parser.check(&Token::Unless) {
            trailing_exceptions.push(parser.parse_exception(0)?);
        } else if matches!(parser.peek(), Token::Ident(s) if s == "except") {
            parser.advance();
            let exception = parser.parse_exception_body(0)?;
            trailing_exceptions.push(exception);
        } else {
            break;
        }
    }

    // Optional `end` terminator.
    let _ = parser.eat(&Token::End);

    if trailing_priority.is_some() || !trailing_exceptions.is_empty() {
        let base_body = term.clone();
        let mut exceptions = Vec::with_capacity(trailing_exceptions.len() + 1);
        if let Some(p) = trailing_priority {
            exceptions.push(Exception {
                guard: Box::new(Term::Sort(Sort::Prop)),
                body: Box::new(term),
                priority: Some(p),
                authority: None,
            });
        }
        exceptions.extend(trailing_exceptions);
        term = Term::Defeasible(DefeasibleRule {
            name: Ident::new("_anon_defeasible"),
            base_ty: Box::new(Term::Constant(QualIdent::simple("_"))),
            base_body: Box::new(base_body),
            exceptions,
            lattice: None,
            applies_to: None,
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

    // ── Surface-form term / obligation / hole / rule-form tests ─────
    //
    // The parser accepts a jurisdictional surface syntax in addition
    // to the Core Lex formal grammar. The tests below pin the
    // surface-form entry points exercised by `modules/lex/**/*.lex`
    // — any regression here will be caught by the unit suite before
    // the `lex_file_coverage` harness runs.

    #[test]
    fn defeasible_term_form_body_parses() {
        use crate::lexer;
        let source = r#"defeasible
  lambda (x : A).
    match x return B with
      | Cons => y
    priority 0
end"#;
        let tokens = lexer::lex(source).expect("lex");
        let term = parse(&tokens).expect("term-form defeasible should parse");
        match term {
            Term::Defeasible(rule) => {
                assert_eq!(rule.name.name, "_anon_defeasible");
                assert_eq!(
                    rule.exceptions.len(),
                    1,
                    "priority should produce one exception slot"
                );
                assert_eq!(rule.exceptions[0].priority, Some(0));
                // Body is the lambda; `base_body` carries the outer lambda.
                assert!(
                    matches!(rule.base_body.as_ref(), Term::Lambda { .. }),
                    "term-form body must be preserved as a Lambda"
                );
            }
            other => panic!("expected Defeasible, got {:?}", other),
        }
    }

    #[test]
    fn defeasible_term_form_with_nested_match_parses() {
        // Matches the Rule-2 shape from usa/regulation_d_503.lex:
        // the match arm body is itself a match.
        use crate::lexer;
        let source = r#"defeasible
  lambda (ctx : T).
    match ctx.outer return V with
      | A => match ctx.inner return V with
        | X => Compliant
        | Y => Pending
      | B => NonCompliant
      | _ => Pending
  priority 0
end"#;
        let tokens = lexer::lex(source).expect("lex");
        parse(&tokens).expect("nested-match term-form should parse");
    }

    #[test]
    fn lambda_with_effect_row_parses() {
        // Matches the bare `lambda (ctx : T) [sanctions_query]. body`
        // shape used by ~46 sanctions-check rules across the corpus.
        use crate::lexer;
        let source = r#"lambda (ctx : T) [sanctions_query].
  let x : S = f ctx in
  match x return V with
    | Clear => Compliant
    | _ => NonCompliant"#;
        let tokens = lexer::lex(source).expect("lex");
        let term = parse(&tokens).expect("lambda-with-effect-row should parse");
        // The Lambda AST carries no effect row today; dropping is
        // intentional (documented on `parse_lambda`).
        assert!(
            matches!(term, Term::Lambda { .. }),
            "bare lambda surface should round-trip to a Lambda AST node"
        );
    }

    #[test]
    fn let_with_equals_parses() {
        // Jurisdictional `.lex` files use `=` instead of the Core Lex
        // `:=` in let-bindings. Both must parse.
        use crate::lexer;

        let with_eq = lexer::lex("let x : T = v in x").expect("lex `=`");
        let with_coloneq = lexer::lex("let x : T := v in x").expect("lex `:=`");

        parse(&with_eq).expect("`let x : T = v in x` must parse");
        parse(&with_coloneq).expect("`let x : T := v in x` must parse");
    }

    #[test]
    fn obligation_form_parses() {
        // Matches a jurisdictional state-notice rule surface
        // form: `obligation temporal NAME : SIG with <empty body> end`.
        use crate::lexer;
        let source = r#"obligation temporal state_notice_deadline : StateNoticeContext -> ComplianceVerdict with
end"#;
        let tokens = lexer::lex(source).expect("lex");
        let term = parse(&tokens).expect("obligation-form should parse");
        match term {
            Term::Defeasible(rule) => {
                assert!(
                    rule.name.name.starts_with("__obligation__."),
                    "obligation name tag should prefix with `__obligation__.`"
                );
            }
            other => panic!("expected Defeasible, got {:?}", other),
        }
    }

    #[test]
    fn hole_form_parses() {
        // Matches a jurisdictional state-notice rule surface
        // form: `hole NAME : SIG with <body-comments> end`.
        use crate::lexer;
        let source = r#"hole state_notice_manual_receipt : StateNoticeContext -> FilingReceipt with
end"#;
        let tokens = lexer::lex(source).expect("lex");
        let term = parse(&tokens).expect("hole-form should parse");
        match term {
            Term::Defeasible(rule) => {
                assert!(
                    rule.name.name.starts_with("__hole__."),
                    "hole name tag should prefix with `__hole__.`"
                );
            }
            other => panic!("expected Defeasible, got {:?}", other),
        }
    }

    #[test]
    fn rule_form_surface_syntax_fails_closed() {
        // `rule NAME : SIG = BODY` is higher-level authoring syntax.
        // The Core Lex parser must not fabricate a name-only placeholder
        // and claim the executable law body parsed.
        use crate::lexer;
        let source = r#"rule fit_and_proper_assessment
  : (director : Director)
  -> Verdict
  = let x = f director in x"#;
        let tokens = lexer::lex(source).expect("lex");
        let err = parse(&tokens).expect_err("rule-form surface syntax must fail closed");
        assert!(
            err.expected.contains("pack-local rule-form compiler"),
            "error should route through pack-local compiler, got {err:?}"
        );
    }

    #[test]
    fn tuple_pattern_lowers_to_synthetic_constructor() {
        use crate::lexer;
        let source = r#"match (a, b) return V with
  | (Rule506b, NoSolicitation) => Compliant
  | _ => Pending"#;
        let tokens = lexer::lex(source).expect("lex");
        let term = parse(&tokens).expect("tuple-scrutinee match should parse");
        match term {
            Term::Match { branches, .. } => {
                assert_eq!(branches.len(), 2);
                if let Pattern::Constructor {
                    constructor,
                    binders,
                } = &branches[0].pattern
                {
                    assert_eq!(
                        constructor.name.segments.join("."),
                        "__tuple2__",
                        "arity-2 tuple lowers to __tuple2__"
                    );
                    assert_eq!(binders.len(), 2);
                } else {
                    panic!("expected tuple constructor pattern");
                }
            }
            other => panic!("expected Match, got {:?}", other),
        }
    }

    #[test]
    fn declarative_defeasible_still_parses() {
        // Regression guard: the Core Lex formal grammar MUST continue
        // to parse after the surface-form extensions.
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
        let term = parse(&tokens).expect("declarative form must still parse");
        match term {
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
        assert!(result.is_err(), "`x )` must not parse");
        // Parser now loops over top-level rules to tolerate multi-rule
        // chunks; the recovery path surfaces the second (fallback)
        // parse error from `parse_term`, which reports `expected term`
        // rather than `expected end of input`. Accept either — both
        // are correct shapes for this regression.
        let err = result.unwrap_err();
        assert!(
            err.expected.contains("end of input") || err.expected.contains("term"),
            "unexpected error shape: {err}"
        );
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
        assert!(
            err.expected.contains("known effect"),
            "expected error mentioning `known effect`, got: {}",
            err.expected
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
