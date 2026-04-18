//! Token types for the Lex lexer.
//!
//! Defines the complete token vocabulary for Core Lex as specified in
//! `docs/language-reference.md` (lexical structure).

use std::fmt;

// ---------------------------------------------------------------------------
// Span — source location
// ---------------------------------------------------------------------------

/// Byte-offset span plus line/column for diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    /// Start byte offset (inclusive).
    pub start: usize,
    /// End byte offset (exclusive).
    pub end: usize,
    /// 1-based line number at `start`.
    pub line: u32,
    /// 1-based column number at `start`.
    pub col: u32,
}

impl Span {
    /// Create a new span.
    pub fn new(start: usize, end: usize, line: u32, col: u32) -> Self {
        Self {
            start,
            end,
            line,
            col,
        }
    }

    /// Length of the span in bytes.
    pub fn len(&self) -> usize {
        self.end.saturating_sub(self.start)
    }

    /// Whether the span is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

// ---------------------------------------------------------------------------
// Spanned — attaches a Span to any value
// ---------------------------------------------------------------------------

/// A value paired with its source span.
pub type Spanned<T> = (T, Span);

// ---------------------------------------------------------------------------
// TokenError — lexer error variants
// ---------------------------------------------------------------------------

/// Errors produced during lexical analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenError {
    /// An unexpected character was encountered.
    UnexpectedChar(char, Span),
    /// A string literal was not terminated before end-of-input.
    UnterminatedString(Span),
    /// A block comment `{- … -}` was not terminated.
    UnterminatedBlockComment(Span),
    /// A numeric literal could not be parsed.
    InvalidNumber(String, Span),
    /// A `blake3:` hash literal was malformed.
    InvalidHash(String, Span),
    /// A `lex://` content reference was malformed.
    InvalidContentRef(String, Span),
    /// An invalid escape sequence inside a string literal.
    InvalidEscape(char, Span),
    /// A token (identifier, string, or comment) exceeded the maximum allowed length.
    TokenTooLong(String, Span),
    /// Block comment nesting exceeded the maximum allowed depth.
    CommentNestingTooDeep(Span),
    /// An internal lexer invariant was violated (e.g. bump after peek returned None).
    InternalError(String),
}

impl fmt::Display for TokenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedChar(c, sp) => {
                write!(f, "unexpected character '{}' at {}:{}", c, sp.line, sp.col)
            }
            Self::UnterminatedString(sp) => {
                write!(
                    f,
                    "unterminated string literal starting at {}:{}",
                    sp.line, sp.col
                )
            }
            Self::UnterminatedBlockComment(sp) => {
                write!(
                    f,
                    "unterminated block comment starting at {}:{}",
                    sp.line, sp.col
                )
            }
            Self::InvalidNumber(s, sp) => {
                write!(
                    f,
                    "invalid number literal '{}' at {}:{}",
                    s, sp.line, sp.col
                )
            }
            Self::InvalidHash(s, sp) => {
                write!(f, "invalid hash literal '{}' at {}:{}", s, sp.line, sp.col)
            }
            Self::InvalidContentRef(s, sp) => {
                write!(
                    f,
                    "invalid content reference '{}' at {}:{}",
                    s, sp.line, sp.col
                )
            }
            Self::InvalidEscape(c, sp) => {
                write!(
                    f,
                    "invalid escape sequence '\\{}' at {}:{}",
                    c, sp.line, sp.col
                )
            }
            Self::TokenTooLong(kind, sp) => {
                write!(
                    f,
                    "{} exceeds maximum token length at {}:{}",
                    kind, sp.line, sp.col
                )
            }
            Self::CommentNestingTooDeep(sp) => {
                write!(
                    f,
                    "block comment nesting too deep at {}:{}",
                    sp.line, sp.col
                )
            }
            Self::InternalError(msg) => {
                write!(f, "internal lexer error: {}", msg)
            }
        }
    }
}

impl std::error::Error for TokenError {}

// ---------------------------------------------------------------------------
// Token — the core token enum
// ---------------------------------------------------------------------------

/// Every token the Lex lexer can produce.
///
/// Variant ordering follows the grammar document: keywords, then literals,
/// then punctuation/operators, then structural tokens.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    // ── Keywords ─────────────────────────────────────────────────────
    /// `λ` or `lambda`
    Lambda,
    /// `Π` or `Pi`
    Pi,
    /// `Σ` or `Sigma`
    Sigma,
    /// `→` or `->`
    Arrow,
    /// `×` or `*` (in type position, product)
    Times,
    /// `let`
    Let,
    /// `in`
    In,
    /// `match`
    Match,
    /// `return`
    Return,
    /// `with`
    With,
    /// `fix`
    Fix,
    /// `defeasible`
    Defeasible,
    /// `unless`
    Unless,
    /// `priority`
    Priority,
    /// `end`
    End,
    /// `Type` (universe sort)
    Type,
    /// `Prop` (proof-irrelevant sort)
    Prop,
    /// `Rule` (rule sort)
    Rule,
    /// `Time₀` or `Time0`
    Time0,
    /// `Time₁` or `Time1`
    Time1,
    /// `asof₀` or `asof0`
    AsOf0,
    /// `asof₁` or `asof1`
    AsOf1,
    /// `lift₀` or `lift0`
    Lift0,
    /// `derive₁` or `derive1`
    Derive1,
    /// `π₁` or `pi_1`
    Proj1,
    /// `π₂` or `pi_2`
    Proj2,
    /// `coerce`
    Coerce,
    /// `axiom`
    Axiom,
    /// `fill` (hole filling / metavariable instantiation)
    Fill,
    /// `balance`
    Balance,
    /// `unlock`
    Unlock,
    /// `defeat`
    Defeat,
    /// `sanctions-dominance`
    SanctionsDominance,

    // ── Literals ─────────────────────────────────────────────────────
    /// Identifier (including qualified identifiers before resolution).
    Ident(String),
    /// Natural-number literal.
    Nat(u64),
    /// Integer literal (may be negative).
    Int(i64),
    /// Rational literal `p/q` — numerator and denominator.
    Rat(i64, u64),
    /// String literal (contents only, without surrounding quotes).
    StringLit(String),
    /// `blake3:<hex64>` hash literal.
    Hash(String),
    /// `lex://<hash>` content-addressed reference.
    ContentRef(String),
    /// Level variable `ℓ0`, `ℓ1`, …
    LevelVar(String),

    // ── Punctuation / Operators ──────────────────────────────────────
    /// `(`
    Lparen,
    /// `)`
    Rparen,
    /// `⟨` or `<` in angle-bracket context
    Langle,
    /// `⟩` or `>` in angle-bracket context
    Rangle,
    /// `[`
    Lbracket,
    /// `]`
    Rbracket,
    /// `{`
    Lbrace,
    /// `}`
    Rbrace,
    /// `.`
    Dot,
    /// `,`
    Comma,
    /// `:`
    Colon,
    /// `:=`
    ColonEq,
    /// `;`
    Semicolon,
    /// `|`
    Pipe,
    /// `⇒` or `=>`
    DoubleArrow,
    /// `_`
    Underscore,
    /// `?`
    Question,
    /// `@`
    At,
    /// `!`
    Bang,
    /// `=`
    Eq,
    /// `≠` or `!=`
    Neq,
    /// `≤` or `<=`
    Le,
    /// `≥` or `>=`
    Ge,
    /// `<`
    Lt,
    /// `>`
    Gt,
    /// `+`
    Plus,
    /// `*`
    Star,
    /// `/`
    Slash,

    // ── Structural ───────────────────────────────────────────────────
    /// Comment text (line `--` or block `{- -}`).
    Comment(String),
    /// End of input sentinel.
    Eof,
}

// ---------------------------------------------------------------------------
// Classification helpers
// ---------------------------------------------------------------------------

impl Token {
    /// Returns `true` if this token is a language keyword.
    pub fn is_keyword(&self) -> bool {
        matches!(
            self,
            Token::Lambda
                | Token::Pi
                | Token::Sigma
                | Token::Arrow
                | Token::Times
                | Token::Let
                | Token::In
                | Token::Match
                | Token::Return
                | Token::With
                | Token::Fix
                | Token::Defeasible
                | Token::Unless
                | Token::Priority
                | Token::End
                | Token::Type
                | Token::Prop
                | Token::Rule
                | Token::Time0
                | Token::Time1
                | Token::AsOf0
                | Token::AsOf1
                | Token::Lift0
                | Token::Derive1
                | Token::Proj1
                | Token::Proj2
                | Token::Coerce
                | Token::Axiom
                | Token::Fill
                | Token::Balance
                | Token::Unlock
                | Token::Defeat
                | Token::SanctionsDominance
        )
    }

    /// Returns `true` if this token is punctuation or an operator.
    pub fn is_punctuation(&self) -> bool {
        matches!(
            self,
            Token::Lparen
                | Token::Rparen
                | Token::Langle
                | Token::Rangle
                | Token::Lbracket
                | Token::Rbracket
                | Token::Lbrace
                | Token::Rbrace
                | Token::Dot
                | Token::Comma
                | Token::Colon
                | Token::ColonEq
                | Token::Semicolon
                | Token::Pipe
                | Token::DoubleArrow
                | Token::Underscore
                | Token::Question
                | Token::At
                | Token::Bang
                | Token::Eq
                | Token::Neq
                | Token::Le
                | Token::Ge
                | Token::Lt
                | Token::Gt
                | Token::Plus
                | Token::Star
                | Token::Slash
        )
    }

    /// Returns `true` if this token carries a literal value.
    pub fn is_literal(&self) -> bool {
        matches!(
            self,
            Token::Ident(_)
                | Token::Nat(_)
                | Token::Int(_)
                | Token::Rat(_, _)
                | Token::StringLit(_)
                | Token::Hash(_)
                | Token::ContentRef(_)
                | Token::LevelVar(_)
        )
    }
}

// ---------------------------------------------------------------------------
// Display — source-faithful representation
// ---------------------------------------------------------------------------

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // Keywords
            Token::Lambda => write!(f, "λ"),
            Token::Pi => write!(f, "Π"),
            Token::Sigma => write!(f, "Σ"),
            Token::Arrow => write!(f, "→"),
            Token::Times => write!(f, "×"),
            Token::Let => write!(f, "let"),
            Token::In => write!(f, "in"),
            Token::Match => write!(f, "match"),
            Token::Return => write!(f, "return"),
            Token::With => write!(f, "with"),
            Token::Fix => write!(f, "fix"),
            Token::Defeasible => write!(f, "defeasible"),
            Token::Unless => write!(f, "unless"),
            Token::Priority => write!(f, "priority"),
            Token::End => write!(f, "end"),
            Token::Type => write!(f, "Type"),
            Token::Prop => write!(f, "Prop"),
            Token::Rule => write!(f, "Rule"),
            Token::Time0 => write!(f, "Time₀"),
            Token::Time1 => write!(f, "Time₁"),
            Token::AsOf0 => write!(f, "asof₀"),
            Token::AsOf1 => write!(f, "asof₁"),
            Token::Lift0 => write!(f, "lift₀"),
            Token::Derive1 => write!(f, "derive₁"),
            Token::Proj1 => write!(f, "π₁"),
            Token::Proj2 => write!(f, "π₂"),
            Token::Coerce => write!(f, "coerce"),
            Token::Axiom => write!(f, "axiom"),
            Token::Fill => write!(f, "fill"),
            Token::Balance => write!(f, "balance"),
            Token::Unlock => write!(f, "unlock"),
            Token::Defeat => write!(f, "defeat"),
            Token::SanctionsDominance => write!(f, "sanctions-dominance"),

            // Literals
            Token::Ident(s) => write!(f, "{}", s),
            Token::Nat(n) => write!(f, "{}", n),
            Token::Int(n) => write!(f, "{}", n),
            Token::Rat(p, q) => write!(f, "{}/{}", p, q),
            Token::StringLit(s) => write!(f, "\"{}\"", s),
            Token::Hash(h) => write!(f, "blake3:{}", h),
            Token::ContentRef(r) => write!(f, "lex://{}", r),
            Token::LevelVar(v) => write!(f, "{}", v),

            // Punctuation / Operators
            Token::Lparen => write!(f, "("),
            Token::Rparen => write!(f, ")"),
            Token::Langle => write!(f, "⟨"),
            Token::Rangle => write!(f, "⟩"),
            Token::Lbracket => write!(f, "["),
            Token::Rbracket => write!(f, "]"),
            Token::Lbrace => write!(f, "{{"),
            Token::Rbrace => write!(f, "}}"),
            Token::Dot => write!(f, "."),
            Token::Comma => write!(f, ","),
            Token::Colon => write!(f, ":"),
            Token::ColonEq => write!(f, ":="),
            Token::Semicolon => write!(f, ";"),
            Token::Pipe => write!(f, "|"),
            Token::DoubleArrow => write!(f, "⇒"),
            Token::Underscore => write!(f, "_"),
            Token::Question => write!(f, "?"),
            Token::At => write!(f, "@"),
            Token::Bang => write!(f, "!"),
            Token::Eq => write!(f, "="),
            Token::Neq => write!(f, "≠"),
            Token::Le => write!(f, "≤"),
            Token::Ge => write!(f, "≥"),
            Token::Lt => write!(f, "<"),
            Token::Gt => write!(f, ">"),
            Token::Plus => write!(f, "+"),
            Token::Star => write!(f, "*"),
            Token::Slash => write!(f, "/"),

            // Structural
            Token::Comment(text) => write!(f, "-- {}", text),
            Token::Eof => write!(f, "<eof>"),
        }
    }
}

// ---------------------------------------------------------------------------
// Keyword lookup
// ---------------------------------------------------------------------------

impl Token {
    /// Try to resolve an identifier string to a keyword token.
    ///
    /// Returns `None` if `s` is not a keyword — the caller should then
    /// produce `Token::Ident(s)`.
    pub fn keyword_from_str(s: &str) -> Option<Token> {
        match s {
            "lambda" | "λ" => Some(Token::Lambda),
            "Pi" | "Π" => Some(Token::Pi),
            "Sigma" | "Σ" => Some(Token::Sigma),
            "let" => Some(Token::Let),
            "in" => Some(Token::In),
            "match" => Some(Token::Match),
            "return" => Some(Token::Return),
            "with" => Some(Token::With),
            "fix" => Some(Token::Fix),
            "defeasible" => Some(Token::Defeasible),
            "unless" => Some(Token::Unless),
            "priority" => Some(Token::Priority),
            "end" => Some(Token::End),
            "Type" => Some(Token::Type),
            "Prop" => Some(Token::Prop),
            "Rule" => Some(Token::Rule),
            "Time0" | "Time₀" => Some(Token::Time0),
            "Time1" | "Time₁" => Some(Token::Time1),
            "asof0" | "asof₀" => Some(Token::AsOf0),
            "asof1" | "asof₁" => Some(Token::AsOf1),
            "lift0" | "lift₀" => Some(Token::Lift0),
            "derive1" | "derive₁" => Some(Token::Derive1),
            "pi_1" | "π₁" => Some(Token::Proj1),
            "pi_2" | "π₂" => Some(Token::Proj2),
            "coerce" => Some(Token::Coerce),
            "axiom" => Some(Token::Axiom),
            "fill" => Some(Token::Fill),
            "balance" => Some(Token::Balance),
            "unlock" => Some(Token::Unlock),
            "defeat" => Some(Token::Defeat),
            "sanctions-dominance" => Some(Token::SanctionsDominance),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keyword_classification() {
        assert!(Token::Lambda.is_keyword());
        assert!(Token::Pi.is_keyword());
        assert!(Token::Proj1.is_keyword());
        assert!(Token::Fill.is_keyword());
        assert!(!Token::Ident("x".into()).is_keyword());
        assert!(!Token::Lparen.is_keyword());
        assert!(!Token::Eof.is_keyword());
    }

    #[test]
    fn punctuation_classification() {
        assert!(Token::Lparen.is_punctuation());
        assert!(Token::DoubleArrow.is_punctuation());
        assert!(Token::Slash.is_punctuation());
        assert!(!Token::Lambda.is_punctuation());
        assert!(!Token::Nat(42).is_punctuation());
    }

    #[test]
    fn literal_classification() {
        assert!(Token::Ident("foo".into()).is_literal());
        assert!(Token::Nat(0).is_literal());
        assert!(Token::Int(-1).is_literal());
        assert!(Token::Rat(1, 3).is_literal());
        assert!(Token::StringLit("hi".into()).is_literal());
        assert!(Token::Hash("abc".into()).is_literal());
        assert!(Token::ContentRef("abc".into()).is_literal());
        assert!(Token::LevelVar("ℓ0".into()).is_literal());
        assert!(!Token::Lambda.is_literal());
        assert!(!Token::Lparen.is_literal());
    }

    #[test]
    fn display_keywords() {
        assert_eq!(Token::Lambda.to_string(), "λ");
        assert_eq!(Token::Pi.to_string(), "Π");
        assert_eq!(Token::Sigma.to_string(), "Σ");
        assert_eq!(Token::Arrow.to_string(), "→");
        assert_eq!(Token::Times.to_string(), "×");
        assert_eq!(Token::Let.to_string(), "let");
        assert_eq!(Token::Time0.to_string(), "Time₀");
        assert_eq!(Token::Derive1.to_string(), "derive₁");
        assert_eq!(Token::Proj1.to_string(), "π₁");
        assert_eq!(Token::Proj2.to_string(), "π₂");
    }

    #[test]
    fn display_literals() {
        assert_eq!(Token::Ident("foo".into()).to_string(), "foo");
        assert_eq!(Token::Nat(42).to_string(), "42");
        assert_eq!(Token::Int(-7).to_string(), "-7");
        assert_eq!(Token::Rat(1, 3).to_string(), "1/3");
        assert_eq!(Token::StringLit("hello".into()).to_string(), "\"hello\"");
        assert_eq!(Token::Hash("abcd".into()).to_string(), "blake3:abcd");
        assert_eq!(
            Token::ContentRef("blake3:abcd".into()).to_string(),
            "lex://blake3:abcd"
        );
    }

    #[test]
    fn display_punctuation() {
        assert_eq!(Token::Lparen.to_string(), "(");
        assert_eq!(Token::ColonEq.to_string(), ":=");
        assert_eq!(Token::DoubleArrow.to_string(), "⇒");
        assert_eq!(Token::Neq.to_string(), "≠");
        assert_eq!(Token::Le.to_string(), "≤");
        assert_eq!(Token::Ge.to_string(), "≥");
    }

    #[test]
    fn keyword_from_str_roundtrip() {
        assert_eq!(Token::keyword_from_str("lambda"), Some(Token::Lambda));
        assert_eq!(Token::keyword_from_str("λ"), Some(Token::Lambda));
        assert_eq!(Token::keyword_from_str("Pi"), Some(Token::Pi));
        assert_eq!(Token::keyword_from_str("Π"), Some(Token::Pi));
        assert_eq!(Token::keyword_from_str("Time0"), Some(Token::Time0));
        assert_eq!(Token::keyword_from_str("Time₀"), Some(Token::Time0));
        assert_eq!(Token::keyword_from_str("derive1"), Some(Token::Derive1));
        assert_eq!(Token::keyword_from_str("derive₁"), Some(Token::Derive1));
        assert_eq!(Token::keyword_from_str("pi_1"), Some(Token::Proj1));
        assert_eq!(Token::keyword_from_str("π₁"), Some(Token::Proj1));
        assert_eq!(Token::keyword_from_str("pi_2"), Some(Token::Proj2));
        assert_eq!(Token::keyword_from_str("π₂"), Some(Token::Proj2));
        assert_eq!(Token::keyword_from_str("unknown"), None);
        assert_eq!(Token::keyword_from_str("x"), None);
    }

    #[test]
    fn span_basics() {
        let sp = Span::new(10, 20, 3, 5);
        assert_eq!(sp.len(), 10);
        assert!(!sp.is_empty());

        let empty = Span::new(5, 5, 1, 1);
        assert_eq!(empty.len(), 0);
        assert!(empty.is_empty());
    }

    #[test]
    fn token_error_display() {
        let sp = Span::new(0, 1, 1, 1);
        let err = TokenError::UnexpectedChar('€', sp);
        assert!(err.to_string().contains("unexpected character"));
        assert!(err.to_string().contains("1:1"));

        let err2 = TokenError::UnterminatedString(sp);
        assert!(err2.to_string().contains("unterminated string"));
    }

    #[test]
    fn token_clone_eq() {
        let a = Token::Rat(3, 7);
        let b = a.clone();
        assert_eq!(a, b);
    }

    #[test]
    fn eof_is_neither_keyword_nor_punct_nor_literal() {
        assert!(!Token::Eof.is_keyword());
        assert!(!Token::Eof.is_punctuation());
        assert!(!Token::Eof.is_literal());
    }

    #[test]
    fn comment_is_neither_keyword_nor_punct_nor_literal() {
        assert!(!Token::Comment("test".into()).is_keyword());
        assert!(!Token::Comment("test".into()).is_punctuation());
        assert!(!Token::Comment("test".into()).is_literal());
    }
}
