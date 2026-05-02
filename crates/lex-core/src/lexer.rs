//! Lex lexer.
//!
//! Converts Core Lex source text into a stream of [`Token`]s with precise
//! source spans for diagnostics.

use crate::token::{Span, Spanned, Token, TokenError};

/// Maximum length (in characters) for any single token (identifier, string, or comment).
const MAX_TOKEN_LENGTH: usize = 65536;

/// Maximum nesting depth for block comments `{- {- … -} -}`.
const MAX_COMMENT_DEPTH: usize = 64;

/// Public lexer error alias used by the lexer module API.
pub type LexError = TokenError;

/// Tokenize Lex source text.
pub fn lex(source: &str) -> Result<Vec<Spanned<Token>>, LexError> {
    lex_internal(source, false)
}

fn lex_internal(source: &str, include_comments: bool) -> Result<Vec<Spanned<Token>>, LexError> {
    let mut lexer = Lexer::new(source);
    let mut tokens = Vec::new();

    loop {
        let token = lexer.next_token(include_comments)?;
        let is_eof = matches!(token.0, Token::Eof);
        tokens.push(token);
        if is_eof {
            break;
        }
    }

    Ok(tokens)
}

struct Lexer<'a> {
    source: &'a str,
    pos: usize,
    line: u32,
    col: u32,
}

impl<'a> Lexer<'a> {
    fn new(source: &'a str) -> Self {
        Self {
            source,
            pos: 0,
            line: 1,
            col: 1,
        }
    }

    fn next_token(&mut self, include_comments: bool) -> Result<Spanned<Token>, LexError> {
        if include_comments {
            self.skip_whitespace();
            if self.starts_with("--") {
                return self.lex_line_comment();
            }
            if self.starts_with("{-") {
                return self.lex_block_comment();
            }
        } else {
            self.skip_whitespace_and_comments()?;
        }

        if self.is_eof() {
            let span = Span::new(self.pos, self.pos, self.line, self.col);
            return Ok((Token::Eof, span));
        }

        let start = self.pos;
        let line = self.line;
        let col = self.col;
        let ch = self
            .peek_char()
            .ok_or_else(|| LexError::InternalError("lexer position must be valid before tokenization".into()))?;

        if self.starts_with("lex://blake3:") {
            return self.lex_content_ref(start, line, col);
        }
        if self.starts_with("blake3:") {
            return self.lex_hash(start, line, col);
        }
        if ch == '"' {
            return self.lex_string(start, line, col);
        }
        if ch == 'ℓ' {
            return self.lex_level_var(start, line, col);
        }
        if ch == '-'
            && self
                .peek_next_char()
                .is_some_and(|next| next.is_ascii_digit())
        {
            return self.lex_number(start, line, col);
        }
        if ch.is_ascii_digit() {
            return self.lex_number(start, line, col);
        }
        if self.starts_with("sanctions-dominance")
            && self.has_identifier_boundary_after("sanctions-dominance")
        {
            return self.lex_exact_token(
                "sanctions-dominance",
                Token::SanctionsDominance,
                start,
                line,
                col,
            );
        }
        if self.starts_with("meta-tribunal")
            && self.has_identifier_boundary_after("meta-tribunal")
        {
            return self.lex_reserved_identifier("meta-tribunal", start, line, col);
        }
        if is_identifier_start(ch) {
            return self.lex_identifier_or_keyword(start, line, col);
        }

        let token = match ch {
            '(' => self.single_char_token(Token::Lparen, start, line, col),
            ')' => self.single_char_token(Token::Rparen, start, line, col),
            '[' => self.single_char_token(Token::Lbracket, start, line, col),
            ']' => self.single_char_token(Token::Rbracket, start, line, col),
            '{' => self.single_char_token(Token::Lbrace, start, line, col),
            '}' => self.single_char_token(Token::Rbrace, start, line, col),
            '⟨' => self.single_char_token(Token::Langle, start, line, col),
            '⟩' => self.single_char_token(Token::Rangle, start, line, col),
            '.' => self.single_char_token(Token::Dot, start, line, col),
            ',' => self.single_char_token(Token::Comma, start, line, col),
            ';' => self.single_char_token(Token::Semicolon, start, line, col),
            '_' => self.single_char_token(Token::Underscore, start, line, col),
            '?' => self.single_char_token(Token::Question, start, line, col),
            '@' => self.single_char_token(Token::At, start, line, col),
            '+' => self.single_char_token(Token::Plus, start, line, col),
            '/' => self.single_char_token(Token::Slash, start, line, col),
            '→' => self.single_char_token(Token::Arrow, start, line, col),
            '×' => self.single_char_token(Token::Times, start, line, col),
            '⇒' => self.single_char_token(Token::DoubleArrow, start, line, col),
            '≠' => self.single_char_token(Token::Neq, start, line, col),
            '≤' => self.single_char_token(Token::Le, start, line, col),
            '≥' => self.single_char_token(Token::Ge, start, line, col),
            '∀' => self.single_char_token(Token::Pi, start, line, col),
            '∃' => self.single_char_token(Token::Sigma, start, line, col),
            '¬' => self.single_char_token(Token::Bang, start, line, col),
            '≡' => self.single_char_token(Token::Eq, start, line, col),
            '←' => self.single_char_token(Token::Arrow, start, line, col),
            '⊤' | '⊥' | '∅' | '◇' | '□' | '▷' | '⊸' | '⊢' | '∧' | '∨' => {
                self.bump_char();
                let span = self.span_from(start, line, col);
                (Token::Ident(ch.to_string()), span)
            }
            ':' => {
                if self.starts_with(":=") {
                    self.consume_exact(":=")?;
                    let span = self.span_from(start, line, col);
                    (Token::ColonEq, span)
                } else {
                    self.single_char_token(Token::Colon, start, line, col)
                }
            }
            '!' => {
                if self.starts_with("!=") {
                    self.consume_exact("!=")?;
                    let span = self.span_from(start, line, col);
                    (Token::Neq, span)
                } else {
                    self.single_char_token(Token::Bang, start, line, col)
                }
            }
            '=' => {
                if self.starts_with("=>") {
                    self.consume_exact("=>")?;
                    let span = self.span_from(start, line, col);
                    (Token::DoubleArrow, span)
                } else {
                    self.single_char_token(Token::Eq, start, line, col)
                }
            }
            '<' => {
                if self.starts_with("<=") {
                    self.consume_exact("<=")?;
                    let span = self.span_from(start, line, col);
                    (Token::Le, span)
                } else if self.starts_with("<-") {
                    self.consume_exact("<-")?;
                    let span = self.span_from(start, line, col);
                    (Token::Arrow, span)
                } else if self.peek_next_char() == Some('>') {
                    self.single_char_token(Token::Langle, start, line, col)
                } else {
                    self.single_char_token(Token::Lt, start, line, col)
                }
            }
            '>' => {
                if self.starts_with(">=") {
                    self.consume_exact(">=")?;
                    let span = self.span_from(start, line, col);
                    (Token::Ge, span)
                } else if self.previous_char() == Some('<') {
                    self.single_char_token(Token::Rangle, start, line, col)
                } else {
                    self.single_char_token(Token::Gt, start, line, col)
                }
            }
            '*' => {
                let token = if self.previous_char().is_some_and(char::is_whitespace)
                    || self.peek_next_char().is_some_and(char::is_whitespace)
                {
                    Token::Times
                } else {
                    Token::Star
                };
                self.single_char_token(token, start, line, col)
            }
            '|' => {
                if self.starts_with("||") {
                    self.consume_exact("||")?;
                    let span = self.span_from(start, line, col);
                    (Token::Ident("||".to_owned()), span)
                } else if self.starts_with("|-") {
                    self.consume_exact("|-")?;
                    let span = self.span_from(start, line, col);
                    (Token::Ident("|-".to_owned()), span)
                } else {
                    self.single_char_token(Token::Pipe, start, line, col)
                }
            }
            '&' => {
                if self.starts_with("&&") {
                    self.consume_exact("&&")?;
                    let span = self.span_from(start, line, col);
                    (Token::Ident("&&".to_owned()), span)
                } else {
                    return Err(TokenError::UnexpectedChar(
                        ch,
                        Span::new(start, start + ch.len_utf8(), line, col),
                    ));
                }
            }
            '-' => {
                if self.starts_with("->") {
                    self.consume_exact("->")?;
                    let span = self.span_from(start, line, col);
                    (Token::Arrow, span)
                } else {
                    return Err(TokenError::UnexpectedChar(
                        ch,
                        Span::new(start, start + ch.len_utf8(), line, col),
                    ));
                }
            }
            _ => {
                return Err(TokenError::UnexpectedChar(
                    ch,
                    Span::new(start, start + ch.len_utf8(), line, col),
                ));
            }
        };

        Ok(token)
    }

    fn lex_identifier_or_keyword(
        &mut self,
        start: usize,
        line: u32,
        col: u32,
    ) -> Result<Spanned<Token>, LexError> {
        let mut text = String::new();
        text.push(
            self.bump_char()
                .ok_or_else(|| LexError::InternalError("identifier lexing requires an initial character".into()))?,
        );
        while let Some(ch) = self.peek_char() {
            if is_identifier_continue(ch) {
                if ch == '_' && should_split_sort_level_suffix(&text, self.peek_next_char()) {
                    break;
                }
                text.push(
                    self.bump_char()
                        .ok_or_else(|| LexError::InternalError("identifier continuation must exist once peeked".into()))?,
                );
                if text.len() > MAX_TOKEN_LENGTH {
                    return Err(TokenError::TokenTooLong(
                        "identifier".to_owned(),
                        self.span_from(start, line, col),
                    ));
                }
            } else {
                break;
            }
        }

        let mut qualified = false;
        while self.peek_char() == Some('.')
            && self
                .peek_char_after_current()
                .is_some_and(is_identifier_start)
        {
            qualified = true;
            text.push(
                self.bump_char()
                    .ok_or_else(|| LexError::InternalError("qualified identifier dot must exist once peeked".into()))?,
            );
            text.push(
                self.bump_char()
                    .ok_or_else(|| LexError::InternalError("qualified identifier segment must exist once peeked".into()))?,
            );
            while let Some(ch) = self.peek_char() {
                if is_identifier_continue(ch) {
                    text.push(
                        self.bump_char()
                            .ok_or_else(|| LexError::InternalError("qualified identifier continuation must exist once peeked".into()))?,
                    );
                    if text.len() > MAX_TOKEN_LENGTH {
                        return Err(TokenError::TokenTooLong(
                            "identifier".to_owned(),
                            self.span_from(start, line, col),
                        ));
                    }
                } else {
                    break;
                }
            }
        }

        let token = if qualified {
            Token::Ident(text)
        } else {
            keyword_or_ident(text)
        };

        let span = self.span_from(start, line, col);
        Ok((token, span))
    }

    fn lex_exact_token(
        &mut self,
        text: &str,
        token: Token,
        start: usize,
        line: u32,
        col: u32,
    ) -> Result<Spanned<Token>, LexError> {
        self.consume_exact(text)?;
        let span = self.span_from(start, line, col);
        Ok((token, span))
    }

    fn lex_reserved_identifier(
        &mut self,
        prefix: &str,
        start: usize,
        line: u32,
        col: u32,
    ) -> Result<Spanned<Token>, LexError> {
        let mut text = String::new();
        self.consume_exact(prefix)?;
        text.push_str(prefix);

        while self.peek_char() == Some('.')
            && self
                .peek_char_after_current()
                .is_some_and(is_identifier_start)
        {
            text.push(
                self.bump_char()
                    .ok_or_else(|| LexError::InternalError("qualified identifier dot must exist once peeked".into()))?,
            );
            text.push(
                self.bump_char()
                    .ok_or_else(|| LexError::InternalError("qualified identifier segment must exist once peeked".into()))?,
            );
            while let Some(ch) = self.peek_char() {
                if is_identifier_continue(ch) {
                    text.push(
                        self.bump_char()
                            .ok_or_else(|| LexError::InternalError("qualified identifier continuation must exist once peeked".into()))?,
                    );
                    if text.len() > MAX_TOKEN_LENGTH {
                        return Err(TokenError::TokenTooLong(
                            "identifier".to_owned(),
                            self.span_from(start, line, col),
                        ));
                    }
                } else {
                    break;
                }
            }
        }

        let span = self.span_from(start, line, col);
        Ok((Token::Ident(text), span))
    }

    fn lex_number(
        &mut self,
        start: usize,
        line: u32,
        col: u32,
    ) -> Result<Spanned<Token>, LexError> {
        let mut text = String::new();
        let negative = self.peek_char() == Some('-');
        if negative {
            text.push(
                self.bump_char()
                    .ok_or_else(|| LexError::InternalError("negative number lexing requires a minus sign".into()))?,
            );
        }

        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_digit() {
                text.push(
                    self.bump_char()
                        .ok_or_else(|| LexError::InternalError("numeric continuation must exist once peeked".into()))?,
                );
            } else {
                break;
            }
        }

        if self.peek_char() == Some('/')
            && self
                .peek_char_after_current()
                .is_some_and(|ch| ch.is_ascii_digit())
        {
            text.push(
                self.bump_char()
                    .ok_or_else(|| LexError::InternalError("rational literal slash must exist once peeked".into()))?,
            );
            let mut denom = String::new();
            while let Some(ch) = self.peek_char() {
                if ch.is_ascii_digit() {
                    denom.push(
                        self.bump_char()
                            .ok_or_else(|| LexError::InternalError("denominator continuation must exist once peeked".into()))?,
                    );
                } else {
                    break;
                }
            }

            let numer_text = &text[..text.len() - 1];
            let numer = numer_text.parse::<i64>().map_err(|_| {
                TokenError::InvalidNumber(text.clone(), self.span_from(start, line, col))
            })?;
            let denom_value = denom.parse::<u64>().map_err(|_| {
                TokenError::InvalidNumber(text.clone(), self.span_from(start, line, col))
            })?;
            if denom_value == 0 {
                return Err(TokenError::InvalidNumber(
                    format!("{numer_text}/{}", denom),
                    self.span_from(start, line, col),
                ));
            }

            let mut literal = numer_text.to_owned();
            literal.push('/');
            literal.push_str(&denom);
            let span = self.span_from(start, line, col);
            return Ok((Token::Rat(numer, denom_value), span));
        }

        let span = self.span_from(start, line, col);
        if negative {
            let value = text
                .parse::<i64>()
                .map_err(|_| TokenError::InvalidNumber(text, span))?;
            Ok((Token::Int(value), span))
        } else {
            let value = text
                .parse::<u64>()
                .map_err(|_| TokenError::InvalidNumber(text, span))?;
            Ok((Token::Nat(value), span))
        }
    }

    fn lex_string(
        &mut self,
        start: usize,
        line: u32,
        col: u32,
    ) -> Result<Spanned<Token>, LexError> {
        self.bump_char();
        let mut value = String::new();

        while let Some(ch) = self.peek_char() {
            match ch {
                '"' => {
                    self.bump_char();
                    let span = self.span_from(start, line, col);
                    return Ok((Token::StringLit(value), span));
                }
                '\\' => {
                    let escape_start = self.pos;
                    let escape_line = self.line;
                    let escape_col = self.col;
                    self.bump_char();
                    let escaped = match self.peek_char() {
                        Some('\\') => '\\',
                        Some('"') => '"',
                        Some('n') => '\n',
                        Some('t') => '\t',
                        Some('r') => '\r',
                        Some('0') => '\0',
                        Some('\'') => '\'',
                        Some(other) => {
                            return Err(TokenError::InvalidEscape(
                                other,
                                Span::new(
                                    escape_start,
                                    escape_start + other.len_utf8() + 1,
                                    escape_line,
                                    escape_col,
                                ),
                            ));
                        }
                        None => {
                            return Err(TokenError::UnterminatedString(Span::new(
                                start, self.pos, line, col,
                            )));
                        }
                    };
                    self.bump_char();
                    value.push(escaped);
                }
                _ => {
                    value.push(
                        self.bump_char()
                            .ok_or_else(|| LexError::InternalError("string character must exist once peeked".into()))?,
                    );
                }
            }
            if value.len() > MAX_TOKEN_LENGTH {
                return Err(TokenError::TokenTooLong(
                    "string literal".to_owned(),
                    self.span_from(start, line, col),
                ));
            }
        }

        Err(TokenError::UnterminatedString(Span::new(
            start, self.pos, line, col,
        )))
    }

    fn lex_hash(&mut self, start: usize, line: u32, col: u32) -> Result<Spanned<Token>, LexError> {
        self.lex_prefixed_hash(start, line, col, false)
    }

    fn lex_content_ref(
        &mut self,
        start: usize,
        line: u32,
        col: u32,
    ) -> Result<Spanned<Token>, LexError> {
        self.lex_prefixed_hash(start, line, col, true)
    }

    fn lex_prefixed_hash(
        &mut self,
        start: usize,
        line: u32,
        col: u32,
        content_ref: bool,
    ) -> Result<Spanned<Token>, LexError> {
        let prefix = if content_ref {
            "lex://blake3:"
        } else {
            "blake3:"
        };
        self.consume_exact(prefix)?;
        let mut body = String::new();
        while let Some(ch) = self.peek_char() {
            if is_hash_digit(ch) && body.len() < 64 {
                body.push(
                    self.bump_char()
                        .ok_or_else(|| LexError::InternalError("hash continuation must exist once peeked".into()))?,
                );
            } else {
                break;
            }
        }

        let has_invalid_trailer = self
            .peek_char()
            .is_some_and(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '\'');
        if body.len() != 64 || has_invalid_trailer {
            while self
                .peek_char()
                .is_some_and(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '\'')
            {
                body.push(
                    self.bump_char()
                        .ok_or_else(|| LexError::InternalError("malformed hash trailer must exist once peeked".into()))?,
                );
            }
            let span = self.span_from(start, line, col);
            let literal = if content_ref {
                format!("lex://blake3:{body}")
            } else {
                format!("blake3:{body}")
            };
            return Err(if content_ref {
                TokenError::InvalidContentRef(literal, span)
            } else {
                TokenError::InvalidHash(literal, span)
            });
        }

        let span = self.span_from(start, line, col);
        if content_ref {
            Ok((Token::ContentRef(format!("blake3:{body}")), span))
        } else {
            Ok((Token::Hash(body), span))
        }
    }

    fn lex_level_var(&mut self, start: usize, line: u32, col: u32) -> Result<Spanned<Token>, LexError> {
        let mut text = String::new();
        text.push(
            self.bump_char()
                .ok_or_else(|| LexError::InternalError("level variable lexing requires the leading ℓ".into()))?,
        );
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_digit() {
                text.push(
                    self.bump_char()
                        .ok_or_else(|| LexError::InternalError("level variable continuation must exist once peeked".into()))?,
                );
            } else {
                break;
            }
        }
        let span = self.span_from(start, line, col);
        Ok((Token::LevelVar(text), span))
    }

    fn lex_line_comment(&mut self) -> Result<Spanned<Token>, LexError> {
        let start = self.pos;
        let line = self.line;
        let col = self.col;
        self.consume_exact("--")?;
        let mut text = String::new();
        while let Some(ch) = self.peek_char() {
            if ch == '\n' {
                break;
            }
            text.push(
                self.bump_char()
                    .ok_or_else(|| LexError::InternalError("line comment continuation must exist once peeked".into()))?,
            );
            if text.len() > MAX_TOKEN_LENGTH {
                return Err(TokenError::TokenTooLong(
                    "line comment".to_owned(),
                    self.span_from(start, line, col),
                ));
            }
        }
        let span = self.span_from(start, line, col);
        Ok((Token::Comment(text), span))
    }

    fn lex_block_comment(&mut self) -> Result<Spanned<Token>, LexError> {
        let start = self.pos;
        let line = self.line;
        let col = self.col;
        self.consume_exact("{-")?;
        let mut text = String::new();
        let mut depth = 1usize;

        while !self.is_eof() {
            if self.starts_with("{-") {
                depth += 1;
                if depth > MAX_COMMENT_DEPTH {
                    return Err(TokenError::CommentNestingTooDeep(Span::new(
                        start, self.pos, line, col,
                    )));
                }
                self.consume_exact("{-")?;
                if depth > 1 {
                    text.push_str("{-");
                }
                continue;
            }
            if self.starts_with("-}") {
                depth -= 1;
                self.consume_exact("-}")?;
                if depth == 0 {
                    let span = self.span_from(start, line, col);
                    return Ok((Token::Comment(text), span));
                }
                text.push_str("-}");
                continue;
            }
            text.push(
                self.bump_char()
                    .ok_or_else(|| LexError::InternalError("block comment continuation must exist before EOF".into()))?,
            );
            if text.len() > MAX_TOKEN_LENGTH {
                return Err(TokenError::TokenTooLong(
                    "block comment".to_owned(),
                    self.span_from(start, line, col),
                ));
            }
        }

        Err(TokenError::UnterminatedBlockComment(Span::new(
            start, self.pos, line, col,
        )))
    }

    fn skip_whitespace_and_comments(&mut self) -> Result<(), LexError> {
        loop {
            self.skip_whitespace();
            if self.starts_with("--") {
                self.lex_line_comment()?;
                continue;
            }
            if self.starts_with("{-") {
                self.lex_block_comment()?;
                continue;
            }
            break;
        }
        Ok(())
    }

    fn skip_whitespace(&mut self) {
        while self.peek_char().is_some_and(char::is_whitespace) {
            self.bump_char();
        }
    }

    fn single_char_token(
        &mut self,
        token: Token,
        start: usize,
        line: u32,
        col: u32,
    ) -> Spanned<Token> {
        self.bump_char();
        let span = self.span_from(start, line, col);
        (token, span)
    }

    fn span_from(&self, start: usize, line: u32, col: u32) -> Span {
        Span::new(start, self.pos, line, col)
    }

    fn consume_exact(&mut self, text: &str) -> Result<(), LexError> {
        for expected in text.chars() {
            let ch = self
                .bump_char()
                .ok_or_else(|| LexError::InternalError(format!("consume_exact: expected '{}' but reached end of input", expected)))?;
            debug_assert_eq!(ch, expected);
        }
        Ok(())
    }

    fn starts_with(&self, text: &str) -> bool {
        self.source[self.pos..].starts_with(text)
    }

    fn has_identifier_boundary_after(&self, text: &str) -> bool {
        match self.source[self.pos + text.len()..].chars().next() {
            Some(ch) => !is_identifier_continue(ch),
            None => true,
        }
    }

    fn peek_char(&self) -> Option<char> {
        self.source[self.pos..].chars().next()
    }

    fn peek_next_char(&self) -> Option<char> {
        self.source[self.pos..].chars().nth(1)
    }

    fn peek_char_after_current(&self) -> Option<char> {
        let current = self.peek_char()?;
        self.source[self.pos + current.len_utf8()..].chars().next()
    }

    fn previous_char(&self) -> Option<char> {
        self.source[..self.pos].chars().next_back()
    }

    fn bump_char(&mut self) -> Option<char> {
        let ch = self.peek_char()?;
        self.pos += ch.len_utf8();
        if ch == '\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        Some(ch)
    }

    fn is_eof(&self) -> bool {
        self.pos >= self.source.len()
    }
}

fn keyword_or_ident(text: String) -> Token {
    match text.as_str() {
        "forall" => Token::Pi,
        "exists" => Token::Sigma,
        _ => Token::keyword_from_str(&text).unwrap_or(Token::Ident(text)),
    }
}

fn should_split_sort_level_suffix(prefix: &str, next: Option<char>) -> bool {
    matches!(prefix, "Type" | "Rule") && next.is_some_and(|ch| ch.is_ascii_digit())
}

fn is_identifier_start(ch: char) -> bool {
    ch.is_alphabetic()
}

fn is_identifier_continue(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_' || ch == '\'' || is_subscript_digit(ch)
}

fn is_subscript_digit(ch: char) -> bool {
    matches!(
        ch,
        '₀' | '₁' | '₂' | '₃' | '₄' | '₅' | '₆' | '₇' | '₈' | '₉'
    )
}

fn is_hash_digit(ch: char) -> bool {
    matches!(ch, '0'..='9' | 'a'..='f')
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokens(source: &str) -> Vec<Token> {
        lex(source)
            .expect("lexing should succeed")
            .into_iter()
            .map(|(token, _)| token)
            .collect()
    }

    #[test]
    fn recognizes_textual_keywords() {
        assert_eq!(
            tokens(
                "lambda let in match return with fix defeasible unless priority end Type Prop Rule Time0 Time1 asof0 asof1 lift0 derive1 pi_1 pi_2 coerce fill"
            ),
            vec![
                Token::Lambda,
                Token::Let,
                Token::In,
                Token::Match,
                Token::Return,
                Token::With,
                Token::Fix,
                Token::Defeasible,
                Token::Unless,
                Token::Priority,
                Token::End,
                Token::Type,
                Token::Prop,
                Token::Rule,
                Token::Time0,
                Token::Time1,
                Token::AsOf0,
                Token::AsOf1,
                Token::Lift0,
                Token::Derive1,
                Token::Proj1,
                Token::Proj2,
                Token::Coerce,
                Token::Fill,
                Token::Eof,
            ]
        );
    }

    #[test]
    fn recognizes_unicode_keywords() {
        assert_eq!(
            tokens("λ Π Σ Time₀ Time₁ asof₀ asof₁ lift₀ derive₁ π₁ π₂"),
            vec![
                Token::Lambda,
                Token::Pi,
                Token::Sigma,
                Token::Time0,
                Token::Time1,
                Token::AsOf0,
                Token::AsOf1,
                Token::Lift0,
                Token::Derive1,
                Token::Proj1,
                Token::Proj2,
                Token::Eof,
            ]
        );
    }

    #[test]
    fn recognizes_sort_level_suffixes() {
        assert_eq!(
            tokens("Type_42 Rule_3"),
            vec![
                Token::Type,
                Token::Underscore,
                Token::Nat(42),
                Token::Rule,
                Token::Underscore,
                Token::Nat(3),
                Token::Eof,
            ]
        );
    }

    #[test]
    fn recognizes_identifiers_with_primes() {
        assert_eq!(
            tokens("x' y'' z_prime"),
            vec![
                Token::Ident("x'".to_owned()),
                Token::Ident("y''".to_owned()),
                Token::Ident("z_prime".to_owned()),
                Token::Eof,
            ]
        );
    }

    #[test]
    fn recognizes_qualified_identifiers() {
        assert_eq!(
            tokens("Foo.Bar.baz meta.tribunal.sanctions"),
            vec![
                Token::Ident("Foo.Bar.baz".to_owned()),
                Token::Ident("meta.tribunal.sanctions".to_owned()),
                Token::Eof,
            ]
        );
    }

    #[test]
    fn recognizes_numeric_literals() {
        assert_eq!(
            tokens("42 -7 3/4 -5/6"),
            vec![
                Token::Nat(42),
                Token::Int(-7),
                Token::Rat(3, 4),
                Token::Rat(-5, 6),
                Token::Eof,
            ]
        );
    }

    #[test]
    fn recognizes_string_literals_with_escapes() {
        assert_eq!(
            tokens("\"hello\\nworld\\t\\\"quote\\\"\\\\\""),
            vec![
                Token::StringLit("hello\nworld\t\"quote\"\\".to_owned()),
                Token::Eof
            ]
        );
    }

    #[test]
    fn recognizes_hash_literals() {
        let hex = "abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789";
        assert_eq!(
            tokens(&format!("blake3:{hex}")),
            vec![Token::Hash(hex.to_owned()), Token::Eof]
        );
    }

    #[test]
    fn recognizes_content_references() {
        let hex = "abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789";
        assert_eq!(
            tokens(&format!("lex://blake3:{hex}")),
            vec![Token::ContentRef(format!("blake3:{hex}")), Token::Eof]
        );
    }

    #[test]
    fn recognizes_level_variables() {
        assert_eq!(
            tokens("ℓ0 ℓ42 ℓ"),
            vec![
                Token::LevelVar("ℓ0".to_owned()),
                Token::LevelVar("ℓ42".to_owned()),
                Token::LevelVar("ℓ".to_owned()),
                Token::Eof,
            ]
        );
    }

    #[test]
    fn recognizes_unicode_operators() {
        assert_eq!(
            tokens("→ × ⟨ ⟩ ⇒ ≡ ≤ ≥ ≠"),
            vec![
                Token::Arrow,
                Token::Times,
                Token::Langle,
                Token::Rangle,
                Token::DoubleArrow,
                Token::Eq,
                Token::Le,
                Token::Ge,
                Token::Neq,
                Token::Eof,
            ]
        );
    }

    #[test]
    fn recognizes_ascii_operator_alternatives() {
        assert_eq!(
            tokens("A * B -> C => D <= E >= F != G <- H <>"),
            vec![
                Token::Ident("A".to_owned()),
                Token::Times,
                Token::Ident("B".to_owned()),
                Token::Arrow,
                Token::Ident("C".to_owned()),
                Token::DoubleArrow,
                Token::Ident("D".to_owned()),
                Token::Le,
                Token::Ident("E".to_owned()),
                Token::Ge,
                Token::Ident("F".to_owned()),
                Token::Neq,
                Token::Ident("G".to_owned()),
                Token::Arrow,
                Token::Ident("H".to_owned()),
                Token::Langle,
                Token::Rangle,
                Token::Eof,
            ]
        );
    }

    #[test]
    fn skips_line_and_block_comments() {
        assert_eq!(
            tokens("let -- line comment\n x {- block comment -} in"),
            vec![
                Token::Let,
                Token::Ident("x".to_owned()),
                Token::In,
                Token::Eof,
            ]
        );
    }

    #[test]
    fn skips_nested_block_comments() {
        assert_eq!(
            tokens("let {- outer {- inner -} still comment -} x"),
            vec![Token::Let, Token::Ident("x".to_owned()), Token::Eof]
        );
    }

    #[test]
    fn tracks_spans_with_line_and_column() {
        let tokens = lex("let\n  x := 42").expect("lexing should succeed");
        assert_eq!(tokens[0], (Token::Let, Span::new(0, 3, 1, 1)));
        assert_eq!(
            tokens[1],
            (Token::Ident("x".to_owned()), Span::new(6, 7, 2, 3))
        );
        assert_eq!(tokens[2], (Token::ColonEq, Span::new(8, 10, 2, 5)));
        assert_eq!(tokens[3], (Token::Nat(42), Span::new(11, 13, 2, 8)));
        assert_eq!(tokens[4], (Token::Eof, Span::new(13, 13, 2, 10)));
    }

    #[test]
    fn errors_on_unterminated_string() {
        let err = lex("\"unterminated").expect_err("lexer should reject unterminated strings");
        assert!(matches!(err, TokenError::UnterminatedString(_)));
    }

    #[test]
    fn errors_on_unterminated_block_comment() {
        let err = lex("{- unterminated").expect_err("lexer should reject unterminated comments");
        assert!(matches!(err, TokenError::UnterminatedBlockComment(_)));
    }

    #[test]
    fn errors_on_invalid_character() {
        let err = lex("€").expect_err("lexer should reject invalid characters");
        assert!(matches!(err, TokenError::UnexpectedChar('€', _)));
    }

    #[test]
    fn tokenizes_mixed_expression() {
        assert_eq!(
            tokens("let x : Nat = 42 in x"),
            vec![
                Token::Let,
                Token::Ident("x".to_owned()),
                Token::Colon,
                Token::Ident("Nat".to_owned()),
                Token::Eq,
                Token::Nat(42),
                Token::In,
                Token::Ident("x".to_owned()),
                Token::Eof,
            ]
        );
    }

    #[test]
    fn supports_comment_tokens_in_internal_mode() {
        let tokens = lex_internal("-- hello", true).expect("comment lexing should succeed");
        assert_eq!(
            tokens,
            vec![
                (Token::Comment(" hello".to_owned()), Span::new(0, 8, 1, 1),),
                (Token::Eof, Span::new(8, 8, 1, 9)),
            ]
        );
    }

    #[test]
    fn recognizes_keyword_aliases() {
        assert_eq!(
            tokens("forall exists"),
            vec![Token::Pi, Token::Sigma, Token::Eof]
        );
    }

    #[test]
    fn recognizes_operator_fallback_aliases() {
        assert_eq!(
            tokens("∀ ∃ ¬ ← && || ⊤"),
            vec![
                Token::Pi,
                Token::Sigma,
                Token::Bang,
                Token::Arrow,
                Token::Ident("&&".to_owned()),
                Token::Ident("||".to_owned()),
                Token::Ident("⊤".to_owned()),
                Token::Eof,
            ]
        );
    }

    #[test]
    fn errors_on_invalid_hash_or_content_ref() {
        let err = lex("blake3:abc").expect_err("short hashes must fail");
        assert!(matches!(err, TokenError::InvalidHash(_, _)));

        let err = lex("lex://blake3:abc").expect_err("short content refs must fail");
        assert!(matches!(err, TokenError::InvalidContentRef(_, _)));
    }
}
