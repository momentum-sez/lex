//! Versioned authored source with an explicit program purpose.

use mez_canonical::ProgramPurposeTag;
use serde::{Deserialize, Deserializer, Serialize};

use crate::{ast::Term, lexer, parser};

/// Authored Lex source and its required, case-sensitive purpose.
///
/// The wire object requires `version: 1`, `purpose`, and `source`.
/// Human-readable formats require a map. Unknown fields and unsupported versions are rejected.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct AuthoredLexProgramV1 {
    version: u32,
    purpose: ProgramPurposeTag,
    source: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AuthoredLexProgramV1Wire {
    version: u32,
    purpose: ProgramPurposeTag,
    source: String,
}

impl<'de> Deserialize<'de> for AuthoredLexProgramV1 {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let wire = if deserializer.is_human_readable() {
            deserializer.deserialize_map(AuthoredProgramMapVisitor)?
        } else {
            AuthoredLexProgramV1Wire::deserialize(deserializer)?
        };
        Self::try_from(wire).map_err(serde::de::Error::custom)
    }
}

struct AuthoredProgramMapVisitor;

impl<'de> serde::de::Visitor<'de> for AuthoredProgramMapVisitor {
    type Value = AuthoredLexProgramV1Wire;

    fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("an authored Lex program object")
    }

    fn visit_map<A: serde::de::MapAccess<'de>>(self, map: A) -> Result<Self::Value, A::Error> {
        AuthoredLexProgramV1Wire::deserialize(serde::de::value::MapAccessDeserializer::new(map))
    }
}

impl TryFrom<AuthoredLexProgramV1Wire> for AuthoredLexProgramV1 {
    type Error = AuthoredLexProgramError;

    fn try_from(wire: AuthoredLexProgramV1Wire) -> Result<Self, Self::Error> {
        if wire.version != 1 {
            return Err(AuthoredLexProgramError::UnsupportedVersion {
                actual: wire.version,
            });
        }
        Ok(Self::new(wire.purpose, wire.source))
    }
}

impl AuthoredLexProgramV1 {
    /// Record the supplied purpose and exact source without inferring metadata.
    pub fn new(purpose: ProgramPurposeTag, source: impl Into<String>) -> Self {
        Self {
            version: 1,
            purpose,
            source: source.into(),
        }
    }

    /// Return the authored purpose.
    pub fn purpose(&self) -> &ProgramPurposeTag {
        &self.purpose
    }

    /// Return the exact authored source, including comments and whitespace.
    pub fn source(&self) -> &str {
        &self.source
    }

    /// Parse through the existing lexer and parser without establishing admission.
    ///
    /// Multiple top-level forms are rejected instead of discarding additional terms.
    pub fn parse(&self) -> Result<ParsedLexProgramV1, AuthoredLexProgramError> {
        let tokens = lexer::lex(&self.source)?;
        let term = parser::parse_single_term(&tokens)?;
        Ok(ParsedLexProgramV1 {
            authored: self.clone(),
            term,
        })
    }
}

/// A single parsed term together with its unchanged authored envelope.
///
/// This value does not establish elaboration, type checking, admission, or proof discharge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedLexProgramV1 {
    authored: AuthoredLexProgramV1,
    term: Term,
}

impl ParsedLexProgramV1 {
    /// Return the unchanged authored envelope.
    pub fn authored(&self) -> &AuthoredLexProgramV1 {
        &self.authored
    }

    /// Return the authored purpose.
    pub fn purpose(&self) -> &ProgramPurposeTag {
        self.authored.purpose()
    }

    /// Return the exact authored source.
    pub fn source(&self) -> &str {
        self.authored.source()
    }

    /// Return the single term produced by the parser.
    pub fn term(&self) -> &Term {
        &self.term
    }
}

/// Failure to decode or parse a versioned authored program.
#[derive(Debug, thiserror::Error)]
pub enum AuthoredLexProgramError {
    /// The wire version is not supported by this wrapper.
    #[error("unsupported authored Lex program version {actual}, expected 1")]
    UnsupportedVersion {
        /// The supplied version.
        actual: u32,
    },
    /// The source failed lexical analysis.
    #[error(transparent)]
    Lex(#[from] lexer::LexError),
    /// The token stream failed parsing.
    #[error(transparent)]
    Parse(#[from] parser::ParseError),
}
