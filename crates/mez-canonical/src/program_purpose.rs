//! Validated identifiers for program purposes.

use std::{fmt, str::FromStr};

use serde::{Deserialize, Deserializer, Serialize};

/// A case-sensitive program purpose identifier with at most 255 ASCII bytes.
///
/// Each dot-separated segment must match `[A-Za-z_][A-Za-z0-9_]*`.
/// Construction and deserialization preserve the exact accepted bytes.
/// Validation does not establish that a purpose exists or is supported.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
#[serde(transparent)]
pub struct ProgramPurposeTag(String);

impl ProgramPurposeTag {
    /// Maximum length of the complete identifier, including dots, in bytes.
    pub const MAX_BYTES: usize = 255;

    /// Construct a tag without trimming, normalization, or case conversion.
    ///
    /// # Errors
    ///
    /// Returns [`ProgramPurposeTagError`] for an empty, oversized, or malformed identifier.
    pub fn new(value: impl Into<String>) -> Result<Self, ProgramPurposeTagError> {
        let value = value.into();
        if value.is_empty() {
            return Err(ProgramPurposeTagError::Empty);
        }
        if value.len() > Self::MAX_BYTES {
            return Err(ProgramPurposeTagError::TooLong {
                actual: value.len(),
            });
        }

        for (index, segment) in value.split('.').enumerate() {
            let mut bytes = segment.bytes();
            let valid_start = bytes
                .next()
                .is_some_and(|byte| byte.is_ascii_alphabetic() || byte == b'_');
            if !valid_start || !bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_') {
                return Err(ProgramPurposeTagError::InvalidSegment { index });
            }
        }

        Ok(Self(value))
    }

    /// Return the exact validated identifier.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for ProgramPurposeTag {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

impl FromStr for ProgramPurposeTag {
    type Err = ProgramPurposeTagError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        Self::new(value)
    }
}

impl TryFrom<String> for ProgramPurposeTag {
    type Error = ProgramPurposeTagError;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        Self::new(value)
    }
}

impl TryFrom<&str> for ProgramPurposeTag {
    type Error = ProgramPurposeTagError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Self::new(value)
    }
}

impl<'de> Deserialize<'de> for ProgramPurposeTag {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        if deserializer.is_human_readable() {
            deserializer.deserialize_any(ProgramPurposeTagVisitor)
        } else {
            deserializer.deserialize_string(ProgramPurposeTagVisitor)
        }
    }
}

struct ProgramPurposeTagVisitor;

impl<'de> serde::de::Visitor<'de> for ProgramPurposeTagVisitor {
    type Value = ProgramPurposeTag;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a program purpose string")
    }

    fn visit_str<E: serde::de::Error>(self, value: &str) -> Result<Self::Value, E> {
        ProgramPurposeTag::new(value).map_err(E::custom)
    }

    fn visit_string<E: serde::de::Error>(self, value: String) -> Result<Self::Value, E> {
        ProgramPurposeTag::new(value).map_err(E::custom)
    }
}

/// An error from validating a [`ProgramPurposeTag`].
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ProgramPurposeTagError {
    /// The complete identifier is empty.
    #[error("program purpose must not be empty")]
    Empty,
    /// The complete identifier exceeds the byte limit.
    #[error("program purpose exceeds 255 bytes ({actual} bytes)")]
    TooLong {
        /// Length of the supplied identifier in bytes.
        actual: usize,
    },
    /// A segment is empty or does not match the ASCII identifier grammar.
    #[error("program purpose segment {index} must match [A-Za-z_][A-Za-z0-9_]*")]
    InvalidSegment {
        /// Zero-based position of the invalid segment.
        index: usize,
    },
}

#[cfg(feature = "openapi")]
impl<'schema> utoipa::ToSchema<'schema> for ProgramPurposeTag {
    fn schema() -> (
        &'schema str,
        utoipa::openapi::RefOr<utoipa::openapi::schema::Schema>,
    ) {
        use utoipa::openapi::schema::{ObjectBuilder, SchemaType};

        (
            "ProgramPurposeTag",
            ObjectBuilder::new()
                .schema_type(SchemaType::String)
                .min_length(Some(1))
                .max_length(Some(Self::MAX_BYTES))
                // This ECMA-262 end condition also rejects a final newline.
                .pattern(Some(
                    r"^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*(?![\s\S])",
                ))
                .into(),
        )
    }
}
