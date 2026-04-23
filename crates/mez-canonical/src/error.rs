//! # Canonicalization Errors
//!
//! Error types returned from Momentum Canonical Form (MCF) operations.

use thiserror::Error;

/// Errors during canonical serialization.
#[derive(Error, Debug)]
pub enum CanonicalizationError {
    /// Float values are not permitted in canonical representations.
    /// Amounts must be strings or integers.
    #[error("float values are not permitted in canonical representations; use string or integer for amounts: {0}")]
    FloatRejected(f64),

    /// JSON serialization failed during canonicalization.
    #[error("serialization failed: {0}")]
    SerializationFailed(#[from] serde_json::Error),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonicalization_error_float_rejected_display() {
        let err = CanonicalizationError::FloatRejected(3.15);
        let msg = format!("{err}");
        assert!(msg.contains("float values are not permitted"));
        assert!(msg.contains("3.15"));
    }

    #[test]
    fn canonicalization_error_is_debug() {
        let err = CanonicalizationError::FloatRejected(0.0);
        assert!(!format!("{err:?}").is_empty());
    }
}
