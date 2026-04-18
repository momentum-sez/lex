//! # Content-Addressed Digests
//!
//! Defines [`ContentDigest`] and [`DigestAlgorithm`] for the content-addressed
//! storage system.
//!
//! ## Security Invariant
//!
//! [`ContentDigest`] can only be computed via [`sha256_digest`], which accepts
//! only [`CanonicalBytes`](crate::canonical::CanonicalBytes). Every digest
//! carried through Lex was produced from properly canonicalized data.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::canonical::CanonicalBytes;

/// The hash algorithm used to compute a content-addressed digest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DigestAlgorithm {
    /// SHA-256 — standard content addressing.
    Sha256,
    /// Poseidon2 — ZK-friendly arithmetic-circuit-native hash (tag only; the
    /// minimal build does not implement Poseidon2 computation, but the tag is
    /// kept for byte-compatibility with kernel-produced digests).
    Poseidon2,
}

impl std::fmt::Display for DigestAlgorithm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sha256 => write!(f, "sha256"),
            Self::Poseidon2 => write!(f, "poseidon2"),
        }
    }
}

/// A content-addressed digest with its algorithm tag.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ContentDigest {
    algorithm: DigestAlgorithm,
    bytes: [u8; 32],
}

impl ContentDigest {
    /// Create the zero digest (all-zero bytes, SHA-256 algorithm).
    pub fn zero() -> Self {
        Self {
            algorithm: DigestAlgorithm::Sha256,
            bytes: [0u8; 32],
        }
    }

    /// Access the digest algorithm.
    pub fn algorithm(&self) -> DigestAlgorithm {
        self.algorithm
    }

    /// Access the raw 32-byte digest value.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.bytes
    }

    /// Return the digest as a lowercase hex string.
    pub fn to_hex(&self) -> String {
        self.bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Reconstruct a SHA-256 `ContentDigest` from a 64-character hex string.
    ///
    /// Returns an error if the string is not exactly 64 hex characters.
    pub fn from_hex(hex: &str) -> Result<Self, HexDigestError> {
        if hex.len() != 64 {
            return Err(HexDigestError::InvalidLength {
                expected: 64,
                actual: hex.len(),
            });
        }
        let mut bytes = [0u8; 32];
        for i in 0..32 {
            bytes[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16)
                .map_err(|_| HexDigestError::InvalidHexByte { position: i * 2 })?;
        }
        Ok(Self {
            algorithm: DigestAlgorithm::Sha256,
            bytes,
        })
    }
}

impl std::fmt::Display for ContentDigest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.algorithm, self.to_hex())
    }
}

/// Error returned from [`ContentDigest::from_hex`].
#[derive(Debug, thiserror::Error)]
pub enum HexDigestError {
    /// The hex string length does not match the expected count.
    #[error("expected {expected} hex chars for SHA-256 digest, got {actual}")]
    InvalidLength {
        /// Required length (always 64 for SHA-256).
        expected: usize,
        /// Provided length.
        actual: usize,
    },

    /// A character at `position` is not a valid hex digit.
    #[error("invalid hex at position {position}")]
    InvalidHexByte {
        /// Byte offset inside the hex string.
        position: usize,
    },
}

/// Compute a SHA-256 content digest from canonical bytes.
///
/// The type signature `&CanonicalBytes` (not `&[u8]`) guarantees that the
/// input has passed through `CanonicalBytes::new`, which applies float
/// rejection, datetime normalization, and key sorting.
///
/// # Example
///
/// ```
/// use mez_core_min::canonical::CanonicalBytes;
/// use mez_core_min::digest::{sha256_digest, DigestAlgorithm};
/// use serde_json::json;
///
/// let canonical = CanonicalBytes::new(&json!({"key": "value"})).unwrap();
/// let digest = sha256_digest(&canonical);
/// assert_eq!(digest.algorithm(), DigestAlgorithm::Sha256);
/// assert_eq!(digest.to_hex().len(), 64);
/// ```
pub fn sha256_digest(canonical: &CanonicalBytes) -> ContentDigest {
    let mut hasher = Sha256::new();
    hasher.update(canonical.as_bytes());
    let result = hasher.finalize();
    ContentDigest {
        algorithm: DigestAlgorithm::Sha256,
        bytes: result.into(),
    }
}

/// Compute a SHA-256 hex digest of raw bytes.
///
/// For structured domain objects, prefer [`sha256_digest`] with
/// [`CanonicalBytes`](crate::canonical::CanonicalBytes).
pub fn sha256_raw(data: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(data);
    let out = hasher.finalize();
    out.iter().map(|b| format!("{b:02x}")).collect()
}

/// Compute SHA-256 of raw bytes, returning the 32-byte digest.
///
/// Single-shot convenience for binary hash operations that need raw
/// `[u8; 32]` (Merkle tree concatenation). For hex output, use
/// [`sha256_raw`]. For canonical JSON digests, use [`sha256_digest`].
pub fn sha256_bytes(data: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(data);
    hasher.finalize().into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn sha256_digest_produces_64_hex_chars() {
        let canonical = CanonicalBytes::new(&json!({"a": 1})).unwrap();
        let digest = sha256_digest(&canonical);
        assert_eq!(digest.to_hex().len(), 64);
        assert!(digest.to_hex().chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn sha256_digest_is_deterministic() {
        let canonical = CanonicalBytes::new(&json!({"key": "value", "n": 42})).unwrap();
        let d1 = sha256_digest(&canonical);
        let d2 = sha256_digest(&canonical);
        assert_eq!(d1, d2);
    }

    #[test]
    fn different_inputs_produce_different_digests() {
        let c1 = CanonicalBytes::new(&json!({"a": 1})).unwrap();
        let c2 = CanonicalBytes::new(&json!({"a": 2})).unwrap();
        assert_ne!(sha256_digest(&c1), sha256_digest(&c2));
    }

    #[test]
    fn display_format() {
        let canonical = CanonicalBytes::new(&json!({})).unwrap();
        let digest = sha256_digest(&canonical);
        let display = format!("{digest}");
        assert!(display.starts_with("sha256:"));
        assert_eq!(display.len(), 7 + 64);
    }

    /// Verify byte-compatibility with the kernel tree. The canonical form of
    /// `{"a":1,"b":2}` is the UTF-8 bytes of that string.
    /// SHA-256 of those bytes is a fixed, known value.
    #[test]
    fn known_test_vector() {
        let value = json!({"b": 2, "a": 1});
        let canonical = CanonicalBytes::new(&value).unwrap();
        assert_eq!(
            std::str::from_utf8(canonical.as_bytes()).unwrap(),
            r#"{"a":1,"b":2}"#
        );
        let digest = sha256_digest(&canonical);
        // echo -n '{"a":1,"b":2}' | sha256sum
        let expected = "43258cff783fe7036d8a43033f830adfc60ec037382473548ac742b888292777";
        assert_eq!(digest.to_hex(), expected);
    }

    #[test]
    fn sha256_of_empty_object_matches_kernel_golden() {
        let c = CanonicalBytes::new(&json!({})).unwrap();
        let d = sha256_digest(&c);
        // echo -n '{}' | sha256sum
        let expected = "44136fa355b3678a1146ad16f7e8649e94fb4fc21fe77e8310c060f61caaff8a";
        assert_eq!(d.to_hex(), expected);
    }

    #[test]
    fn from_hex_roundtrips_with_to_hex() {
        let canonical = CanonicalBytes::new(&json!({"key": "value"})).unwrap();
        let original = sha256_digest(&canonical);
        let hex = original.to_hex();
        let reconstructed = ContentDigest::from_hex(&hex).unwrap();
        assert_eq!(original, reconstructed);
    }

    #[test]
    fn from_hex_rejects_short_string() {
        let result = ContentDigest::from_hex("abcd");
        assert!(matches!(
            result,
            Err(HexDigestError::InvalidLength { expected: 64, .. })
        ));
    }

    #[test]
    fn from_hex_rejects_long_string() {
        let long = "a".repeat(128);
        assert!(ContentDigest::from_hex(&long).is_err());
    }

    #[test]
    fn from_hex_rejects_non_hex_chars() {
        let bad = "z".repeat(64);
        assert!(matches!(
            ContentDigest::from_hex(&bad),
            Err(HexDigestError::InvalidHexByte { .. })
        ));
    }

    #[test]
    fn zero_digest_is_sha256() {
        let d = ContentDigest::zero();
        assert_eq!(d.algorithm(), DigestAlgorithm::Sha256);
        assert_eq!(d.as_bytes(), &[0u8; 32]);
    }

    #[test]
    fn digest_algorithm_display() {
        assert_eq!(format!("{}", DigestAlgorithm::Sha256), "sha256");
        assert_eq!(format!("{}", DigestAlgorithm::Poseidon2), "poseidon2");
    }

    #[test]
    fn sha256_raw_matches_sha256_digest_of_canonical_empty_object() {
        let c = CanonicalBytes::new(&json!({})).unwrap();
        let via_canonical = sha256_digest(&c).to_hex();
        let via_raw = sha256_raw(c.as_bytes());
        assert_eq!(via_canonical, via_raw);
    }

    #[test]
    fn sha256_bytes_matches_sha256_raw() {
        let data = b"hello";
        let raw_hex = sha256_raw(data);
        let bytes = sha256_bytes(data);
        let bytes_hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(raw_hex, bytes_hex);
    }

    #[test]
    fn content_digest_serde_roundtrip() {
        let canonical = CanonicalBytes::new(&json!({"key": "val"})).unwrap();
        let digest = sha256_digest(&canonical);
        let serialized = serde_json::to_string(&digest).unwrap();
        let deserialized: ContentDigest = serde_json::from_str(&serialized).unwrap();
        assert_eq!(digest, deserialized);
    }
}
