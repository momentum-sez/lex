//! Tiny digest helper for the core calculus frontier.
//!
//! Uses `sha2::Sha256` directly. The input is serialized to JSON via
//! `serde_json::to_vec`; frontier types deliberately avoid floats and other
//! non-canonical fields so the JSON serialization is stable across
//! invocations. Downstream kernel adapters that need canonical-equivalent
//! digests (e.g., under `CanonicalBytes`) recompute at the bridge boundary.

use serde::Serialize;
use sha2::{Digest, Sha256};

/// SHA-256 hex digest over the JSON serialization of `value`.
pub fn sha256_hex<T: Serialize>(value: &T) -> String {
    let bytes = serde_json::to_vec(value)
        .expect("core calculus values are always serializable");
    sha256_hex_bytes(&bytes)
}

/// SHA-256 hex digest over a raw byte slice.
pub fn sha256_hex_bytes(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    let out = h.finalize();
    hex_lower(&out)
}

fn hex_lower(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push(HEX[(b >> 4) as usize] as char);
        s.push(HEX[(b & 0x0f) as usize] as char);
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sha256_hex_len_is_64() {
        assert_eq!(sha256_hex(&"hello").len(), 64);
    }

    #[test]
    fn sha256_hex_is_deterministic() {
        let a = sha256_hex(&vec![1u8, 2, 3]);
        let b = sha256_hex(&vec![1u8, 2, 3]);
        assert_eq!(a, b);
    }

    #[test]
    fn sha256_hex_is_sensitive_to_input() {
        let a = sha256_hex(&"abc");
        let b = sha256_hex(&"abd");
        assert_ne!(a, b);
    }

    #[test]
    fn known_vector_bytes() {
        assert_eq!(
            sha256_hex_bytes(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }
}
