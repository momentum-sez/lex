//! # Canonical Serialization — Momentum Canonical Form (MCF)
//!
//! This module defines [`CanonicalBytes`], the sole construction path for bytes
//! used in digest computation across the Lex pipeline.
//!
//! ## Momentum Canonical Form (MCF)
//!
//! MCF is based on RFC 8785 JSON Canonicalization Scheme (JCS) with two
//! additional safety coercions:
//!
//! 1. Convert to `serde_json::Value`
//! 2. Reject any `Number` that is f64-only (non-integer, NaN, Inf)
//! 3. Normalize RFC 3339 datetime strings to UTC, truncated to seconds,
//!    suffix `Z`
//! 4. Serialize with RFC 8785 JCS rules (sorted keys, no whitespace)
//!
//! **Digest:** `SHA-256(MCF(payload))`
//!
//! ## Security Invariant
//!
//! The inner `Vec<u8>` is private. The only way to construct `CanonicalBytes`
//! is through [`CanonicalBytes::new`], which applies the full MCF pipeline
//! before serialization. This makes the "wrong serialization path" class of
//! defects structurally impossible.

use serde::Serialize;
use serde_json::Value;

use crate::error::CanonicalizationError;

/// Bytes produced exclusively by Momentum Canonical Form (MCF) canonicalization.
///
/// MCF = RFC 8785 JCS + float rejection + datetime normalization to UTC seconds.
///
/// The inner `Vec<u8>` is private — downstream code cannot construct
/// `CanonicalBytes` except through [`CanonicalBytes::new`]. This single
/// construction path ensures every digest in the system is computed from
/// properly canonicalized data.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CanonicalBytes(Vec<u8>);

impl CanonicalBytes {
    /// Construct canonical bytes from any serializable value.
    ///
    /// Applies the full Momentum type coercion pipeline before serialization:
    /// 1. Converts to `serde_json::Value` via serde.
    /// 2. Recursively coerces types (float rejection, datetime normalization).
    /// 3. Serializes with sorted keys and compact separators.
    ///
    /// # Errors
    ///
    /// Returns [`CanonicalizationError::FloatRejected`] if any numeric value
    /// is a float (not representable as `i64` or `u64`).
    /// Returns [`CanonicalizationError::SerializationFailed`] if serde
    /// serialization fails.
    pub fn new(obj: &impl Serialize) -> Result<Self, CanonicalizationError> {
        let value = serde_json::to_value(obj)?;
        let coerced = coerce_json_value(value)?;
        let bytes = serialize_canonical(&coerced)?;
        Ok(Self(bytes))
    }

    /// Construct canonical bytes from a pre-existing `serde_json::Value`.
    ///
    /// Applies the same coercion pipeline as [`CanonicalBytes::new`].
    pub fn from_value(value: Value) -> Result<Self, CanonicalizationError> {
        let coerced = coerce_json_value(value)?;
        let bytes = serialize_canonical(&coerced)?;
        Ok(Self(bytes))
    }

    /// Access the canonical bytes for digest computation.
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Consume and return the inner byte vector.
    pub fn into_bytes(self) -> Vec<u8> {
        self.0
    }

    /// Return the length of the canonical byte representation.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Return whether the canonical byte representation is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl AsRef<[u8]> for CanonicalBytes {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

/// Recursively coerce JSON values according to Momentum canonicalization rules.
///
/// - Rejects floats (numbers that are not representable as `i64` or `u64`).
/// - Normalizes RFC 3339 datetime strings to UTC with `Z` suffix, truncated to
///   seconds.
/// - Recursively processes objects and arrays.
/// - Passes through strings, booleans, integers, and null unchanged.
fn coerce_json_value(value: Value) -> Result<Value, CanonicalizationError> {
    match value {
        Value::Number(ref n) => {
            if n.is_i64() || n.is_u64() {
                Ok(value)
            } else if let Some(f) = n.as_f64() {
                Err(CanonicalizationError::FloatRejected(f))
            } else {
                // serde_json::Number is guaranteed to be one of i64/u64/f64.
                Err(CanonicalizationError::FloatRejected(f64::NAN))
            }
        }
        Value::Object(map) => {
            // serde_json::Map is BTreeMap by default → keys already sorted.
            // We rebuild to coerce child values.
            let mut coerced = serde_json::Map::new();
            for (k, v) in map {
                coerced.insert(k, coerce_json_value(v)?);
            }
            Ok(Value::Object(coerced))
        }
        Value::Array(arr) => {
            let coerced: Result<Vec<_>, _> = arr.into_iter().map(coerce_json_value).collect();
            Ok(Value::Array(coerced?))
        }
        Value::String(ref s) => {
            // Datetime normalization: if the string parses as RFC 3339,
            // normalize to UTC ISO 8601 with Z suffix, truncated to seconds.
            if let Ok(dt) = chrono::DateTime::parse_from_rfc3339(s) {
                let utc = dt.with_timezone(&chrono::Utc);
                Ok(Value::String(utc.format("%Y-%m-%dT%H:%M:%SZ").to_string()))
            } else {
                Ok(value)
            }
        }
        // Bool and Null pass through unchanged.
        #[allow(clippy::wildcard_enum_match_arm)]
        other => Ok(other),
    }
}

/// Serialize a JSON value with sorted keys and compact separators.
fn serialize_canonical(value: &Value) -> Result<Vec<u8>, CanonicalizationError> {
    Ok(serde_json::to_vec(value)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn canonical_sorts_keys() {
        let value = json!({"z": 1, "a": 2, "m": 3});
        let cb = CanonicalBytes::new(&value).unwrap();
        let s = std::str::from_utf8(cb.as_bytes()).unwrap();
        assert_eq!(s, r#"{"a":2,"m":3,"z":1}"#);
    }

    #[test]
    fn canonical_nested_key_sorting() {
        let value = json!({"b": {"z": 1, "a": 2}, "a": 1});
        let cb = CanonicalBytes::new(&value).unwrap();
        let s = std::str::from_utf8(cb.as_bytes()).unwrap();
        assert_eq!(s, r#"{"a":1,"b":{"a":2,"z":1}}"#);
    }

    #[test]
    fn canonical_rejects_float() {
        let value = json!({"amount": 3.15});
        let result = CanonicalBytes::new(&value);
        assert!(matches!(
            result,
            Err(CanonicalizationError::FloatRejected(_))
        ));
    }

    #[test]
    fn canonical_accepts_integers() {
        let value = json!({"count": 42, "negative": -7, "zero": 0});
        let cb = CanonicalBytes::new(&value).unwrap();
        let s = std::str::from_utf8(cb.as_bytes()).unwrap();
        assert_eq!(s, r#"{"count":42,"negative":-7,"zero":0}"#);
    }

    #[test]
    fn canonical_normalizes_datetime_string() {
        let value = json!({"ts": "2026-01-15T12:00:00.123456+00:00"});
        let cb = CanonicalBytes::new(&value).unwrap();
        let s = std::str::from_utf8(cb.as_bytes()).unwrap();
        assert_eq!(s, r#"{"ts":"2026-01-15T12:00:00Z"}"#);
    }

    #[test]
    fn canonical_normalizes_non_utc_datetime() {
        let value = json!({"ts": "2026-01-15T17:00:00+05:00"});
        let cb = CanonicalBytes::new(&value).unwrap();
        let s = std::str::from_utf8(cb.as_bytes()).unwrap();
        assert_eq!(s, r#"{"ts":"2026-01-15T12:00:00Z"}"#);
    }

    #[test]
    fn canonical_preserves_non_datetime_strings() {
        let value = json!({"name": "hello world", "id": "abc-123"});
        let cb = CanonicalBytes::new(&value).unwrap();
        let s = std::str::from_utf8(cb.as_bytes()).unwrap();
        assert_eq!(s, r#"{"id":"abc-123","name":"hello world"}"#);
    }

    #[test]
    fn canonical_handles_empty_structures() {
        let empty_obj = json!({});
        let empty_arr = json!([]);
        assert_eq!(
            std::str::from_utf8(CanonicalBytes::new(&empty_obj).unwrap().as_bytes()).unwrap(),
            "{}"
        );
        assert_eq!(
            std::str::from_utf8(CanonicalBytes::new(&empty_arr).unwrap().as_bytes()).unwrap(),
            "[]"
        );
    }

    #[test]
    fn canonical_null_bool() {
        let value = json!({"flag": true, "nothing": null, "off": false});
        let cb = CanonicalBytes::new(&value).unwrap();
        let s = std::str::from_utf8(cb.as_bytes()).unwrap();
        assert_eq!(s, r#"{"flag":true,"nothing":null,"off":false}"#);
    }

    #[test]
    fn canonical_is_deterministic() {
        let value = json!({"b": [3, 2, 1], "a": {"y": "hello", "x": 42}});
        let a = CanonicalBytes::new(&value).unwrap();
        let b = CanonicalBytes::new(&value).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn from_value_matches_new() {
        let value = json!({"key": "value", "n": 42});
        let from_new = CanonicalBytes::new(&value).unwrap();
        let from_value = CanonicalBytes::from_value(value).unwrap();
        assert_eq!(from_new, from_value);
    }

    #[test]
    fn canonical_len_and_is_empty() {
        let value = json!({});
        let cb = CanonicalBytes::new(&value).unwrap();
        assert_eq!(cb.len(), 2); // "{}"
        assert!(!cb.is_empty());
    }

    #[test]
    fn canonical_into_bytes() {
        let value = json!({"key": "val"});
        let cb = CanonicalBytes::new(&value).unwrap();
        let expected = cb.as_bytes().to_vec();
        let bytes = cb.into_bytes();
        assert_eq!(bytes, expected);
    }

    #[test]
    fn canonical_as_ref() {
        let value = json!({"x": 1});
        let cb = CanonicalBytes::new(&value).unwrap();
        let as_ref_bytes: &[u8] = cb.as_ref();
        assert_eq!(as_ref_bytes, cb.as_bytes());
    }

    #[test]
    fn canonical_clone_and_eq() {
        let value = json!({"a": 1});
        let cb = CanonicalBytes::new(&value).unwrap();
        let cb2 = cb.clone();
        assert_eq!(cb, cb2);
    }

    #[test]
    fn serde_json_map_must_use_sorted_order() {
        let mut map = serde_json::Map::new();
        map.insert("z".to_string(), serde_json::Value::Null);
        map.insert("m".to_string(), serde_json::Value::Null);
        map.insert("a".to_string(), serde_json::Value::Null);
        let keys: Vec<&String> = map.keys().collect();
        assert_eq!(
            keys,
            vec!["a", "m", "z"],
            "serde_json preserve_order is active — Map uses IndexMap not BTreeMap"
        );
    }

    // Golden vectors — must produce bytes and digests identical to the kernel
    // tree so fibers/certificates remain byte-compatible.
    #[test]
    fn golden_empty_object() {
        let cb = CanonicalBytes::new(&json!({})).unwrap();
        assert_eq!(std::str::from_utf8(cb.as_bytes()).unwrap(), "{}");
    }

    #[test]
    fn golden_nested_sorted_keys() {
        let cb = CanonicalBytes::new(&json!({"z": {"b": 2, "a": 1}, "a": 0})).unwrap();
        assert_eq!(
            std::str::from_utf8(cb.as_bytes()).unwrap(),
            r#"{"a":0,"z":{"a":1,"b":2}}"#
        );
    }
}
