#![deny(missing_docs)]

//! # mez-canonical - Canonical Foundational Types
//!
//! Lex canonical foundational types: Lex Canonical Form (LCF) serialization ([`canonical::CanonicalBytes`]), SHA-256 content
//! digests ([`digest::sha256_digest`], [`digest::ContentDigest`]), and the
//! 23-variant [`domain::ComplianceDomain`] enum.
//!
//! This crate is the single source of truth for content-addressed compliance
//! primitives across the public Lex/Op tooling and downstream
//! runtimes that consume them. Everything that needs to produce a
//! content-addressed proof or interact with compliance domains depends on
//! this crate; the wire format is stable across all consumers.
//!
//! ## Scope
//!
//! - [`canonical::CanonicalBytes`] - Lex Canonical Form (LCF) serializer:
//!   RFC 8785 JCS plus datetime normalization to UTC seconds with a `Z`
//!   suffix. Sole construction path for bytes entering digest computation.
//! - [`digest::ContentDigest`], [`digest::DigestAlgorithm`],
//!   [`digest::sha256_digest`] - SHA-256 content-addressed digest of
//!   [`canonical::CanonicalBytes`].
//! - [`domain::ComplianceDomain`] - single enum with the 23 compliance
//!   domains used across the Lex/Op toolchain. Exhaustive `match` enforced by the
//!   compiler everywhere the enum appears.
//! - [`error::CanonicalizationError`] - the error type returned from LCF
//!   canonicalization.
//!
//! ## Design Principles
//!
//! 1. **[`canonical::CanonicalBytes`] is the sole path to digest
//!    computation.** The inner `Vec<u8>` is private. Bytes entering a digest
//!    must have passed through the LCF pipeline.
//! 2. **Single [`domain::ComplianceDomain`] enum.** 23 variants, exhaustive
//!    `match` everywhere.
//! 3. **Structured errors with `thiserror`.** No `Box<dyn Error>`.

pub mod canonical;
pub mod digest;
pub mod domain;
pub mod error;

pub use canonical::CanonicalBytes;
pub use digest::{
    sha256_bytes, sha256_digest, sha256_raw, ContentDigest, DigestAlgorithm, HexDigestError,
    Sha256Accumulator,
};
pub use domain::ComplianceDomain;
pub use error::CanonicalizationError;
