#![deny(missing_docs)]

//! # mez-core-min — Foundational Types for Lex (standalone)
//!
//! A minimal, standalone crate providing the subset of `mez-core` that Lex
//! depends on: canonical serialization ([`canonical::CanonicalBytes`]), SHA-256
//! content digests ([`digest::sha256_digest`], [`digest::ContentDigest`]), and
//! the 23-variant [`domain::ComplianceDomain`] enum.
//!
//! This crate reimplements those types so a cold clone of `~/lex` compiles
//! without requiring an external kernel repository checkout. The definitions
//! are kept byte-compatible with the kernel tree so fibers and certificates
//! produced by Lex retain their content-addressed digests when consumed by
//! the full kernel.
//!
//! ## Scope
//!
//! - [`canonical::CanonicalBytes`] — Momentum Canonical Form (MCF) serializer:
//!   RFC 8785 JCS plus datetime normalization to UTC seconds with a `Z`
//!   suffix. Sole construction path for bytes entering digest computation.
//! - [`digest::ContentDigest`], [`digest::DigestAlgorithm`],
//!   [`digest::sha256_digest`] — SHA-256 content-addressed digest of
//!   [`canonical::CanonicalBytes`].
//! - [`domain::ComplianceDomain`] — single enum with the 23 compliance
//!   domains used across the EZ Stack. Exhaustive `match` enforced by the
//!   compiler everywhere the enum appears.
//! - [`error::CanonicalizationError`] — the error type returned from MCF
//!   canonicalization.
//!
//! ## Design Principles
//!
//! 1. **[`canonical::CanonicalBytes`] is the sole path to digest
//!    computation.** The inner `Vec<u8>` is private. Bytes entering a digest
//!    must have passed through the MCF pipeline.
//! 2. **Single [`domain::ComplianceDomain`] enum.** 23 variants, exhaustive
//!    `match` everywhere.
//! 3. **Structured errors with `thiserror`.** No `Box<dyn Error>`.

pub mod canonical;
pub mod digest;
pub mod domain;
pub mod error;

pub use canonical::CanonicalBytes;
pub use digest::{sha256_bytes, sha256_digest, sha256_raw, ContentDigest, DigestAlgorithm};
pub use domain::ComplianceDomain;
pub use error::CanonicalizationError;
