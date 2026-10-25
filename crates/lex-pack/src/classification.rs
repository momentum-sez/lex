//! Signed classifications that bind program purposes to executable artifacts and pack rules.

use std::{
    collections::{HashMap, HashSet},
    fmt,
    marker::PhantomData,
};

use lex_core::ast::{JurisdictionScope, OperationKindScope, QualIdent};
use mez_canonical::{
    sha256_digest, CanonicalBytes, CanonicalizationError, ContentDigest, ProgramPurposeTag,
};
use serde::{Deserialize, Deserializer, Serialize};

use crate::{CompiledLexPredicate, CuratorSignature, CuratorVerifier, Pack, PackVerifyError};

fn deserialize_wire<'de, D, T>(deserializer: D, expected: &'static str) -> Result<T, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    if deserializer.is_human_readable() {
        deserializer.deserialize_map(WireMapVisitor {
            expected,
            marker: PhantomData,
        })
    } else {
        T::deserialize(deserializer)
    }
}

struct WireMapVisitor<T> {
    expected: &'static str,
    marker: PhantomData<T>,
}

fn is_concrete_scope(value: &QualIdent) -> bool {
    !value.segments.is_empty()
        && value.segments.iter().all(|segment| {
            !segment.is_empty()
                && !segment
                    .chars()
                    .any(|ch| matches!(ch, '.' | '*') || ch.is_whitespace() || ch.is_control())
        })
}

impl<'de, T: Deserialize<'de>> serde::de::Visitor<'de> for WireMapVisitor<T> {
    type Value = T;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.expected)
    }

    fn visit_map<A: serde::de::MapAccess<'de>>(self, map: A) -> Result<Self::Value, A::Error> {
        T::deserialize(serde::de::value::MapAccessDeserializer::new(map))
    }
}

/// A curator's classification of one exact executable artifact for an authored purpose.
///
/// Rule references must be nonempty and unique. The containing pack validates their existence.
/// Human-readable formats require a map.
/// This classification does not establish that a rule passed admission.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct PurposeClassificationV1 {
    version: u32,
    purpose: ProgramPurposeTag,
    executable_digest: ContentDigest,
    rule_hashes: Vec<ContentDigest>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PurposeClassificationV1Wire {
    version: u32,
    purpose: ProgramPurposeTag,
    executable_digest: ContentDigest,
    rule_hashes: Vec<ContentDigest>,
}

impl<'de> Deserialize<'de> for PurposeClassificationV1 {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let wire = deserialize_wire::<D, PurposeClassificationV1Wire>(
            deserializer,
            "a purpose classification object",
        )?;
        Self::try_from(wire).map_err(serde::de::Error::custom)
    }
}

impl TryFrom<PurposeClassificationV1Wire> for PurposeClassificationV1 {
    type Error = ClassificationError;

    fn try_from(wire: PurposeClassificationV1Wire) -> Result<Self, Self::Error> {
        if wire.version != 1 {
            return Err(ClassificationError::UnsupportedVersion {
                artifact: "purpose classification",
                actual: wire.version,
            });
        }
        Self::new(wire.purpose, wire.executable_digest, wire.rule_hashes)
    }
}

impl PurposeClassificationV1 {
    /// Bind the supplied purpose and executable digest to explicit pack rule hashes.
    pub fn new(
        purpose: ProgramPurposeTag,
        executable_digest: ContentDigest,
        rule_hashes: Vec<ContentDigest>,
    ) -> Result<Self, ClassificationError> {
        if rule_hashes.is_empty() {
            return Err(ClassificationError::EmptyRuleReferences);
        }
        let mut seen = HashSet::new();
        for rule_hash in &rule_hashes {
            if !seen.insert(rule_hash) {
                return Err(ClassificationError::DuplicateRuleReference {
                    rule_hash: *rule_hash,
                });
            }
        }
        Ok(Self {
            version: 1,
            purpose,
            executable_digest,
            rule_hashes,
        })
    }

    /// Return the exact authored purpose.
    pub fn purpose(&self) -> &ProgramPurposeTag {
        &self.purpose
    }

    /// Return the exact executable artifact digest, including its algorithm.
    pub fn executable_digest(&self) -> &ContentDigest {
        &self.executable_digest
    }

    /// Return the referenced pack rule hashes in their signed order.
    pub fn rule_hashes(&self) -> &[ContentDigest] {
        &self.rule_hashes
    }
}

/// A versioned classification envelope around an unchanged [`Pack`].
///
/// Its separate digest binds the complete base pack and every classification.
/// Both signatures use the base pack's curator through the supplied verifier.
/// Construction checks references. Verification remains required before resolution.
/// Human-readable formats require a map.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ClassifiedPackV2 {
    version: u32,
    pack: Pack,
    classifications: Vec<PurposeClassificationV1>,
    digest: ContentDigest,
    signature: Option<CuratorSignature>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ClassifiedPackV2Wire {
    version: u32,
    pack: Pack,
    classifications: Vec<PurposeClassificationV1>,
    digest: ContentDigest,
    signature: Option<CuratorSignature>,
}

impl<'de> Deserialize<'de> for ClassifiedPackV2 {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let wire =
            deserialize_wire::<D, ClassifiedPackV2Wire>(deserializer, "a classified pack object")?;
        Self::try_from(wire).map_err(serde::de::Error::custom)
    }
}

impl TryFrom<ClassifiedPackV2Wire> for ClassifiedPackV2 {
    type Error = ClassificationError;

    fn try_from(wire: ClassifiedPackV2Wire) -> Result<Self, Self::Error> {
        if wire.version != 2 {
            return Err(ClassificationError::UnsupportedVersion {
                artifact: "classified pack",
                actual: wire.version,
            });
        }
        let classified = Self {
            version: wire.version,
            pack: wire.pack,
            classifications: wire.classifications,
            digest: wire.digest,
            signature: wire.signature,
        };
        classified.validate_references()?;
        Ok(classified)
    }
}

#[derive(Serialize)]
struct ClassificationBody<'a> {
    domain: &'static str,
    version: u32,
    pack: &'a Pack,
    classifications: &'a [PurposeClassificationV1],
}

impl ClassifiedPackV2 {
    /// Construct an unsigned classification envelope without changing the supplied pack.
    pub fn new(
        pack: Pack,
        classifications: Vec<PurposeClassificationV1>,
    ) -> Result<Self, ClassificationError> {
        let mut classified = Self {
            version: 2,
            pack,
            classifications,
            digest: ContentDigest::zero(),
            signature: None,
        };
        classified.validate_references()?;
        classified.digest = classified.recompute_digest()?;
        Ok(classified)
    }

    /// Return the unchanged base pack.
    pub fn pack(&self) -> &Pack {
        &self.pack
    }

    /// Return all signed classification entries in their authored order.
    pub fn classifications(&self) -> &[PurposeClassificationV1] {
        &self.classifications
    }

    /// Return the domain-separated digest to sign with the base curator's key.
    pub fn digest(&self) -> &ContentDigest {
        &self.digest
    }

    /// Record an opaque signature over this envelope's digest.
    ///
    /// This operation does not establish signature validity.
    pub fn with_signature(mut self, signature: CuratorSignature) -> Self {
        self.signature = Some(signature);
        self
    }

    /// Verify the base pack and the separate classification signature with the same curator.
    pub fn verify(&self, verifier: &dyn CuratorVerifier) -> Result<(), ClassificationError> {
        self.pack.verify(verifier)?;
        let recomputed = self.recompute_digest()?;
        if recomputed != self.digest {
            return Err(ClassificationError::DigestMismatch {
                recorded: self.digest,
                recomputed,
            });
        }
        let signature = self
            .signature
            .as_ref()
            .ok_or(ClassificationError::Unsigned)?;
        verifier
            .verify(
                &self.pack.version.curator_did,
                &self.digest.to_hex(),
                signature,
            )
            .map_err(ClassificationError::SignatureRejected)
    }

    /// Verify complete classification coverage and resolve all applicable base-pack rules.
    ///
    /// The caller supplies the actual executable digest and concrete operation scope.
    /// References cannot omit an applicable rule or change the base pack's rule order.
    /// Success always contains at least one rule. This does not discharge rule obligations.
    pub fn resolve(
        &self,
        purpose: &ProgramPurposeTag,
        executable_digest: &ContentDigest,
        jurisdiction: &QualIdent,
        operation_kind: &QualIdent,
        verifier: &dyn CuratorVerifier,
    ) -> Result<Vec<&CompiledLexPredicate>, ClassificationError> {
        self.verify(verifier)?;
        for (field, value) in [
            ("jurisdiction", jurisdiction),
            ("operation_kind", operation_kind),
        ] {
            if !is_concrete_scope(value) {
                return Err(ClassificationError::InvalidResolutionScope { field });
            }
        }

        let matching_purpose: Vec<_> = self
            .classifications
            .iter()
            .filter(|entry| &entry.purpose == purpose)
            .collect();
        if matching_purpose.is_empty() {
            return Err(ClassificationError::UnknownPurpose {
                purpose: purpose.clone(),
            });
        }
        let entry = matching_purpose
            .into_iter()
            .find(|entry| &entry.executable_digest == executable_digest)
            .ok_or_else(|| ClassificationError::WrongArtifact {
                purpose: purpose.clone(),
                provided: *executable_digest,
            })?;

        let rules_by_digest = self.rules_by_digest()?;
        for rule_hash in &entry.rule_hashes {
            if !rules_by_digest.contains_key(rule_hash) {
                return Err(ClassificationError::UnknownRuleReference {
                    rule_hash: *rule_hash,
                });
            }
        }
        let rules = self.pack.rules_for(jurisdiction, operation_kind);
        if rules.is_empty() {
            return Err(ClassificationError::NoApplicableRules {
                purpose: purpose.clone(),
                jurisdiction: jurisdiction.to_dotted(),
                operation_kind: operation_kind.to_dotted(),
            });
        }
        let referenced: HashSet<_> = entry.rule_hashes.iter().copied().collect();
        let mut missing_rule_hashes = Vec::new();
        for rule in &rules {
            let digest = Self::decode_rule_hash(&rule.rule_hash)?;
            if !referenced.contains(&digest) {
                missing_rule_hashes.push(digest);
            }
        }
        if !missing_rule_hashes.is_empty() {
            return Err(ClassificationError::IncompleteCoverage {
                purpose: purpose.clone(),
                jurisdiction: jurisdiction.to_dotted(),
                operation_kind: operation_kind.to_dotted(),
                missing_rule_hashes,
            });
        }
        Ok(rules)
    }

    fn validate_references(&self) -> Result<(), ClassificationError> {
        if self.classifications.is_empty() {
            return Err(ClassificationError::EmptyClassifications);
        }
        let rules_by_digest = self.rules_by_digest()?;

        let mut keys = HashSet::new();
        for entry in &self.classifications {
            if !keys.insert((&entry.purpose, &entry.executable_digest)) {
                return Err(ClassificationError::DuplicateClassification {
                    purpose: entry.purpose.clone(),
                    executable_digest: entry.executable_digest,
                });
            }
            for rule_hash in &entry.rule_hashes {
                if !rules_by_digest.contains_key(rule_hash) {
                    return Err(ClassificationError::UnknownRuleReference {
                        rule_hash: *rule_hash,
                    });
                }
            }
        }
        Ok(())
    }

    fn rules_by_digest(
        &self,
    ) -> Result<HashMap<ContentDigest, &CompiledLexPredicate>, ClassificationError> {
        let mut rules = HashMap::new();
        for rule in &self.pack.rules {
            let scope = &rule.applies_to;
            let valid_jurisdictions = !scope.jurisdictions.is_empty()
                && scope
                    .jurisdictions
                    .iter()
                    .all(|jurisdiction| match jurisdiction {
                        JurisdictionScope::All => true,
                        JurisdictionScope::Specific(value) => is_concrete_scope(value),
                    });
            let valid_operations = !scope.operation_kinds.is_empty()
                && scope
                    .operation_kinds
                    .iter()
                    .all(|operation| match operation {
                        OperationKindScope::All => true,
                        OperationKindScope::Specific(value) => is_concrete_scope(value),
                        OperationKindScope::Family(value) => {
                            value.segments.len() == 1 && is_concrete_scope(value)
                        }
                    });
            if !valid_jurisdictions || !valid_operations {
                return Err(ClassificationError::InvalidPackRuleScope {
                    rule_hash: rule.rule_hash.clone(),
                });
            }
            let digest = Self::decode_rule_hash(&rule.rule_hash)?;
            if rules.insert(digest, rule).is_some() {
                return Err(ClassificationError::DuplicatePackRule { rule_hash: digest });
            }
        }
        Ok(rules)
    }

    fn decode_rule_hash(hash: &str) -> Result<ContentDigest, ClassificationError> {
        if hash.len() != 64 || !hash.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(ClassificationError::InvalidPackRuleHash {
                rule_hash: hash.to_owned(),
            });
        }
        ContentDigest::from_hex(hash).map_err(|_| ClassificationError::InvalidPackRuleHash {
            rule_hash: hash.to_owned(),
        })
    }

    fn recompute_digest(&self) -> Result<ContentDigest, ClassificationError> {
        let body = ClassificationBody {
            domain: "lex.classified_pack.v2",
            version: self.version,
            pack: &self.pack,
            classifications: &self.classifications,
        };
        Ok(sha256_digest(&CanonicalBytes::new(&body)?))
    }
}

/// Failure to construct, verify, or resolve a classified pack.
#[derive(Debug, thiserror::Error)]
pub enum ClassificationError {
    /// A base rule has an empty or malformed applicability scope.
    #[error("base pack rule {rule_hash} has an invalid applicability scope")]
    InvalidPackRuleScope {
        /// The rule whose scope cannot establish applicability.
        rule_hash: String,
    },
    /// A wrapper version is unsupported.
    #[error("unsupported {artifact} version {actual}")]
    UnsupportedVersion {
        /// The wrapper whose version was rejected.
        artifact: &'static str,
        /// The supplied version.
        actual: u32,
    },
    /// A classified pack has no classifications.
    #[error("classified pack requires at least one classification")]
    EmptyClassifications,
    /// A classification has no rule references.
    #[error("purpose classification requires at least one rule reference")]
    EmptyRuleReferences,
    /// A classification repeats a rule reference.
    #[error("duplicate classified rule reference {rule_hash}")]
    DuplicateRuleReference {
        /// The repeated hash.
        rule_hash: ContentDigest,
    },
    /// A reference does not identify a rule in the base pack.
    #[error("unknown classified rule reference {rule_hash}")]
    UnknownRuleReference {
        /// The unknown hash.
        rule_hash: ContentDigest,
    },
    /// The base pack contains an ambiguous rule hash.
    #[error("duplicate base pack rule hash {rule_hash}")]
    DuplicatePackRule {
        /// The ambiguous hash.
        rule_hash: ContentDigest,
    },
    /// A base rule hash cannot be decoded as a SHA-256 content digest.
    #[error("invalid base pack rule hash {rule_hash}")]
    InvalidPackRuleHash {
        /// The invalid legacy hash string.
        rule_hash: String,
    },
    /// Multiple entries use the same purpose and executable digest.
    #[error("duplicate classification for {purpose} and {executable_digest}")]
    DuplicateClassification {
        /// The repeated purpose.
        purpose: ProgramPurposeTag,
        /// The repeated artifact digest.
        executable_digest: ContentDigest,
    },
    /// The base pack failed its existing verification contract.
    #[error("base pack verification failed: {0}")]
    BasePack(#[from] PackVerifyError),
    /// Canonical serialization failed.
    #[error(transparent)]
    Canonicalization(#[from] CanonicalizationError),
    /// The classification digest differs from its content.
    #[error("classification digest mismatch: recorded {recorded}, recomputed {recomputed}")]
    DigestMismatch {
        /// The recorded digest.
        recorded: ContentDigest,
        /// The computed digest.
        recomputed: ContentDigest,
    },
    /// The outer classification signature is absent.
    #[error("classified pack is unsigned")]
    Unsigned,
    /// The verifier rejected the outer classification signature.
    #[error("classification signature rejected: {0}")]
    SignatureRejected(String),
    /// No classification uses the exact requested purpose.
    #[error("unknown program purpose {purpose}")]
    UnknownPurpose {
        /// The requested purpose.
        purpose: ProgramPurposeTag,
    },
    /// The purpose exists, but the exact executable digest is not classified.
    #[error("artifact {provided} is not classified for {purpose}")]
    WrongArtifact {
        /// The requested purpose.
        purpose: ProgramPurposeTag,
        /// The actual executable digest supplied by the caller.
        provided: ContentDigest,
    },
    /// A query omitted a concrete scope or supplied a malformed identifier.
    #[error("classification resolution requires a concrete {field}")]
    InvalidResolutionScope {
        /// The missing or non-concrete scope component.
        field: &'static str,
    },
    /// The classification omits rules that apply to the supplied operation scope.
    #[error("classification for {purpose} does not cover every rule in {jurisdiction} for {operation_kind}")]
    IncompleteCoverage {
        /// The requested purpose.
        purpose: ProgramPurposeTag,
        /// The actual jurisdiction.
        jurisdiction: String,
        /// The actual operation kind.
        operation_kind: String,
        /// Applicable rule digests absent from the classification, in base-pack order.
        missing_rule_hashes: Vec<ContentDigest>,
    },
    /// No base-pack rules match the supplied operation scope.
    #[error("no base-pack rules apply to {purpose} in {jurisdiction} for {operation_kind}")]
    NoApplicableRules {
        /// The requested purpose.
        purpose: ProgramPurposeTag,
        /// The actual jurisdiction.
        jurisdiction: String,
        /// The actual operation kind.
        operation_kind: String,
    },
}
