use lex_core::{
    ast::{AppliesTo, JurisdictionScope, OperationKindScope, QualIdent, Term},
    elaborate, prelude, typecheck, AuthoredLexProgramV1,
};
use lex_pack::{
    compile, AdmittedRule, ClassificationError, ClassifiedPackV2, CuratorSignature,
    CuratorVerifier, Pack, PackVerifyError, PurposeClassificationV1,
};
use mez_canonical::{sha256_digest, CanonicalBytes, ContentDigest, ProgramPurposeTag};
use serde::{Deserialize, Deserializer};
use serde_json::{json, Value};

const CURATOR: &str = "did:example:curator";

struct SchemaDirectedStruct(Value);

impl<'de> Deserializer<'de> for SchemaDirectedStruct {
    type Error = serde_json::Error;

    fn deserialize_any<V: serde::de::Visitor<'de>>(
        self,
        _visitor: V,
    ) -> Result<V::Value, Self::Error> {
        Err(serde::de::Error::custom(
            "this format requires a struct schema",
        ))
    }

    fn deserialize_struct<V: serde::de::Visitor<'de>>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        self.0.deserialize_any(visitor)
    }

    fn is_human_readable(&self) -> bool {
        false
    }

    serde::forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string bytes byte_buf
        option unit unit_struct newtype_struct seq tuple tuple_struct map enum identifier ignored_any
    }
}

// This verifier checks registered test tuples. It does not perform cryptography.
#[derive(Default)]
struct BoundVerifier(Vec<(String, String, CuratorSignature)>);

impl BoundVerifier {
    fn register(&mut self, curator: &str, digest: &str, signature: &CuratorSignature) {
        self.0
            .push((curator.into(), digest.into(), signature.clone()));
    }
}

impl CuratorVerifier for BoundVerifier {
    fn verify(
        &self,
        curator_did: &str,
        content_digest: &str,
        signature: &CuratorSignature,
    ) -> Result<(), String> {
        if self.0.iter().any(|(curator, digest, registered)| {
            curator == curator_did && digest == content_digest && registered == signature
        }) {
            Ok(())
        } else {
            Err("no registered test signature for this curator and digest".into())
        }
    }
}

fn signature(byte: &str) -> CuratorSignature {
    CuratorSignature {
        scheme: "test-tuple-only".into(),
        signature_hex: byte.repeat(32),
    }
}

fn purpose(value: &str) -> ProgramPurposeTag {
    ProgramPurposeTag::new(value).unwrap()
}

fn artifact(value: &str) -> ContentDigest {
    sha256_digest(&CanonicalBytes::new(&value).unwrap())
}

fn qi(value: &str) -> QualIdent {
    QualIdent::from_dotted(value)
}

fn rule_digest(pack: &Pack, index: usize) -> ContentDigest {
    ContentDigest::from_hex(&pack.rules[index].rule_hash).unwrap()
}

fn rule(name: &str, jurisdiction: &str, source: &str) -> AdmittedRule {
    let parsed = AuthoredLexProgramV1::new(purpose("Entity.Incorporate"), source)
        .parse()
        .unwrap();
    let context = prelude::structural_prelude();
    let body = elaborate::elaborate(parsed.term(), &context).unwrap();
    typecheck::check_admissible(&context, &body, &Term::constant("ComplianceVerdict")).unwrap();
    AdmittedRule {
        name: name.into(),
        legal_basis: "Example law".into(),
        applies_to: Some(AppliesTo {
            jurisdictions: vec![JurisdictionScope::Specific(qi(jurisdiction))],
            operation_kinds: vec![OperationKindScope::Specific(qi("entity.incorporate"))],
        }),
        body,
    }
}

fn signed_rules(rules: Vec<AdmittedRule>) -> (Pack, BoundVerifier) {
    let pack = compile(CURATOR, "1.0.0", rules).unwrap();
    let sig = signature("11");
    let mut verifier = BoundVerifier::default();
    verifier.register(CURATOR, &pack.digest, &sig);
    (pack.with_signature(sig), verifier)
}

fn signed_base() -> (Pack, BoundVerifier) {
    signed_rules(vec![
        rule("sc_selected", "sc", "Compliant"),
        rule("de_selected", "de", "Pending"),
        rule("sc_blocking", "sc", "NonCompliant"),
    ])
}

fn entry(pack: &Pack, indices: &[usize]) -> PurposeClassificationV1 {
    PurposeClassificationV1::new(
        purpose("Entity.Incorporate"),
        artifact("executable-a"),
        indices
            .iter()
            .map(|&index| rule_digest(pack, index))
            .collect(),
    )
    .unwrap()
}

fn sign_outer(pack: ClassifiedPackV2, verifier: &mut BoundVerifier) -> ClassifiedPackV2 {
    let sig = signature("22");
    verifier.register(
        &pack.pack().version.curator_did,
        &pack.digest().to_hex(),
        &sig,
    );
    pack.with_signature(sig)
}

fn classified() -> (ClassifiedPackV2, BoundVerifier) {
    let (pack, mut verifier) = signed_base();
    let classification = entry(&pack, &[2, 1, 0]);
    let outer = ClassifiedPackV2::new(pack, vec![classification]).unwrap();
    (sign_outer(outer, &mut verifier), verifier)
}

fn classification_array(classification: &PurposeClassificationV1) -> Value {
    let wire = serde_json::to_value(classification).unwrap();
    json!([
        wire["version"],
        wire["purpose"],
        wire["executable_digest"],
        wire["rule_hashes"],
    ])
}

fn classified_pack_array(pack: &ClassifiedPackV2) -> Value {
    let wire = serde_json::to_value(pack).unwrap();
    json!([
        wire["version"],
        wire["pack"],
        wire["classifications"],
        wire["digest"],
        wire["signature"],
    ])
}

fn duplicate_field(wire: &Value, field: &str) -> String {
    let original = wire.to_string();
    format!(
        "{{{}:{},{}",
        serde_json::to_string(field).unwrap(),
        wire[field],
        original.strip_prefix('{').unwrap(),
    )
}

#[test]
fn positional_json_arrays_cannot_replace_classification_objects() {
    let (classified, verifier) = classified();
    let entry_array = classification_array(&classified.classifications()[0]);
    let outer_array = classified_pack_array(&classified);
    let mut nested = serde_json::to_value(&classified).unwrap();
    nested["classifications"] = json!([entry_array.clone()]);
    let entry_decoded = serde_json::from_str::<PurposeClassificationV1>(&entry_array.to_string());
    let outer_decoded = serde_json::from_str::<ClassifiedPackV2>(&outer_array.to_string());
    let nested_decoded = serde_json::from_str::<ClassifiedPackV2>(&nested.to_string());
    let resolves = |pack: &ClassifiedPackV2| {
        pack.resolve(
            &purpose("Entity.Incorporate"),
            &artifact("executable-a"),
            &qi("sc"),
            &qi("entity.incorporate"),
            &verifier,
        )
        .is_ok()
    };
    assert!(
        entry_decoded.is_err() && outer_decoded.is_err() && nested_decoded.is_err(),
        "arrays accepted: entry={}, outer={}, nested={}, outer_resolves={}, nested_resolves={}",
        entry_decoded.is_ok(),
        outer_decoded.is_ok(),
        nested_decoded.is_ok(),
        outer_decoded.as_ref().is_ok_and(resolves),
        nested_decoded.as_ref().is_ok_and(resolves),
    );
}

#[test]
fn classification_objects_preserve_duplicate_field_rejection_at_both_levels() {
    let (classified, verifier) = classified();
    let entry = serde_json::to_value(&classified.classifications()[0]).unwrap();
    let outer = serde_json::to_value(&classified).unwrap();
    let decoded: ClassifiedPackV2 = serde_json::from_str(&outer.to_string()).unwrap();
    decoded.verify(&verifier).unwrap();
    assert_eq!(
        serde_json::from_str::<PurposeClassificationV1>(&entry.to_string()).unwrap(),
        classified.classifications()[0]
    );

    for field in ["version", "purpose", "executable_digest", "rule_hashes"] {
        let duplicated = duplicate_field(&entry, field);
        assert!(serde_json::from_str::<PurposeClassificationV1>(&duplicated).is_err());
        let nested = format!(
            r#"{{"version":2,"pack":{},"classifications":[{}],"digest":{},"signature":{}}}"#,
            outer["pack"], duplicated, outer["digest"], outer["signature"],
        );
        assert!(serde_json::from_str::<ClassifiedPackV2>(&nested).is_err());
    }
    for field in ["version", "pack", "classifications", "digest", "signature"] {
        assert!(serde_json::from_str::<ClassifiedPackV2>(&duplicate_field(&outer, field)).is_err());
    }
}

#[test]
fn schema_directed_classifications_keep_field_order_and_validation() {
    let (classified, verifier) = classified();
    let entry = &classified.classifications()[0];
    let mut entry_array = classification_array(entry);
    let decoded =
        PurposeClassificationV1::deserialize(SchemaDirectedStruct(entry_array.clone())).unwrap();
    assert_eq!(&decoded, entry);
    entry_array[0] = json!(2);
    assert!(PurposeClassificationV1::deserialize(SchemaDirectedStruct(entry_array)).is_err());

    let mut outer_array = classified_pack_array(&classified);
    let decoded = ClassifiedPackV2::deserialize(SchemaDirectedStruct(outer_array.clone())).unwrap();
    let rules = decoded
        .resolve(
            &purpose("Entity.Incorporate"),
            &artifact("executable-a"),
            &qi("sc"),
            &qi("entity.incorporate"),
            &verifier,
        )
        .unwrap();
    assert_eq!(
        rules
            .iter()
            .map(|rule| rule.name.as_str())
            .collect::<Vec<_>>(),
        ["sc_selected", "sc_blocking"]
    );
    outer_array[0] = json!(3);
    assert!(ClassifiedPackV2::deserialize(SchemaDirectedStruct(outer_array)).is_err());
}

#[test]
fn omitting_an_applicable_blocking_rule_is_an_incomplete_classification() {
    let (base, mut verifier) = signed_base();
    let blocking_digest = rule_digest(&base, 2);
    let classification = entry(&base, &[0, 1]);
    let classified = sign_outer(
        ClassifiedPackV2::new(base, vec![classification]).unwrap(),
        &mut verifier,
    );
    let error = classified
        .resolve(
            &purpose("Entity.Incorporate"),
            &artifact("executable-a"),
            &qi("sc"),
            &qi("entity.incorporate"),
            &verifier,
        )
        .unwrap_err();
    match error {
        ClassificationError::IncompleteCoverage {
            purpose: actual_purpose,
            jurisdiction,
            operation_kind,
            missing_rule_hashes,
        } => {
            assert_eq!(actual_purpose.as_str(), "Entity.Incorporate");
            assert_eq!(jurisdiction, "sc");
            assert_eq!(operation_kind, "entity.incorporate");
            assert_eq!(missing_rule_hashes, vec![blocking_digest]);
        }
        other => panic!("unexpected rejection: {other}"),
    }
}

#[test]
fn identifier_segment_aliases_cannot_hide_an_applicable_blocking_rule() {
    let mut global = rule("global", "sc.region", "Compliant");
    global.applies_to = Some(AppliesTo {
        jurisdictions: vec![JurisdictionScope::All],
        operation_kinds: vec![OperationKindScope::All],
    });
    let (base, mut verifier) =
        signed_rules(vec![global, rule("blocking", "sc.region", "NonCompliant")]);
    let classification = entry(&base, &[0]);
    let classified = sign_outer(
        ClassifiedPackV2::new(base, vec![classification]).unwrap(),
        &mut verifier,
    );
    assert!(matches!(
        classified.resolve(
            &purpose("Entity.Incorporate"),
            &artifact("executable-a"),
            &qi("sc.region"),
            &qi("entity.incorporate"),
            &verifier,
        ),
        Err(ClassificationError::IncompleteCoverage { .. })
    ));
    for (jurisdiction, operation) in [
        (qi("sc.region"), QualIdent::simple("entity.incorporate")),
        (QualIdent::simple("sc.region"), qi("entity.incorporate")),
    ] {
        assert_eq!(jurisdiction.to_dotted(), "sc.region");
        assert_eq!(operation.to_dotted(), "entity.incorporate");
        assert!(matches!(
            classified.resolve(
                &purpose("Entity.Incorporate"),
                &artifact("executable-a"),
                &jurisdiction,
                &operation,
                &verifier,
            ),
            Err(ClassificationError::InvalidResolutionScope { .. })
        ));
    }
}

#[test]
fn malformed_base_scopes_cannot_become_invisible_classified_rules() {
    let (classified, _) = classified();
    let original = serde_json::to_value(&classified).unwrap();
    let invalid_scopes = [
        AppliesTo {
            jurisdictions: vec![],
            operation_kinds: vec![OperationKindScope::All],
        },
        AppliesTo {
            jurisdictions: vec![JurisdictionScope::All],
            operation_kinds: vec![],
        },
        AppliesTo {
            jurisdictions: vec![JurisdictionScope::Specific(QualIdent::simple("sc.region"))],
            operation_kinds: vec![OperationKindScope::All],
        },
        AppliesTo {
            jurisdictions: vec![JurisdictionScope::All],
            operation_kinds: vec![OperationKindScope::Specific(QualIdent::simple(
                "entity.incorporate",
            ))],
        },
        AppliesTo {
            jurisdictions: vec![JurisdictionScope::All],
            operation_kinds: vec![OperationKindScope::Family(qi("entity.subfamily"))],
        },
        AppliesTo {
            jurisdictions: vec![JurisdictionScope::All],
            operation_kinds: vec![OperationKindScope::Family(qi(""))],
        },
    ];
    for scope in invalid_scopes {
        let mut base = classified.pack().clone();
        base.rules[2].applies_to = scope.clone();
        assert!(matches!(
            ClassifiedPackV2::new(base, classified.classifications().to_vec()),
            Err(ClassificationError::InvalidPackRuleScope { .. })
        ));
        let mut wire = original.clone();
        wire["pack"]["rules"][2]["applies_to"] = serde_json::to_value(scope).unwrap();
        assert!(serde_json::from_value::<ClassifiedPackV2>(wire).is_err());
    }
}

#[test]
fn verified_resolution_returns_every_applicable_rule_in_base_pack_order() {
    let (classified, verifier) = classified();
    let wire = serde_json::to_vec(&classified).unwrap();
    let decoded: ClassifiedPackV2 = serde_json::from_slice(&wire).unwrap();
    for (jurisdiction, expected) in [
        ("sc", vec!["sc_selected", "sc_blocking"]),
        ("de", vec!["de_selected"]),
    ] {
        let rules = decoded
            .resolve(
                &purpose("Entity.Incorporate"),
                &artifact("executable-a"),
                &qi(jurisdiction),
                &qi("entity.incorporate"),
                &verifier,
            )
            .unwrap();
        assert_eq!(
            rules
                .iter()
                .map(|rule| rule.name.as_str())
                .collect::<Vec<_>>(),
            expected
        );
    }
    assert_eq!(
        serde_json::to_vec(decoded.pack()).unwrap(),
        serde_json::to_vec(classified.pack()).unwrap()
    );
}

#[test]
fn artifact_classifications_cannot_borrow_coverage_from_each_other() {
    let (base, mut verifier) = signed_base();
    let entries = vec![
        entry(&base, &[0, 2]),
        PurposeClassificationV1::new(
            purpose("Entity.Incorporate"),
            artifact("executable-b"),
            vec![rule_digest(&base, 1)],
        )
        .unwrap(),
    ];
    let classified = sign_outer(ClassifiedPackV2::new(base, entries).unwrap(), &mut verifier);
    for (executable, jurisdiction, expected) in [
        ("executable-a", "sc", vec!["sc_selected", "sc_blocking"]),
        ("executable-b", "de", vec!["de_selected"]),
    ] {
        let rules = classified
            .resolve(
                &purpose("Entity.Incorporate"),
                &artifact(executable),
                &qi(jurisdiction),
                &qi("entity.incorporate"),
                &verifier,
            )
            .unwrap();
        assert_eq!(
            rules
                .iter()
                .map(|rule| rule.name.as_str())
                .collect::<Vec<_>>(),
            expected
        );
    }
    for (executable, jurisdiction) in [("executable-a", "de"), ("executable-b", "sc")] {
        assert!(matches!(
            classified.resolve(
                &purpose("Entity.Incorporate"),
                &artifact(executable),
                &qi(jurisdiction),
                &qi("entity.incorporate"),
                &verifier,
            ),
            Err(ClassificationError::IncompleteCoverage { .. })
        ));
    }
}

#[test]
fn classification_need_not_reference_rules_from_other_scopes() {
    let mut other_operation = rule("sc_dissolve", "sc", "NonCompliant");
    other_operation.applies_to.as_mut().unwrap().operation_kinds =
        vec![OperationKindScope::Specific(qi("entity.dissolve"))];
    let (base, mut verifier) = signed_rules(vec![
        rule("sc_selected", "sc", "Compliant"),
        rule("de_selected", "de", "Pending"),
        other_operation,
    ]);
    let classification = entry(&base, &[0]);
    let classified = sign_outer(
        ClassifiedPackV2::new(base, vec![classification]).unwrap(),
        &mut verifier,
    );
    let rules = classified
        .resolve(
            &purpose("Entity.Incorporate"),
            &artifact("executable-a"),
            &qi("sc"),
            &qi("entity.incorporate"),
            &verifier,
        )
        .unwrap();
    assert_eq!(
        rules
            .iter()
            .map(|rule| rule.name.as_str())
            .collect::<Vec<_>>(),
        ["sc_selected"]
    );
}

#[test]
fn resolution_refuses_unknown_purpose_wrong_artifact_and_non_applicable_scope() {
    let (classified, verifier) = classified();
    let resolve = |tag: &str, digest: ContentDigest, jurisdiction: &str, operation: &str| {
        classified.resolve(
            &purpose(tag),
            &digest,
            &qi(jurisdiction),
            &qi(operation),
            &verifier,
        )
    };
    assert!(matches!(
        resolve(
            "entity.incorporate",
            artifact("executable-a"),
            "sc",
            "entity.incorporate"
        ),
        Err(ClassificationError::UnknownPurpose { .. })
    ));
    for digest in [
        artifact("executable-b"),
        ContentDigest::from_poseidon2_bytes(*artifact("executable-a").as_bytes()),
    ] {
        assert!(matches!(
            resolve("Entity.Incorporate", digest, "sc", "entity.incorporate"),
            Err(ClassificationError::WrongArtifact { .. })
        ));
    }
    for (jurisdiction, operation) in [("uk", "entity.incorporate"), ("sc", "entity.dissolve")] {
        assert!(matches!(
            resolve(
                "Entity.Incorporate",
                artifact("executable-a"),
                jurisdiction,
                operation
            ),
            Err(ClassificationError::NoApplicableRules { .. })
        ));
    }
    for (jurisdiction, operation) in [("", "entity.incorporate"), ("sc", "*")] {
        assert!(matches!(
            resolve(
                "Entity.Incorporate",
                artifact("executable-a"),
                jurisdiction,
                operation
            ),
            Err(ClassificationError::InvalidResolutionScope { .. })
        ));
    }
}

#[test]
fn classification_construction_rejects_empty_unknown_and_ambiguous_references() {
    let (pack, _) = signed_base();
    assert!(matches!(
        PurposeClassificationV1::new(
            purpose("Entity.Incorporate"),
            artifact("executable-a"),
            vec![]
        ),
        Err(ClassificationError::EmptyRuleReferences)
    ));
    assert!(matches!(
        PurposeClassificationV1::new(
            purpose("Entity.Incorporate"),
            artifact("executable-a"),
            vec![rule_digest(&pack, 0); 2],
        ),
        Err(ClassificationError::DuplicateRuleReference { .. })
    ));
    let unknown = PurposeClassificationV1::new(
        purpose("Entity.Incorporate"),
        artifact("executable-a"),
        vec![artifact("unknown-rule")],
    )
    .unwrap();
    assert!(matches!(
        ClassifiedPackV2::new(pack.clone(), vec![unknown]),
        Err(ClassificationError::UnknownRuleReference { .. })
    ));
    let wrong_algorithm = PurposeClassificationV1::new(
        purpose("Entity.Incorporate"),
        artifact("executable-a"),
        vec![ContentDigest::from_poseidon2_bytes(
            *rule_digest(&pack, 0).as_bytes(),
        )],
    )
    .unwrap();
    assert!(matches!(
        ClassifiedPackV2::new(pack.clone(), vec![wrong_algorithm]),
        Err(ClassificationError::UnknownRuleReference { .. })
    ));
    assert!(matches!(
        ClassifiedPackV2::new(pack.clone(), vec![]),
        Err(ClassificationError::EmptyClassifications)
    ));
    for second in [entry(&pack, &[0]), entry(&pack, &[2])] {
        assert!(matches!(
            ClassifiedPackV2::new(pack.clone(), vec![entry(&pack, &[0]), second]),
            Err(ClassificationError::DuplicateClassification { .. })
        ));
    }
    let mut ambiguous = pack.clone();
    ambiguous.rules.push(pack.rules[0].clone());
    assert!(matches!(
        ClassifiedPackV2::new(ambiguous, vec![entry(&pack, &[0])]),
        Err(ClassificationError::DuplicatePackRule { .. })
    ));
    for invalid_hash in ["invalid".into(), "é".repeat(32)] {
        let mut invalid = pack.clone();
        invalid.rules[0].rule_hash = invalid_hash;
        assert!(matches!(
            ClassifiedPackV2::new(invalid, vec![entry(&pack, &[0])]),
            Err(ClassificationError::InvalidPackRuleHash { .. })
        ));
    }
}

#[test]
fn serde_requires_explicit_versions_metadata_and_valid_references_without_legacy_fallback() {
    let (classified, _) = classified();
    let original = serde_json::to_value(&classified).unwrap();
    let edits: &[(&str, Value)] = &[
        ("/version", json!(1)),
        ("/version", json!(3)),
        ("/classifications/0/version", json!(0)),
        ("/classifications/0/version", json!(2)),
        ("/classifications/0/purpose", json!("Entity.*")),
        ("/classifications/0/purpose", Value::Null),
        ("/classifications/0/executable_digest", Value::Null),
        ("/classifications/0/rule_hashes", json!([])),
        ("/classifications/0/rule_hashes", json!(["unknown"])),
        (
            "/classifications/0/rule_hashes",
            json!([artifact("unknown-rule")]),
        ),
        (
            "/classifications/0/rule_hashes",
            json!(vec![rule_digest(classified.pack(), 0); 2]),
        ),
        ("/classifications", json!([])),
        (
            "/classifications",
            json!(vec![classified.classifications()[0].clone(); 2]),
        ),
    ];
    for (path, replacement) in edits {
        let mut wire = original.clone();
        *wire.pointer_mut(path).unwrap() = replacement.clone();
        assert!(
            serde_json::from_value::<ClassifiedPackV2>(wire).is_err(),
            "accepted {path} = {replacement}"
        );
    }
    for path in ["", "/classifications/0"] {
        for key in ["version", "purpose"] {
            if path.is_empty() && key == "purpose" {
                continue;
            }
            let mut wire = original.clone();
            wire.pointer_mut(path)
                .unwrap()
                .as_object_mut()
                .unwrap()
                .remove(key);
            assert!(serde_json::from_value::<ClassifiedPackV2>(wire).is_err());
        }
        let mut wire = original.clone();
        wire.pointer_mut(path)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .insert("unbound_metadata".into(), json!(true));
        assert!(serde_json::from_value::<ClassifiedPackV2>(wire).is_err());
    }
    assert!(serde_json::from_value::<ClassifiedPackV2>(
        serde_json::to_value(classified.pack()).unwrap()
    )
    .is_err());
}

#[test]
fn classification_tampering_cannot_reuse_the_recorded_digest_or_signature() {
    let (classified, verifier) = classified();
    let original = serde_json::to_value(&classified).unwrap();
    let edits = [
        ("/classifications/0/purpose", json!("Entity.Dissolve")),
        (
            "/classifications/0/executable_digest",
            json!(artifact("executable-b")),
        ),
        (
            "/classifications/0/rule_hashes",
            json!([rule_digest(classified.pack(), 2)]),
        ),
    ];
    for (path, replacement) in edits {
        let mut wire = original.clone();
        *wire.pointer_mut(path).unwrap() = replacement;
        let tampered: ClassifiedPackV2 = serde_json::from_value(wire).unwrap();
        assert!(matches!(
            tampered.verify(&verifier),
            Err(ClassificationError::DigestMismatch { .. })
        ));

        let rehashed =
            ClassifiedPackV2::new(tampered.pack().clone(), tampered.classifications().to_vec())
                .unwrap()
                .with_signature(signature("22"));
        assert!(matches!(
            rehashed.verify(&verifier),
            Err(ClassificationError::SignatureRejected(_))
        ));
        assert!(rehashed
            .resolve(
                tampered.classifications()[0].purpose(),
                tampered.classifications()[0].executable_digest(),
                &qi("sc"),
                &qi("entity.incorporate"),
                &verifier,
            )
            .is_err());
    }
}

#[test]
fn outer_signature_cannot_launder_unsigned_tampered_or_rejected_base_packs() {
    let (pack, verifier) = signed_base();
    for failure in ["unsigned", "tampered", "rejected"] {
        let mut base = pack.clone();
        match failure {
            "unsigned" => base.signature = None,
            "tampered" => base.rules[0].legal_basis = "Changed law".into(),
            "rejected" => base.signature = Some(signature("33")),
            _ => unreachable!(),
        }
        let mut accepting_outer = BoundVerifier(verifier.0.clone());
        let outer = ClassifiedPackV2::new(base, vec![entry(&pack, &[0])]).unwrap();
        let outer = sign_outer(outer, &mut accepting_outer);
        let error = outer.verify(&accepting_outer).unwrap_err();
        match failure {
            "unsigned" => assert!(matches!(
                error,
                ClassificationError::BasePack(PackVerifyError::Unsigned)
            )),
            "tampered" => assert!(matches!(
                error,
                ClassificationError::BasePack(PackVerifyError::DigestMismatch { .. })
            )),
            "rejected" => assert!(matches!(
                error,
                ClassificationError::BasePack(PackVerifyError::SignatureRejected(_))
            )),
            _ => unreachable!(),
        }
    }
}

#[test]
fn unsigned_outer_or_wrong_curator_signature_cannot_resolve() {
    let (base, mut verifier) = signed_base();
    let outer = ClassifiedPackV2::new(base.clone(), vec![entry(&base, &[0])]).unwrap();
    assert!(matches!(
        outer.verify(&verifier),
        Err(ClassificationError::Unsigned)
    ));
    let sig = signature("22");
    verifier.register("did:example:other", &outer.digest().to_hex(), &sig);
    let outer = outer.with_signature(sig);
    assert!(matches!(
        outer.verify(&verifier),
        Err(ClassificationError::SignatureRejected(_))
    ));
}

#[test]
fn classification_preimage_has_a_domain_and_covers_the_complete_base_pack() {
    let (classified, _) = classified();
    let expected = json!({
        "domain": "lex.classified_pack.v2",
        "version": 2,
        "pack": classified.pack(),
        "classifications": classified.classifications(),
    });
    assert_eq!(
        *classified.digest(),
        sha256_digest(&CanonicalBytes::new(&expected).unwrap())
    );

    let mut changed_base = classified.pack().clone();
    changed_base.signature = Some(signature("44"));
    let changed =
        ClassifiedPackV2::new(changed_base, classified.classifications().to_vec()).unwrap();
    assert_ne!(changed.digest(), classified.digest());
}

#[test]
fn historical_pack_serialization_and_digest_preimages_remain_fixed() {
    let cases = [
        (
            "0.1.0",
            "64f91918dfa8d3c2d12e9ed32bae670e232fefcfc00bf2b89220f748eb20e7ae",
            r#"{"version":{"curator_did":"did:example:curator","semver":"0.1.0","content_digest":"64f91918dfa8d3c2d12e9ed32bae670e232fefcfc00bf2b89220f748eb20e7ae"},"digest":"64f91918dfa8d3c2d12e9ed32bae670e232fefcfc00bf2b89220f748eb20e7ae","signature":null,"rules":[{"rule_hash":"f92555dbca7bdeca470f5af60e7276ce7720857108b5ff5cc0c9ef78dc772389","applies_to":{"jurisdictions":[{"Specific":{"segments":["sc"]}}],"operation_kinds":[{"Specific":{"segments":["entity","incorporate"]}}]},"name":"one","legal_basis":"Example law","body":{"term":{"Constant":{"segments":["Compliant"]}},"term_hash":"f92555dbca7bdeca470f5af60e7276ce7720857108b5ff5cc0c9ef78dc772389"},"obligations":[]}]}"#,
        ),
        (
            "1.0.0",
            "a25364a0a3e2f13abeac073e150b2fcb2961f456eb79e262b10fdcb0324d511d",
            r#"{"version":{"curator_did":"did:example:curator","semver":"1.0.0","content_digest":"a25364a0a3e2f13abeac073e150b2fcb2961f456eb79e262b10fdcb0324d511d"},"digest":"a25364a0a3e2f13abeac073e150b2fcb2961f456eb79e262b10fdcb0324d511d","signature":null,"rules":[{"rule_hash":"f92555dbca7bdeca470f5af60e7276ce7720857108b5ff5cc0c9ef78dc772389","applies_to":{"jurisdictions":[{"Specific":{"segments":["sc"]}}],"operation_kinds":[{"Specific":{"segments":["entity","incorporate"]}}]},"name":"one","legal_basis":"Example law","body":{"term":{"Constant":{"segments":["Compliant"]}},"term_hash":"f92555dbca7bdeca470f5af60e7276ce7720857108b5ff5cc0c9ef78dc772389"},"obligations":[]}]}"#,
        ),
    ];
    for (semver, digest, wire) in cases {
        let pack = compile(CURATOR, semver, [rule("one", "sc", "Compliant")]).unwrap();
        assert_eq!(pack.digest, digest);
        assert_eq!(serde_json::to_string(&pack).unwrap(), wire);
        let decoded: Pack = serde_json::from_str(wire).unwrap();
        assert_eq!(decoded, pack);
    }
}
