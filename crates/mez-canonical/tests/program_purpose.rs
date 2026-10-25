use mez_canonical::{CanonicalBytes, ProgramPurposeTag, ProgramPurposeTagError};
use serde::{Deserialize, Deserializer};

// This adapter models scalar coercion when a format receives a string type hint.
struct StringFormat {
    value: serde_json::Value,
    human_readable: bool,
}

impl<'de> Deserializer<'de> for StringFormat {
    type Error = serde_json::Error;

    fn deserialize_any<V: serde::de::Visitor<'de>>(
        self,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        if self.human_readable {
            self.value.deserialize_any(visitor)
        } else {
            Err(serde::de::Error::custom(
                "this format requires a string schema",
            ))
        }
    }

    fn deserialize_string<V: serde::de::Visitor<'de>>(
        self,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        match self.value {
            serde_json::Value::String(value) => visitor.visit_string(value),
            other if self.human_readable => visitor.visit_string(other.to_string()),
            _ => Err(serde::de::Error::custom("expected an encoded string")),
        }
    }

    fn is_human_readable(&self) -> bool {
        self.human_readable
    }

    serde::forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str bytes byte_buf
        option unit unit_struct newtype_struct seq tuple tuple_struct map struct enum identifier ignored_any
    }
}

#[test]
fn human_readable_scalar_coercion_cannot_turn_other_kinds_into_purpose_strings() {
    for value in [
        serde_json::Value::Null,
        serde_json::json!(true),
        serde_json::json!(42),
    ] {
        assert!(ProgramPurposeTag::deserialize(StringFormat {
            value,
            human_readable: true,
        })
        .is_err());
    }
}

#[test]
fn schema_directed_string_formats_keep_validation_and_exact_bytes() {
    for human_readable in [true, false] {
        let tag = ProgramPurposeTag::deserialize(StringFormat {
            value: serde_json::json!("Entity.Incorporate"),
            human_readable,
        })
        .unwrap();
        assert_eq!(
            CanonicalBytes::new(&tag).unwrap().as_bytes(),
            br#""Entity.Incorporate""#
        );
        assert!(ProgramPurposeTag::deserialize(StringFormat {
            value: serde_json::json!("Entity.*"),
            human_readable,
        })
        .is_err());
    }
}

#[test]
fn accepted_tags_preserve_exact_wire_and_canonical_bytes() {
    let cases: &[(&str, &[u8])] = &[
        ("US.RegD_506c", br#""US.RegD_506c""#),
        ("us.regd_506c", br#""us.regd_506c""#),
        ("_", br#""_""#),
        ("a0._B1.C", br#""a0._B1.C""#),
    ];

    for &(input, expected) in cases {
        let constructed = ProgramPurposeTag::new(input).unwrap();
        let decoded: ProgramPurposeTag = serde_json::from_slice(expected).unwrap();
        for tag in [constructed, decoded] {
            assert_eq!(tag.as_str(), input);
            assert_eq!(tag.to_string(), input);
            assert_eq!(serde_json::to_vec(&tag).unwrap(), expected);
            assert_eq!(CanonicalBytes::new(&tag).unwrap().as_bytes(), expected);
        }
    }
}

#[test]
fn malformed_identifiers_are_rejected_at_constructor_and_serde_ingress() {
    use ProgramPurposeTagError::{Empty, InvalidSegment};

    let cases = [
        ("", Empty),
        (".purpose", InvalidSegment { index: 0 }),
        ("purpose.", InvalidSegment { index: 1 }),
        ("a..b", InvalidSegment { index: 1 }),
        ("1purpose", InvalidSegment { index: 0 }),
        ("a.1purpose", InvalidSegment { index: 1 }),
        (" purpose", InvalidSegment { index: 0 }),
        ("purpose ", InvalidSegment { index: 0 }),
        ("pur pose", InvalidSegment { index: 0 }),
        ("purpose\n", InvalidSegment { index: 0 }),
        ("a.\tb", InvalidSegment { index: 1 }),
        ("purpose.*", InvalidSegment { index: 1 }),
        ("purpose.under-score", InvalidSegment { index: 1 }),
        ("purpose/child", InvalidSegment { index: 0 }),
        ("purpöse", InvalidSegment { index: 0 }),
        ("purpose.\0", InvalidSegment { index: 1 }),
    ];

    for (input, expected) in cases {
        assert_eq!(ProgramPurposeTag::new(input), Err(expected), "{input:?}");
        let wire = serde_json::to_string(input).unwrap();
        assert!(
            serde_json::from_str::<ProgramPurposeTag>(&wire).is_err(),
            "serde accepted {input:?}"
        );
    }
}

#[test]
fn complete_identifier_has_a_255_byte_limit_including_dots() {
    let accepted = [
        "a".repeat(255),
        format!("{}.{}", "a".repeat(127), "B".repeat(127)),
    ];
    for input in accepted {
        let wire = serde_json::to_string(&input).unwrap();
        assert!(ProgramPurposeTag::new(&input).is_ok());
        assert!(serde_json::from_str::<ProgramPurposeTag>(&wire).is_ok());
    }

    let rejected = [
        "a".repeat(256),
        format!("{}.{}", "a".repeat(128), "B".repeat(127)),
    ];
    for input in rejected {
        let wire = serde_json::to_string(&input).unwrap();
        assert_eq!(
            ProgramPurposeTag::new(input),
            Err(ProgramPurposeTagError::TooLong { actual: 256 })
        );
        assert!(serde_json::from_str::<ProgramPurposeTag>(&wire).is_err());
    }
}

#[test]
fn serde_rejects_non_string_wire_values() {
    for wire in [
        "null",
        "true",
        "12",
        "1.5",
        "[]",
        r#"["purpose"]"#,
        r#"{"purpose":"a"}"#,
    ] {
        assert!(
            serde_json::from_str::<ProgramPurposeTag>(wire).is_err(),
            "serde accepted {wire}"
        );
    }
}

#[test]
fn string_conversions_validate_before_exposing_a_tag() {
    let expected = ProgramPurposeTagError::InvalidSegment { index: 1 };
    assert_eq!(
        "valid.*".parse::<ProgramPurposeTag>(),
        Err(expected.clone())
    );
    assert_eq!(
        ProgramPurposeTag::try_from("valid.*"),
        Err(expected.clone())
    );
    assert_eq!(
        ProgramPurposeTag::try_from(String::from("valid.*")),
        Err(expected)
    );
}

#[cfg(feature = "openapi")]
#[test]
fn openapi_exposes_the_constrained_string_wire_contract() {
    let (_, schema) = <ProgramPurposeTag as utoipa::ToSchema>::schema();
    let schema = serde_json::to_value(schema).unwrap();
    assert_eq!(schema["type"], "string");
    assert_eq!(schema["minLength"], 1);
    assert_eq!(schema["maxLength"], 255);
    assert_eq!(
        schema["pattern"],
        r"^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*(?![\s\S])"
    );
    assert!(schema.get("default").is_none());
}
