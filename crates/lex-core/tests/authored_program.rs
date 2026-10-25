use lex_core::{elaborate, prelude, typecheck, AuthoredLexProgramError, AuthoredLexProgramV1};
use mez_canonical::ProgramPurposeTag;
use serde::{Deserialize, Deserializer};
use serde_json::json;

struct SchemaDirectedStruct(serde_json::Value);

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

#[test]
fn positional_json_arrays_cannot_replace_authored_program_objects() {
    let decoded =
        serde_json::from_str::<AuthoredLexProgramV1>(r#"[1,"Entity.Incorporate","Pending"]"#);
    let parses = decoded
        .as_ref()
        .is_ok_and(|program| program.parse().is_ok());
    assert!(
        decoded.is_err(),
        "positional array accepted, parses={parses}"
    );
}

#[test]
fn authored_program_objects_reject_duplicate_fields_without_collecting_them() {
    for wire in [
        r#"{"version":1,"version":1,"purpose":"Entity.Incorporate","source":"Pending"}"#,
        r#"{"version":1,"purpose":"Entity.Incorporate","purpose":"Entity.Incorporate","source":"Pending"}"#,
        r#"{"version":1,"purpose":"Entity.Incorporate","source":"Pending","source":"Pending"}"#,
    ] {
        assert!(serde_json::from_str::<AuthoredLexProgramV1>(wire).is_err());
    }
}

#[test]
fn schema_directed_authored_programs_keep_field_order_and_version_validation() {
    let decoded = AuthoredLexProgramV1::deserialize(SchemaDirectedStruct(json!([
        1,
        "Entity.Incorporate",
        "Pending"
    ])))
    .unwrap();
    assert_eq!(
        serde_json::to_value(&decoded).unwrap(),
        json!({"version": 1, "purpose": "Entity.Incorporate", "source": "Pending"})
    );
    assert!(decoded.parse().is_ok());
    assert!(
        AuthoredLexProgramV1::deserialize(SchemaDirectedStruct(json!([
            2,
            "Entity.Incorporate",
            "Pending"
        ])))
        .is_err()
    );
}

#[test]
fn authored_program_preserves_purpose_and_source_through_the_real_parser() {
    let source =
        "  -- purpose stays outside the term\n lambda (ctx : IncorporationContext). Pending \n";
    let wire = json!({"version": 1, "purpose": "Entity.Incorporate", "source": source});
    let authored: AuthoredLexProgramV1 = serde_json::from_value(wire.clone()).unwrap();
    let parsed = authored.parse().unwrap();
    assert_eq!(parsed.purpose().as_str(), "Entity.Incorporate");
    assert_eq!(parsed.source().as_bytes(), source.as_bytes());
    assert_eq!(serde_json::to_value(parsed.authored()).unwrap(), wire);

    let context = prelude::structural_prelude();
    let elaborated = elaborate::elaborate(parsed.term(), &context).unwrap();
    typecheck::check(
        &context,
        &elaborated,
        &lex_core::ast::Term::pi(
            "ctx",
            lex_core::ast::Term::constant("IncorporationContext"),
            lex_core::ast::Term::constant("ComplianceVerdict"),
        ),
    )
    .unwrap();
}

#[test]
fn authored_envelope_requires_explicit_supported_metadata() {
    for wire in [
        json!({"version": 1, "source": "-- purpose: Entity.Incorporate\nPending"}),
        json!({"purpose": "Entity.Incorporate", "source": "Pending"}),
        json!({"version": 0, "purpose": "Entity.Incorporate", "source": "Pending"}),
        json!({"version": 2, "purpose": "Entity.Incorporate", "source": "Pending"}),
        json!({"version": "1", "purpose": "Entity.Incorporate", "source": "Pending"}),
        json!({"version": 1, "purpose": "Entity.*", "source": "Pending"}),
        json!({"version": 1, "purpose": " Entity.Incorporate", "source": "Pending"}),
        json!({"version": 1, "purpose": null, "source": "Pending"}),
        json!({"version": 1, "purpose": "Entity.Incorporate"}),
        json!({"version": 1, "purpose": "Entity.Incorporate", "source": "Pending", "admitted": true}),
        json!({"Constant": {"segments": ["Pending"]}}),
    ] {
        assert!(
            serde_json::from_value::<AuthoredLexProgramV1>(wire.clone()).is_err(),
            "accepted {wire}"
        );
    }
}

#[test]
fn parsing_errors_remain_errors_and_success_is_not_admission() {
    let purpose = ProgramPurposeTag::new("Entity.Incorporate").unwrap();
    assert!(matches!(
        AuthoredLexProgramV1::new(purpose.clone(), "💥").parse(),
        Err(AuthoredLexProgramError::Lex(_))
    ));
    assert!(matches!(
        AuthoredLexProgramV1::new(purpose.clone(), "lambda :").parse(),
        Err(AuthoredLexProgramError::Parse(_))
    ));

    let parsed = AuthoredLexProgramV1::new(purpose, "? review : Prop @ regulator")
        .parse()
        .unwrap();
    assert!(typecheck::check_admissibility(parsed.term()).is_err());
}

#[test]
fn authored_program_rejects_additional_top_level_terms_without_changing_legacy_parse() {
    let source = "Pending end NonCompliant";
    let tokens = lex_core::lexer::lex(source).unwrap();
    assert!(lex_core::parser::parse(&tokens).is_ok());
    assert!(lex_core::parser::parse_single_term(&tokens).is_err());
    assert!(matches!(
        AuthoredLexProgramV1::new(
            ProgramPurposeTag::new("Entity.Incorporate").unwrap(),
            source
        )
        .parse(),
        Err(AuthoredLexProgramError::Parse(_))
    ));

    let mut tokens = lex_core::lexer::lex("Pending").unwrap();
    tokens.extend(lex_core::lexer::lex("NonCompliant").unwrap());
    assert!(lex_core::parser::parse_single_term(&tokens).is_err());
}
