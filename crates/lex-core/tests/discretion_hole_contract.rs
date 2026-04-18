use std::fs;
use std::path::PathBuf;

use lex_core::ast::Term;
use lex_core::elaborate;
use lex_core::lexer;
use lex_core::parser;
use lex_core::prelude::compliance_prelude;
use lex_core::typecheck::{infer, AdmissibilityViolation, TypeError};

fn load_example(name: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(name);
    fs::read_to_string(path).expect("example file should load")
}

#[test]
fn surface_hole_example_is_preserved_then_rejected_by_main_checker() {
    let source = load_example("discretion-hole-frontier.lex");
    let tokens = lexer::lex(&source).expect("lexing should succeed");
    let parsed = parser::parse(&tokens).expect("parsing should succeed");
    let ctx = compliance_prelude();
    let elaborated = elaborate::elaborate(&parsed, &ctx).expect("elaboration should succeed");

    match &elaborated {
        Term::Hole(hole) => {
            assert_eq!(
                hole.name.as_ref().map(|name| name.name.as_str()),
                Some("fit_and_proper")
            );
        }
        other => panic!("expected Term::Hole after elaboration, found {other:?}"),
    }

    match infer(&ctx, &elaborated).expect_err("main checker should reject holes") {
        TypeError::Admissibility {
            violation: AdmissibilityViolation::UnfilledHole,
            term: Term::Hole(hole),
        } => {
            assert_eq!(
                hole.name.as_ref().map(|name| name.name.as_str()),
                Some("fit_and_proper")
            );
        }
        other => panic!("expected UnfilledHole admissibility error, found {other:?}"),
    }
}

#[test]
fn surface_fill_example_is_preserved_then_rejected_by_main_checker() {
    let source = load_example("discretion-hole-fill-frontier.lex");
    let tokens = lexer::lex(&source).expect("lexing should succeed");
    let parsed = parser::parse(&tokens).expect("parsing should succeed");
    let ctx = compliance_prelude();
    let elaborated = elaborate::elaborate(&parsed, &ctx).expect("elaboration should succeed");

    match &elaborated {
        Term::HoleFill { hole_name, .. } => {
            assert_eq!(
                hole_name.as_ref().map(|name| name.name.as_str()),
                Some("fit_and_proper")
            );
        }
        other => panic!("expected Term::HoleFill after elaboration, found {other:?}"),
    }

    match infer(&ctx, &elaborated).expect_err("main checker should reject fill forms") {
        TypeError::Admissibility {
            violation: AdmissibilityViolation::HoleFillNotSupported,
            term: Term::HoleFill { hole_name, .. },
        } => {
            assert_eq!(
                hole_name.as_ref().map(|name| name.name.as_str()),
                Some("fit_and_proper")
            );
        }
        other => panic!("expected HoleFillNotSupported admissibility error, found {other:?}"),
    }
}
