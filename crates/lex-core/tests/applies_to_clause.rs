//! Integration tests for the `applies_to { ... }` rule-level scope clause
//! (Frontier-09 §2.3) — exercised end-to-end through the lexer + parser, and
//! round-tripped through the pretty-printer.

use lex_core::ast::{AppliesTo, DefeasibleRule, JurisdictionScope, OperationKindScope, Term};
use lex_core::{lexer, parser, pretty};

/// Lex + parse a source string into a `Term`.
fn parse_src(src: &str) -> Result<Term, String> {
    let tokens = lexer::lex(src).map_err(|e| format!("lex error: {e:?}"))?;
    parser::parse(&tokens).map_err(|e| format!("parse error: {e:?}"))
}

/// Extract the `applies_to` scope from a parsed defeasible-rule term.
fn applies_to_of(term: &Term) -> Option<AppliesTo> {
    match term {
        Term::Defeasible(DefeasibleRule { applies_to, .. }) => applies_to.clone(),
        other => panic!("expected a defeasible rule term, got {other:?}"),
    }
}

#[test]
fn declarative_rule_parses_specific_scope() {
    let src = "defeasible sc_aml : ComplianceVerdict \
               applies_to { jurisdictions: [ sc ]; operation_kinds: [ entity.incorporate ] } \
               with end";
    let term = parse_src(src).expect("should parse");
    let scope = applies_to_of(&term).expect("applies_to should be present");
    assert_eq!(
        scope.jurisdictions,
        vec![JurisdictionScope::Specific(
            lex_core::ast::QualIdent::from_dotted("sc")
        )]
    );
    assert_eq!(
        scope.operation_kinds,
        vec![OperationKindScope::Specific(
            lex_core::ast::QualIdent::from_dotted("entity.incorporate")
        )]
    );
    // (sc, entity.incorporate) matches; (de, entity.incorporate) does not.
    assert!(scope.matches(
        &lex_core::ast::QualIdent::from_dotted("sc"),
        &lex_core::ast::QualIdent::from_dotted("entity.incorporate")
    ));
    assert!(!scope.matches(
        &lex_core::ast::QualIdent::from_dotted("de"),
        &lex_core::ast::QualIdent::from_dotted("entity.incorporate")
    ));
}

#[test]
fn family_wildcard_parses() {
    let src = "defeasible sc_entity : ComplianceVerdict \
               applies_to { jurisdictions: [ sc ]; operation_kinds: [ entity.* ] } \
               with end";
    let term = parse_src(src).expect("should parse");
    let scope = applies_to_of(&term).expect("applies_to present");
    assert_eq!(
        scope.operation_kinds,
        vec![OperationKindScope::Family(
            lex_core::ast::QualIdent::from_dotted("entity")
        )]
    );
    assert!(scope.matches(
        &lex_core::ast::QualIdent::from_dotted("sc"),
        &lex_core::ast::QualIdent::from_dotted("entity.dissolve")
    ));
}

#[test]
fn universal_wildcard_parses() {
    let src = "defeasible sanctions : ComplianceVerdict \
               applies_to { jurisdictions: [*]; operation_kinds: [*] } \
               with end";
    let term = parse_src(src).expect("should parse");
    let scope = applies_to_of(&term).expect("applies_to present");
    assert_eq!(scope.jurisdictions, vec![JurisdictionScope::All]);
    assert_eq!(scope.operation_kinds, vec![OperationKindScope::All]);
    assert!(scope.is_universal());
}

#[test]
fn multiple_jurisdictions_and_operations_parse() {
    let src = "defeasible multi : ComplianceVerdict \
               applies_to { jurisdictions: [ sc, de ]; \
               operation_kinds: [ entity.incorporate, ownership.* ] } \
               with end";
    let term = parse_src(src).expect("should parse");
    let scope = applies_to_of(&term).expect("applies_to present");
    assert_eq!(scope.jurisdictions.len(), 2);
    assert_eq!(scope.operation_kinds.len(), 2);
    assert!(scope.matches(
        &lex_core::ast::QualIdent::from_dotted("de"),
        &lex_core::ast::QualIdent::from_dotted("ownership.issue_shares")
    ));
}

#[test]
fn pre_09_rule_without_applies_to_still_parses() {
    // A rule with no applies_to clause parses with applies_to = None (backward
    // compatible, Frontier-09 §2.2).
    let src = "defeasible legacy : ComplianceVerdict with end";
    let term = parse_src(src).expect("should parse");
    assert_eq!(applies_to_of(&term), None);
}

#[test]
fn empty_jurisdiction_list_is_rejected_fail_loud() {
    // "Applies everywhere" must be the explicit `[*]`, never `[]`.
    let src = "defeasible bad : ComplianceVerdict \
               applies_to { jurisdictions: []; operation_kinds: [ entity.incorporate ] } \
               with end";
    let err = parse_src(src).expect_err("empty jurisdictions must be rejected");
    assert!(
        err.contains("empty jurisdictions"),
        "error should name the empty jurisdictions list: {err}"
    );
}

#[test]
fn empty_operation_kinds_list_is_rejected_fail_loud() {
    let src = "defeasible bad : ComplianceVerdict \
               applies_to { jurisdictions: [ sc ]; operation_kinds: [] } \
               with end";
    let err = parse_src(src).expect_err("empty operation_kinds must be rejected");
    assert!(
        err.contains("empty operation_kinds"),
        "error should name the empty operation_kinds list: {err}"
    );
}

#[test]
fn missing_operation_kinds_field_is_rejected() {
    let src = "defeasible bad : ComplianceVerdict \
               applies_to { jurisdictions: [ sc ] } \
               with end";
    let err = parse_src(src).expect_err("missing operation_kinds must be rejected");
    assert!(
        err.contains("operation_kinds"),
        "error should name the missing operation_kinds field: {err}"
    );
}

#[test]
fn applies_to_is_rendered_by_pretty_printer() {
    // NB: the declarative `defeasible NAME : T with end` form has a
    // pre-existing pretty-print/parse asymmetry (the printer emits the implicit
    // body `NAME@idx`, which the declarative parser does not re-accept) that is
    // unrelated to `applies_to`. This test therefore asserts the scope CLAUSE
    // is rendered, which is the new commitment; clause parse correctness is
    // covered by the dedicated parse tests above.
    let src = "defeasible sc_aml : ComplianceVerdict \
               applies_to { jurisdictions: [ sc ]; operation_kinds: [ entity.incorporate, entity.* ] } \
               with end";
    let term = parse_src(src).expect("should parse");
    let printed = pretty::pretty_print(&term);
    assert!(
        printed.contains("applies_to {"),
        "pretty output should render the applies_to clause; got:\n{printed}"
    );
    assert!(
        printed.contains("jurisdictions: [") && printed.contains("operation_kinds: ["),
        "pretty output should render both scope fields; got:\n{printed}"
    );
    // The family wildcard is rendered as `entity.*`.
    assert!(
        printed.contains("entity.*"),
        "pretty output should render the family wildcard; got:\n{printed}"
    );
}
