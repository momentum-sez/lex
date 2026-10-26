use lex_core::ast::Term;
use lex_core::boolean_rule::{BooleanRuleError, CompiledBooleanRule};
use lex_core::predicate_runtime::{EvalContext, EvalError, LexValue};
use lex_core::{prelude, typecheck};

fn signature() -> typecheck::Context {
    let mut signature =
        prelude::production_prelude().with_named_constant("RequestContext", Term::type_sort(0));
    for name in ["first", "second"] {
        signature = signature.with_named_constant(
            name,
            Term::pi(
                "ctx",
                Term::constant("RequestContext"),
                Term::constant("Bool"),
            ),
        );
    }
    signature
}

const CONJUNCTION: &str = "\
lambda (ctx : RequestContext).
  match first ctx return ComplianceVerdict with
  | False => NonCompliant
  | True =>
      match second ctx return ComplianceVerdict with
      | True => Compliant
      | False => NonCompliant
      end
  end";

#[test]
fn compiled_source_controls_both_branches_and_nested_tests() {
    let equivalent = "\
lambda (ctx : RequestContext).
  match first ctx return ComplianceVerdict with
  | True =>
      match second ctx return ComplianceVerdict with
      | True => Compliant
      | False => NonCompliant
      end
  | False =>
      match second ctx return ComplianceVerdict with
      | True => NonCompliant
      | False => Compliant
      end
  end";
    let conjunction = CompiledBooleanRule::compile(CONJUNCTION, &signature()).unwrap();
    let equivalent = CompiledBooleanRule::compile(equivalent, &signature()).unwrap();
    for (first, second, both, equal) in [
        (false, false, false, true),
        (false, true, false, false),
        (true, false, false, false),
        (true, true, true, true),
    ] {
        let context = EvalContext::new()
            .with("first", LexValue::Bool(first))
            .with("second", LexValue::Bool(second));
        assert_eq!(conjunction.evaluate(&context).unwrap(), both);
        assert_eq!(equivalent.evaluate(&context).unwrap(), equal);
    }
}

#[test]
fn untaken_branches_cannot_hide_missing_or_mistyped_facts() {
    let rule = CompiledBooleanRule::compile(CONJUNCTION, &signature()).unwrap();
    let context = EvalContext::new().with("first", LexValue::Bool(false));
    assert!(matches!(
        rule.evaluate(&context),
        Err(BooleanRuleError::Evaluation(EvalError::UnknownAttribute(name))) if name == "second"
    ));
    let context = context.with("second", LexValue::String("true".into()));
    assert!(matches!(
        rule.evaluate(&context),
        Err(BooleanRuleError::Evaluation(EvalError::TypeMismatch {
            attr,
            expected: "Bool",
            found: "String"
        })) if attr == "second"
    ));
    assert!(!rule
        .evaluate(&context.with("second", LexValue::Bool(true)))
        .unwrap());
}

#[test]
fn the_fragment_requires_exhaustive_explicit_boolean_branches() {
    CompiledBooleanRule::compile(CONJUNCTION, &signature()).unwrap();
    for branches in [
        "| True => Compliant",
        "| True => Compliant | True => NonCompliant",
        "| True => Compliant | _ => NonCompliant",
        "| True => Pending | False => NonCompliant",
        "| True value => Compliant | False => NonCompliant",
        "| True => Compliant | False => NonCompliant | False => Compliant",
    ] {
        let source = format!(
            "lambda (ctx : RequestContext). match first ctx return ComplianceVerdict with {branches} end"
        );
        assert!(
            CompiledBooleanRule::compile(&source, &signature()).is_err(),
            "accepted unsupported branches: {branches}"
        );
    }
}

#[test]
fn source_cannot_read_a_different_context_or_erase_unsupported_terms() {
    let signature = signature()
        .with_named_constant("other", Term::constant("RequestContext"))
        .with_named_constant("reviewer", Term::constant("ComplianceTag"));
    for source in [
        "lambda (ctx : RequestContext). match first other return ComplianceVerdict with | True => Compliant | False => NonCompliant end",
        "lambda (ctx : RequestContext). match unknown ctx return ComplianceVerdict with | True => Compliant | False => NonCompliant end",
        "lambda (ctx : RequestContext). let result : ComplianceVerdict = Compliant in result",
        "lambda (ctx : RequestContext). ? review : ComplianceVerdict @ reviewer",
        "lambda (ctx : RequestContext). Pending",
    ] {
        assert!(CompiledBooleanRule::compile(source, &signature).is_err(), "accepted {source}");
    }
    assert!(matches!(
        CompiledBooleanRule::compile(&format!("{CONJUNCTION} end NonCompliant"), &signature),
        Err(BooleanRuleError::Parse(_))
    ));
}

#[test]
fn trusted_signature_must_preserve_boolean_and_verdict_types() {
    let malformed = signature().with_named_constant("True", Term::constant("Nat"));
    assert!(matches!(
        CompiledBooleanRule::compile(CONJUNCTION, &malformed),
        Err(BooleanRuleError::InvalidSignature { name }) if name == "True"
    ));
    let wrong_accessor = signature().with_named_constant(
        "second",
        Term::pi(
            "ctx",
            Term::constant("RequestContext"),
            Term::constant("Nat"),
        ),
    );
    assert!(matches!(
        CompiledBooleanRule::compile(CONJUNCTION, &wrong_accessor),
        Err(BooleanRuleError::Type(_))
    ));
    let effectful_accessor = signature().with_named_constant(
        "second",
        Term::Pi {
            binder: lex_core::ast::Ident::new("ctx"),
            domain: Box::new(Term::constant("RequestContext")),
            codomain: Box::new(Term::constant("Bool")),
            effect_row: Some(lex_core::ast::EffectRow::Effects(vec![
                lex_core::ast::Effect::Read,
            ])),
        },
    );
    assert!(CompiledBooleanRule::compile(CONJUNCTION, &effectful_accessor).is_err());
}

#[test]
fn oversized_source_is_rejected_before_parsing() {
    let source = format!("-- {}\n{CONJUNCTION}", "x".repeat(65_536));
    assert!(matches!(
        CompiledBooleanRule::compile(&source, &signature()),
        Err(BooleanRuleError::SourceTooLarge { limit: 65_536, .. })
    ));
}

#[test]
fn source_effect_annotations_cannot_be_erased_before_fragment_admission() {
    CompiledBooleanRule::compile("lambda (ctx : RequestContext). Compliant", &signature()).unwrap();
    for effects in ["read", "write(ctx)"] {
        let source = format!("lambda (ctx : RequestContext) [{effects}]. Compliant");
        assert!(
            CompiledBooleanRule::compile(&source, &signature()).is_err(),
            "accepted source effect annotation {effects}"
        );
    }
}

#[test]
fn large_application_chain_is_bounded_before_recursive_processing() {
    const CHILD: &str = "LEX_BOOLEAN_RULE_DEPTH_PROBE_CHILD";
    if std::env::var_os(CHILD).is_some() {
        CompiledBooleanRule::compile(CONJUNCTION, &signature()).unwrap();
        let source = format!(
            "lambda (ctx : RequestContext). {}ctx",
            "first ".repeat(10_000)
        );
        assert!(source.len() < 65_536);
        assert!(CompiledBooleanRule::compile(&source, &signature()).is_err());
        return;
    }
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "large_application_chain_is_bounded_before_recursive_processing",
            "--nocapture",
        ])
        .env(CHILD, "1")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "bounded compiler probe terminated: {}\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn distinct_qualified_names_cannot_share_a_runtime_fact_key() {
    let accessor_type = Term::pi(
        "ctx",
        Term::constant("RequestContext"),
        Term::constant("Bool"),
    );
    let signature = signature()
        .with_named_constant("pack.flag", accessor_type.clone())
        .with_constant(
            lex_core::ast::QualIdent::from_dotted("pack.flag"),
            accessor_type,
        );
    let canonical = "lambda (ctx : RequestContext). match pack . flag ctx return ComplianceVerdict with | True => Compliant | False => NonCompliant end";
    let canonical = CompiledBooleanRule::compile(canonical, &signature).unwrap();
    assert!(canonical
        .evaluate(&EvalContext::new().with("pack.flag", LexValue::Bool(true)))
        .unwrap());
    let ambiguous = "lambda (ctx : RequestContext). match pack.flag ctx return ComplianceVerdict with | True => Compliant | False => NonCompliant end";
    assert!(
        CompiledBooleanRule::compile(ambiguous, &signature).is_err(),
        "distinct signature names were collapsed to one runtime key"
    );
}
