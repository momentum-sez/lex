use lex_core::ast::Term;
use lex_core::certificate::ComplianceVerdict;
use lex_core::evaluate::{evaluate, EvalError, RuntimeContext, RuntimeValue};
use lex_core::{elaborate, lexer, parser, prelude, typecheck};

fn context() -> typecheck::Context {
    prelude::structural_prelude().with_named_constant(
        "enabled",
        Term::pi(
            "ctx",
            Term::constant("IncorporationContext"),
            Term::constant("Bool"),
        ),
    )
}

fn elaborate_rule(source: &str) -> Term {
    let tokens = lexer::lex(source).unwrap();
    let parsed = parser::parse(&tokens).unwrap();
    elaborate::elaborate(&parsed, &context()).unwrap()
}

fn rule_type() -> Term {
    Term::pi(
        "ctx",
        Term::constant("IncorporationContext"),
        Term::constant("ComplianceVerdict"),
    )
}

const REDUCED_PAYLOAD_RULE: &str = "\
λ(ctx : IncorporationContext).
  match (let tag : ComplianceTag = Nil in Cons ctx tag) return ComplianceVerdict with
  | Cons saved tail =>
      match tail return ComplianceVerdict with
      | Nil => match enabled saved return ComplianceVerdict with
          | True => Compliant
          | False => NonCompliant
          end
      | _ => Pending
      end
  end";

#[test]
fn typed_reduced_payload_rule_preserves_runtime_evidence() {
    let core = elaborate_rule(REDUCED_PAYLOAD_RULE);
    typecheck::check(&context(), &core, &rule_type()).unwrap();

    assert_eq!(
        evaluate(&core, &RuntimeContext::new()),
        Err(EvalError::UnknownAccessor {
            name: "enabled".into(),
        })
    );
    for (enabled, expected) in [
        (true, ComplianceVerdict::Compliant),
        (false, ComplianceVerdict::NonCompliant),
    ] {
        let mut runtime = RuntimeContext::new();
        runtime.insert("enabled", RuntimeValue::Bool(enabled));
        assert_eq!(evaluate(&core, &runtime), Ok(expected));
    }
}

#[test]
fn typed_reduced_payload_rule_checks_unselected_branch_types() {
    let source = REDUCED_PAYLOAD_RULE.replace("| _ => Pending", "| _ => True");
    let core = elaborate_rule(&source);
    assert!(typecheck::check(&context(), &core, &rule_type()).is_err());
}
