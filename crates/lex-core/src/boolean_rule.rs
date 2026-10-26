//! Checked Boolean decision trees lowered to the production predicate runtime.
//!
//! Compilation requires an explicit trusted signature. Evaluation supplies facts,
//! not declarations. This module does not establish fact provenance or authority.

use std::collections::BTreeSet;

use crate::ast::{Branch, Pattern, Term};
use crate::predicate_runtime::{self, EvalContext, EvalError, LexProposition, LexValue};
use crate::token::{Spanned, Token};
use crate::{elaborate, lexer, parser, typecheck};

/// Identity of this checked fragment and its evaluation contract.
pub const EVALUATOR_ID: &str = "lex.boolean-rule.predicate-runtime.v1";

const MAX_SOURCE_BYTES: usize = 65_536;
const MAX_TREE_DEPTH: usize = 64;
const MAX_TREE_NODES: usize = 1_024;

/// A checked rule. Only successful compilation can construct this value.
///
/// The rule accepts one named context type and returns a compliance verdict.
/// Its branches test Boolean accessors of that context.
#[derive(Debug, Clone)]
pub struct CompiledBooleanRule {
    term: Term,
    predicate: LexProposition,
    required_accessors: BTreeSet<String>,
}

impl CompiledBooleanRule {
    /// Parse one source term, elaborate it, check its type, and lower its branches.
    pub fn compile(source: &str, signature: &typecheck::Context) -> Result<Self, BooleanRuleError> {
        if source.len() > MAX_SOURCE_BYTES {
            return Err(BooleanRuleError::SourceTooLarge {
                actual: source.len(),
                limit: MAX_SOURCE_BYTES,
            });
        }
        require_structural_signature(signature)?;
        let tokens = lexer::lex(source)?;
        check_source_shape(&tokens)?;
        let parsed = parser::parse_single_term(&tokens)?;
        let term = elaborate::elaborate(&parsed, signature)?;
        let Term::Lambda { domain, body, .. } = &term else {
            return Err(unsupported("expected one outer lambda"));
        };
        let Term::Constant(context_name) = domain.as_ref() else {
            return Err(unsupported("the context type must be a named constant"));
        };
        require_canonical_name(context_name)?;
        if signature.lookup_constant(context_name) != Some(&Term::type_sort(0)) {
            return Err(BooleanRuleError::InvalidSignature {
                name: context_name.to_dotted(),
            });
        }
        let expected = Term::pi("ctx", *domain.clone(), Term::constant("ComplianceVerdict"));
        typecheck::check(signature, &term, &expected)
            .map_err(|error| BooleanRuleError::Type(Box::new(error)))?;

        let mut required_accessors = BTreeSet::new();
        let mut remaining = MAX_TREE_NODES;
        let predicate = lower_tree(
            body,
            domain,
            signature,
            &mut required_accessors,
            0,
            &mut remaining,
        )?;
        Ok(Self {
            term,
            predicate,
            required_accessors,
        })
    }

    /// Return the checked, indexed source term for content addressing.
    pub fn term(&self) -> &Term {
        &self.term
    }

    /// Return the proposition derived from the complete source tree.
    pub fn predicate(&self) -> &LexProposition {
        &self.predicate
    }

    /// Return all referenced accessors in lexical order, including untaken branches.
    pub fn required_accessors(&self) -> impl ExactSizeIterator<Item = &str> {
        self.required_accessors.iter().map(String::as_str)
    }

    /// Check every required input before evaluating the lowered proposition.
    ///
    /// `true` represents `Compliant`. `false` represents `NonCompliant`.
    /// Missing or non-Boolean inputs remain errors, including inputs on untaken branches.
    pub fn evaluate(&self, context: &EvalContext) -> Result<bool, BooleanRuleError> {
        for name in &self.required_accessors {
            match context.get(name) {
                Some(LexValue::Bool(_)) => {}
                Some(value) => {
                    return Err(EvalError::TypeMismatch {
                        attr: name.clone(),
                        expected: "Bool",
                        found: value.kind(),
                    }
                    .into());
                }
                None => return Err(EvalError::UnknownAttribute(name.clone()).into()),
            }
        }
        predicate_runtime::evaluate(&self.predicate, context).map_err(Into::into)
    }
}

// Check the closed source grammar iteratively before any recursive AST exists.
// The general parser intentionally drops lambda effect annotations and admits
// application chains beyond this fragment. Neither may reach elaboration here.
fn check_source_shape(tokens: &[Spanned<Token>]) -> Result<(), BooleanRuleError> {
    enum Task {
        Tree(usize),
        Branch(usize),
        Token(Token),
    }

    let mut source = SourceCursor {
        tokens,
        position: 0,
    };
    source.expect(&Token::Lambda)?;
    source.expect(&Token::Lparen)?;
    let binder = source.name()?;
    source.expect(&Token::Colon)?;
    source.qualified_name()?;
    source.expect(&Token::Rparen)?;
    source.expect(&Token::Dot)?;

    let mut tasks = vec![Task::Tree(0)];
    let mut nodes = 0_usize;
    while let Some(task) = tasks.pop() {
        match task {
            Task::Token(token) => source.expect(&token)?,
            Task::Branch(depth) => {
                source.expect(&Token::Pipe)?;
                if !matches!(source.name()?, "True" | "False") {
                    return Err(unsupported("Boolean branches must be True and False"));
                }
                source.expect(&Token::DoubleArrow)?;
                tasks.push(Task::Tree(depth));
            }
            Task::Tree(depth) => {
                nodes += 1;
                if depth > MAX_TREE_DEPTH || nodes > MAX_TREE_NODES {
                    return Err(BooleanRuleError::StructuralLimit);
                }
                match source.peek()? {
                    Token::Lparen => {
                        source.expect(&Token::Lparen)?;
                        tasks.push(Task::Token(Token::Rparen));
                        tasks.push(Task::Tree(depth + 1));
                    }
                    Token::Match => {
                        source.expect(&Token::Match)?;
                        source.qualified_name()?;
                        if source.name()? != binder {
                            return Err(unsupported(
                                "an accessor must read the bound context directly",
                            ));
                        }
                        source.expect(&Token::Return)?;
                        if source.name()? != "ComplianceVerdict" {
                            return Err(unsupported("a branch must return ComplianceVerdict"));
                        }
                        source.expect(&Token::With)?;
                        tasks.push(Task::Token(Token::End));
                        tasks.push(Task::Branch(depth + 1));
                        tasks.push(Task::Branch(depth + 1));
                    }
                    Token::Ident(name) if matches!(name.as_str(), "Compliant" | "NonCompliant") => {
                        source.name()?;
                    }
                    _ => {
                        return Err(unsupported(
                            "source is outside the Boolean decision-tree grammar",
                        ))
                    }
                }
            }
        }
    }
    if !matches!(source.peek()?, Token::Eof) {
        let (_, span) = source
            .tokens
            .get(source.position)
            .ok_or_else(|| unsupported("incomplete source"))?;
        return Err(parser::ParseError {
            span: *span,
            expected: "end of input".into(),
            found: source.peek()?.to_string(),
        }
        .into());
    }
    Ok(())
}

struct SourceCursor<'a> {
    tokens: &'a [Spanned<Token>],
    position: usize,
}

impl<'a> SourceCursor<'a> {
    fn peek(&self) -> Result<&'a Token, BooleanRuleError> {
        self.tokens
            .get(self.position)
            .map(|(token, _)| token)
            .ok_or_else(|| unsupported("incomplete source"))
    }

    fn expect(&mut self, expected: &Token) -> Result<(), BooleanRuleError> {
        if self.peek()? != expected {
            return Err(unsupported(
                "source is outside the Boolean decision-tree grammar",
            ));
        }
        self.position += 1;
        Ok(())
    }

    fn name(&mut self) -> Result<&'a str, BooleanRuleError> {
        let Token::Ident(name) = self.peek()? else {
            return Err(unsupported("expected a source identifier"));
        };
        self.position += 1;
        Ok(name)
    }

    fn qualified_name(&mut self) -> Result<(), BooleanRuleError> {
        self.name()?;
        while matches!(self.peek()?, Token::Dot) {
            self.expect(&Token::Dot)?;
            self.name()?;
        }
        Ok(())
    }
}

fn require_canonical_name(name: &crate::ast::QualIdent) -> Result<(), BooleanRuleError> {
    if name.segments.is_empty()
        || name
            .segments
            .iter()
            .any(|segment| segment.is_empty() || segment.contains('.'))
    {
        return Err(BooleanRuleError::InvalidSignature {
            name: name.to_dotted(),
        });
    }
    Ok(())
}

fn require_structural_signature(signature: &typecheck::Context) -> Result<(), BooleanRuleError> {
    for (name, expected) in [
        ("Bool", Term::type_sort(0)),
        ("True", Term::constant("Bool")),
        ("False", Term::constant("Bool")),
        ("ComplianceVerdict", Term::type_sort(0)),
        ("Compliant", Term::constant("ComplianceVerdict")),
        ("NonCompliant", Term::constant("ComplianceVerdict")),
    ] {
        if signature.lookup_named_constant(name) != Some(&expected) {
            return Err(BooleanRuleError::InvalidSignature { name: name.into() });
        }
    }
    Ok(())
}

fn lower_tree(
    term: &Term,
    domain: &Term,
    signature: &typecheck::Context,
    accessors: &mut BTreeSet<String>,
    depth: usize,
    remaining: &mut usize,
) -> Result<LexProposition, BooleanRuleError> {
    if depth > MAX_TREE_DEPTH || *remaining == 0 {
        return Err(BooleanRuleError::StructuralLimit);
    }
    *remaining -= 1;
    match term {
        Term::Constant(name) if name == &crate::ast::QualIdent::simple("Compliant") => {
            Ok(LexProposition::Bool(true))
        }
        Term::Constant(name) if name == &crate::ast::QualIdent::simple("NonCompliant") => {
            Ok(LexProposition::Bool(false))
        }
        Term::Match {
            scrutinee,
            return_ty,
            branches,
        } => {
            if return_ty.as_ref() != &Term::constant("ComplianceVerdict") {
                return Err(unsupported("a branch must return ComplianceVerdict"));
            }
            let accessor = require_boolean_accessor(scrutinee, domain, signature)?;
            accessors.insert(accessor.clone());
            let (when_true, when_false) = exhaustive_branches(branches)?;
            let when_true = lower_tree(
                when_true,
                domain,
                signature,
                accessors,
                depth + 1,
                remaining,
            )?;
            let when_false = lower_tree(
                when_false,
                domain,
                signature,
                accessors,
                depth + 1,
                remaining,
            )?;
            let condition = LexProposition::Eq {
                attr: accessor,
                value: LexValue::Bool(true),
            };
            Ok(LexProposition::Or(
                Box::new(LexProposition::And(
                    Box::new(condition.clone()),
                    Box::new(when_true),
                )),
                Box::new(LexProposition::And(
                    Box::new(LexProposition::Not(Box::new(condition))),
                    Box::new(when_false),
                )),
            ))
        }
        _ => Err(unsupported(
            "expected a Boolean match or a Compliant/NonCompliant leaf",
        )),
    }
}

fn require_boolean_accessor(
    scrutinee: &Term,
    domain: &Term,
    signature: &typecheck::Context,
) -> Result<String, BooleanRuleError> {
    let Term::App { func, arg } = scrutinee else {
        return Err(unsupported(
            "a test must apply a named accessor to the context",
        ));
    };
    let (Term::Constant(name), Term::Var { index: 0, .. }) = (func.as_ref(), arg.as_ref()) else {
        return Err(unsupported(
            "an accessor must read the bound context directly",
        ));
    };
    require_canonical_name(name)?;
    match signature.lookup_constant(name) {
        Some(Term::Pi {
            domain: accessor_domain,
            codomain,
            effect_row: None,
            ..
        }) if accessor_domain.as_ref() == domain
            && codomain.as_ref() == &Term::constant("Bool") =>
        {
            Ok(name.to_dotted())
        }
        _ => Err(BooleanRuleError::InvalidSignature {
            name: name.to_dotted(),
        }),
    }
}

fn exhaustive_branches(branches: &[Branch]) -> Result<(&Term, &Term), BooleanRuleError> {
    if branches.len() != 2 {
        return Err(unsupported("a Boolean match requires exactly two branches"));
    }
    let mut when_true = None;
    let mut when_false = None;
    for branch in branches {
        let Pattern::Constructor {
            constructor,
            binders,
        } = &branch.pattern
        else {
            return Err(unsupported(
                "Boolean branches require explicit constructor patterns",
            ));
        };
        if !binders.is_empty() {
            return Err(unsupported("Boolean constructors have no payload"));
        }
        let slot = if constructor.name == crate::ast::QualIdent::simple("True") {
            &mut when_true
        } else if constructor.name == crate::ast::QualIdent::simple("False") {
            &mut when_false
        } else {
            return Err(unsupported("Boolean branches must be True and False"));
        };
        if slot.replace(&branch.body).is_some() {
            return Err(unsupported("duplicate Boolean branch"));
        }
    }
    match (when_true, when_false) {
        (Some(when_true), Some(when_false)) => Ok((when_true, when_false)),
        _ => Err(unsupported("Boolean branches must be exhaustive")),
    }
}

fn unsupported(reason: &'static str) -> BooleanRuleError {
    BooleanRuleError::UnsupportedShape { reason }
}

/// A source, signature, fragment, or runtime input failed the checked contract.
#[derive(Debug, thiserror::Error)]
pub enum BooleanRuleError {
    /// The source exceeds the bounded compiler input.
    #[error("Boolean rule source has {actual} bytes, maximum {limit}")]
    SourceTooLarge { actual: usize, limit: usize },
    /// Lexical analysis failed.
    #[error(transparent)]
    Lex(#[from] lexer::LexError),
    /// Parsing failed, including additional top-level terms.
    #[error(transparent)]
    Parse(#[from] parser::ParseError),
    /// Names or bound variables could not be resolved.
    #[error(transparent)]
    Elaboration(#[from] elaborate::ElaborationError),
    /// The full source term did not have the required type.
    #[error("Boolean rule type checking failed: {0}")]
    Type(Box<typecheck::TypeError>),
    /// A declaration differs from the required structural or accessor signature.
    #[error("invalid Boolean rule signature for {name}")]
    InvalidSignature { name: String },
    /// The checked term uses syntax outside this executable fragment.
    #[error("unsupported Boolean rule shape: {reason}")]
    UnsupportedShape { reason: &'static str },
    /// The tree exceeds the bounded compiler depth or node count.
    #[error("Boolean rule exceeds the structural limit")]
    StructuralLimit,
    /// A required runtime fact is missing or has the wrong type.
    #[error(transparent)]
    Evaluation(#[from] EvalError),
}
