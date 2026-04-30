//! Runtime predicate evaluator for Lex capability caveats.
//!
//! The dependently-typed `Term`/type-checker in the rest of this crate checks
//! that a proposition is well-formed. At authorisation time, the host must
//! take a **closed**, already-well-typed caveat proposition and *decide* it
//! against a concrete request context (actor DID, zone, entity id, op family,
//! amount, expiry, etc.). That is what this module does.
//!
//! This evaluator is intentionally a **small first-order fragment**: conjunction,
//! disjunction, negation, equality, ordering over numbers/timestamps,
//! membership in a finite set, and presence of an attribute. That fragment is
//! sufficient for the public capability-caveat fragment (Jurisdiction,
//! Monetary, Temporal, Domain, Rate, Operation, Mcp, Resource, Counterparty,
//! Discretion, Subject, and Custom), and subsumption on it is decidable
//! cheaply.
//!
//! # Design
//!
//! - [`LexValue`] is the runtime value lattice: `Did`, `String`, `Number`,
//!   `Timestamp`, `Bool`, `Set`.
//! - [`EvalContext`] is a map from attribute name (`actor`, `entity_id`,
//!   `op_type`, `amount`, `expires`, …) to a [`LexValue`].
//! - [`LexProposition`] is the closed proposition to decide. Literals are
//!   atomic constraints on named attributes; boolean combinators compose them.
//! - [`evaluate`] returns `Ok(bool)` on a successful decision, or an
//!   [`EvalError`] when the context is structurally incompatible with the
//!   proposition (unknown attribute, type mismatch, undecidable temporal).
//!
//! Narrowing/subsumption is a separate concern and lives in
//! `predicate_narrowing`.

use std::collections::{BTreeMap, BTreeSet};

use chrono::{DateTime, Utc};
use rust_decimal::Decimal;
use serde::{Deserialize, Serialize};
use thiserror::Error;

// ---------------------------------------------------------------------------
// LexValue — the runtime value lattice
// ---------------------------------------------------------------------------

/// A concrete runtime value bound to an attribute in an [`EvalContext`].
///
/// Ordering on `LexValue` is total (it is derived), but comparison is only
/// *semantically* meaningful between values of the same variant; mixing
/// variants in `<`/`≤` is an [`EvalError::TypeMismatch`] at evaluation time.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum LexValue {
    /// A decentralised identifier (a DID URI string).
    Did(String),
    /// An opaque string (e.g., zone id, operation family name, resource id).
    String(String),
    /// A numeric value (money amount, count).
    Number(Decimal),
    /// A UTC timestamp.
    Timestamp(DateTime<Utc>),
    /// A boolean flag.
    Bool(bool),
    /// A finite set of values (e.g., a DomainSet, an OperationFamilySet).
    Set(BTreeSet<LexValue>),
}

impl LexValue {
    /// Return a short tag naming the variant. Used by error messages.
    pub fn kind(&self) -> &'static str {
        match self {
            LexValue::Did(_) => "Did",
            LexValue::String(_) => "String",
            LexValue::Number(_) => "Number",
            LexValue::Timestamp(_) => "Timestamp",
            LexValue::Bool(_) => "Bool",
            LexValue::Set(_) => "Set",
        }
    }
}

// ---------------------------------------------------------------------------
// EvalContext — map from attribute name to LexValue
// ---------------------------------------------------------------------------

/// The request context against which a caveat is decided.
///
/// Populated by the auth layer before handing a closed [`LexProposition`] to
/// [`evaluate`]. Canonical attribute names include `actor`, `entity_id`,
/// `zone`, `op_type`, `amount`, `expires`, `now`, `counterparty`, `domain`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvalContext {
    /// Attribute name → bound value.
    pub attrs: BTreeMap<String, LexValue>,
}

impl EvalContext {
    /// Construct an empty context.
    pub fn new() -> Self {
        Self {
            attrs: BTreeMap::new(),
        }
    }

    /// Insert / overwrite an attribute binding (builder-style).
    pub fn with(mut self, name: impl Into<String>, value: LexValue) -> Self {
        self.attrs.insert(name.into(), value);
        self
    }

    /// Mutating insertion.
    pub fn insert(&mut self, name: impl Into<String>, value: LexValue) -> &mut Self {
        self.attrs.insert(name.into(), value);
        self
    }

    /// Look up an attribute.
    pub fn get(&self, name: &str) -> Option<&LexValue> {
        self.attrs.get(name)
    }
}

// ---------------------------------------------------------------------------
// LexProposition — the AST decided at runtime
// ---------------------------------------------------------------------------

/// A closed first-order proposition over [`EvalContext`] attributes.
///
/// "Closed" means all variables have been substituted with concrete literals
/// or reduced to attribute references. The proposition is the subset of Lex
/// propositions that this runtime evaluator can decide directly; richer
/// Lex terms must be lowered to this fragment by the typechecker before
/// being passed to [`evaluate`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum LexProposition {
    /// Constant truth value.
    Bool(bool),

    /// Logical conjunction `p ∧ q`.
    And(Box<LexProposition>, Box<LexProposition>),

    /// Logical disjunction `p ∨ q`.
    Or(Box<LexProposition>, Box<LexProposition>),

    /// Logical negation `¬p`.
    Not(Box<LexProposition>),

    /// `attr = literal`.
    Eq { attr: String, value: LexValue },

    /// `attr ≠ literal`.
    NotEq { attr: String, value: LexValue },

    /// `attr < literal` — ordering over numbers or timestamps.
    Lt { attr: String, value: LexValue },

    /// `attr ≤ literal` — ordering over numbers or timestamps.
    Le { attr: String, value: LexValue },

    /// `attr > literal`.
    Gt { attr: String, value: LexValue },

    /// `attr ≥ literal`.
    Ge { attr: String, value: LexValue },

    /// `attr ∈ {v1, v2, …}` — membership in a finite literal set.
    In {
        attr: String,
        values: BTreeSet<LexValue>,
    },

    /// `attr ∈ ctx-set-attr` — membership where the set lives in the context.
    InCtx { attr: String, set_attr: String },
}

// ---------------------------------------------------------------------------
// LexCaveat — a semantically-typed caveat wrapping a proposition
// ---------------------------------------------------------------------------

/// The kinds of caveats recognised by the narrowing engine.
///
/// These mirror the caveat variants in `09-AUTH-CAPABILITY.md`. Each kind
/// corresponds to a structural subsumption rule; see
/// [`crate::predicate_narrowing`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum CaveatKind {
    /// Restrict which operation families are authorised.
    Operation,
    /// Restrict which resources are authorised.
    Resource,
    /// Restrict to named jurisdictions.
    Jurisdiction,
    /// Bound a monetary outflow.
    Monetary,
    /// Restrict to a UTC interval `[not_before, not_after]`.
    Temporal,
    /// Restrict to a subset of the 23 compliance domains.
    Domain,
    /// Per-subject rate limit.
    Rate,
    /// Restrict to named MCP tools.
    Mcp,
    /// Restrict to named counterparties.
    Counterparty,
    /// Discretion hole (requires human principal match).
    Discretion,
    /// Subject binding: the principal-side allowlist of entity ids the
    /// bearer may act *on behalf of*. Distinct from `Resource`:
    /// `Subject` narrows the principal side, `Resource` narrows the
    /// object side. Narrowing semantics: monotone set-inclusion on the
    /// `subject_entity_id` attribute (`child ⊆ parent`).
    Subject,
    /// Uncategorised / opaque caveat — decided purely by its proposition.
    Custom,
}

/// A caveat: a named kind tag plus the closed predicate that decides it.
///
/// The `kind` is advisory — it drives the fast-path structural subsumption
/// rules in [`crate::predicate_narrowing`]. The `predicate` is the semantic
/// content and is what [`evaluate`] actually runs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LexCaveat {
    /// Structural classification of the caveat.
    pub kind: CaveatKind,
    /// The closed proposition this caveat imposes.
    pub predicate: LexProposition,
}

impl LexCaveat {
    /// Construct a new caveat.
    pub fn new(kind: CaveatKind, predicate: LexProposition) -> Self {
        Self { kind, predicate }
    }
}

// ---------------------------------------------------------------------------
// EvalError — structural failure during evaluation
// ---------------------------------------------------------------------------

/// Errors returned by [`evaluate`].
///
/// A well-formed, well-typed proposition decided against a complete context
/// returns `Ok(true)` or `Ok(false)`. Any of the `EvalError` variants
/// indicates the proposition is structurally incompatible with the context
/// (i.e., the proposition cannot be decided as stated).
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum EvalError {
    /// Proposition references an attribute not present in the context.
    #[error("unknown attribute `{0}` in evaluation context")]
    UnknownAttribute(String),

    /// Proposition compares values of incompatible kinds.
    #[error("type mismatch for attribute `{attr}`: expected {expected}, found {found}")]
    TypeMismatch {
        /// Attribute name.
        attr: String,
        /// Expected value kind.
        expected: &'static str,
        /// Found value kind.
        found: &'static str,
    },

    /// Ordering operator used on a kind that does not admit it.
    #[error("attribute `{attr}` of kind {kind} does not support ordering comparisons")]
    UnorderedKind {
        /// Attribute name.
        attr: String,
        /// Non-orderable kind.
        kind: &'static str,
    },

    /// A temporal comparison cannot be decided (e.g., no `now` in context for
    /// a relative temporal predicate). Reserved for callers that lower
    /// `not_before/not_after` against a wall-clock source not in `ctx`.
    #[error("temporal predicate undecidable: {0}")]
    TemporalUndecidable(String),

    /// Expected a `Set` value for a set-typed attribute, found something else.
    #[error("attribute `{attr}` expected to be a Set, found {found}")]
    ExpectedSet {
        /// Attribute name.
        attr: String,
        /// Actual kind.
        found: &'static str,
    },
}

// ---------------------------------------------------------------------------
// evaluate
// ---------------------------------------------------------------------------

/// Decide a closed [`LexProposition`] against an [`EvalContext`].
///
/// Returns `Ok(true)` if the proposition holds, `Ok(false)` if it is refuted,
/// or [`EvalError`] if the proposition is structurally incompatible with the
/// context.
pub fn evaluate(prop: &LexProposition, ctx: &EvalContext) -> Result<bool, EvalError> {
    match prop {
        LexProposition::Bool(b) => Ok(*b),

        LexProposition::And(a, b) => {
            // Short-circuit on false.
            if !evaluate(a, ctx)? {
                Ok(false)
            } else {
                evaluate(b, ctx)
            }
        }

        LexProposition::Or(a, b) => {
            if evaluate(a, ctx)? {
                Ok(true)
            } else {
                evaluate(b, ctx)
            }
        }

        LexProposition::Not(p) => evaluate(p, ctx).map(|v| !v),

        LexProposition::Eq { attr, value } => {
            let bound = ctx
                .get(attr)
                .ok_or_else(|| EvalError::UnknownAttribute(attr.clone()))?;
            kinds_compatible(attr, bound, value)?;
            Ok(bound == value)
        }

        LexProposition::NotEq { attr, value } => {
            let bound = ctx
                .get(attr)
                .ok_or_else(|| EvalError::UnknownAttribute(attr.clone()))?;
            kinds_compatible(attr, bound, value)?;
            Ok(bound != value)
        }

        LexProposition::Lt { attr, value } => compare(attr, value, ctx, Ordering::Lt),
        LexProposition::Le { attr, value } => compare(attr, value, ctx, Ordering::Le),
        LexProposition::Gt { attr, value } => compare(attr, value, ctx, Ordering::Gt),
        LexProposition::Ge { attr, value } => compare(attr, value, ctx, Ordering::Ge),

        LexProposition::In { attr, values } => {
            let bound = ctx
                .get(attr)
                .ok_or_else(|| EvalError::UnknownAttribute(attr.clone()))?;
            // Every member of `values` must share the attribute's kind. If
            // `values` is empty, membership is vacuously false (matches the
            // mathematical convention on the empty set).
            if let Some(first) = values.iter().next() {
                kinds_compatible(attr, bound, first)?;
            }
            Ok(values.contains(bound))
        }

        LexProposition::InCtx { attr, set_attr } => {
            let bound = ctx
                .get(attr)
                .ok_or_else(|| EvalError::UnknownAttribute(attr.clone()))?;
            let set_value = ctx
                .get(set_attr)
                .ok_or_else(|| EvalError::UnknownAttribute(set_attr.clone()))?;
            let set = match set_value {
                LexValue::Set(s) => s,
                other => {
                    return Err(EvalError::ExpectedSet {
                        attr: set_attr.clone(),
                        found: other.kind(),
                    });
                }
            };
            if let Some(first) = set.iter().next() {
                kinds_compatible(attr, bound, first)?;
            }
            Ok(set.contains(bound))
        }
    }
}

// ---------------------------------------------------------------------------
// internal helpers
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
enum Ordering {
    Lt,
    Le,
    Gt,
    Ge,
}

fn compare(
    attr: &str,
    value: &LexValue,
    ctx: &EvalContext,
    op: Ordering,
) -> Result<bool, EvalError> {
    let bound = ctx
        .get(attr)
        .ok_or_else(|| EvalError::UnknownAttribute(attr.to_string()))?;
    kinds_compatible(attr, bound, value)?;
    // Ordering is only defined over Number and Timestamp values.
    let ord = match (bound, value) {
        (LexValue::Number(a), LexValue::Number(b)) => a.cmp(b),
        (LexValue::Timestamp(a), LexValue::Timestamp(b)) => a.cmp(b),
        (other, _) => {
            return Err(EvalError::UnorderedKind {
                attr: attr.to_string(),
                kind: other.kind(),
            });
        }
    };
    Ok(match op {
        Ordering::Lt => ord.is_lt(),
        Ordering::Le => ord.is_le(),
        Ordering::Gt => ord.is_gt(),
        Ordering::Ge => ord.is_ge(),
    })
}

/// Return `Ok(())` if `bound` and `lit` share the same [`LexValue`] variant;
/// return [`EvalError::TypeMismatch`] otherwise.
fn kinds_compatible(attr: &str, bound: &LexValue, lit: &LexValue) -> Result<(), EvalError> {
    if std::mem::discriminant(bound) == std::mem::discriminant(lit) {
        Ok(())
    } else {
        Err(EvalError::TypeMismatch {
            attr: attr.to_string(),
            expected: bound.kind(),
            found: lit.kind(),
        })
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use chrono::TimeZone;
    use std::str::FromStr;

    fn ts(s: &str) -> LexValue {
        LexValue::Timestamp(DateTime::parse_from_rfc3339(s).unwrap().with_timezone(&Utc))
    }

    fn num(s: &str) -> LexValue {
        LexValue::Number(Decimal::from_str(s).unwrap())
    }

    fn set(items: Vec<LexValue>) -> LexValue {
        LexValue::Set(items.into_iter().collect())
    }

    #[test]
    fn conjunction_both_true() {
        let prop = LexProposition::And(
            Box::new(LexProposition::Eq {
                attr: "actor".into(),
                value: LexValue::Did("did:mass:alice".into()),
            }),
            Box::new(LexProposition::Eq {
                attr: "entity_id".into(),
                value: LexValue::String("E1".into()),
            }),
        );
        let ctx = EvalContext::new()
            .with("actor", LexValue::Did("did:mass:alice".into()))
            .with("entity_id", LexValue::String("E1".into()));
        assert_eq!(evaluate(&prop, &ctx), Ok(true));
    }

    #[test]
    fn conjunction_one_false() {
        let prop = LexProposition::And(
            Box::new(LexProposition::Eq {
                attr: "actor".into(),
                value: LexValue::Did("did:mass:alice".into()),
            }),
            Box::new(LexProposition::Eq {
                attr: "entity_id".into(),
                value: LexValue::String("E1".into()),
            }),
        );
        let ctx = EvalContext::new()
            .with("actor", LexValue::Did("did:mass:alice".into()))
            .with("entity_id", LexValue::String("E2".into()));
        assert_eq!(evaluate(&prop, &ctx), Ok(false));
    }

    #[test]
    fn disjunction() {
        // actor=alice ∨ actor=bob
        let prop = LexProposition::Or(
            Box::new(LexProposition::Eq {
                attr: "actor".into(),
                value: LexValue::Did("did:mass:alice".into()),
            }),
            Box::new(LexProposition::Eq {
                attr: "actor".into(),
                value: LexValue::Did("did:mass:bob".into()),
            }),
        );
        let ctx_alice = EvalContext::new().with("actor", LexValue::Did("did:mass:alice".into()));
        let ctx_bob = EvalContext::new().with("actor", LexValue::Did("did:mass:bob".into()));
        let ctx_eve = EvalContext::new().with("actor", LexValue::Did("did:mass:eve".into()));
        assert_eq!(evaluate(&prop, &ctx_alice), Ok(true));
        assert_eq!(evaluate(&prop, &ctx_bob), Ok(true));
        assert_eq!(evaluate(&prop, &ctx_eve), Ok(false));
    }

    #[test]
    fn negation() {
        let prop = LexProposition::Not(Box::new(LexProposition::Eq {
            attr: "actor".into(),
            value: LexValue::Did("did:mass:eve".into()),
        }));
        let ctx = EvalContext::new().with("actor", LexValue::Did("did:mass:alice".into()));
        assert_eq!(evaluate(&prop, &ctx), Ok(true));
    }

    #[test]
    fn temporal_expiry_in_the_past_returns_false() {
        // expires < now: proposition says "expiry already passed (still valid)".
        // If expiry time is in the past, the caveat has lapsed → we set
        // up the negation: `now ≤ expires` should be false when expires is past.
        let now = ts("2026-04-19T12:00:00Z");
        let expires_past = ts("2026-04-01T00:00:00Z");
        let ctx = EvalContext::new()
            .with("now", now.clone())
            .with("expires", expires_past);
        // now < expires should be false (now is after expiry).
        let prop = LexProposition::Lt {
            attr: "now".into(),
            value: match ctx.get("expires") {
                Some(LexValue::Timestamp(t)) => LexValue::Timestamp(*t),
                _ => panic!(),
            },
        };
        assert_eq!(evaluate(&prop, &ctx), Ok(false));
    }

    #[test]
    fn temporal_not_yet_expired() {
        let now = ts("2026-04-19T12:00:00Z");
        let future = ts("2026-12-31T23:59:59Z");
        let ctx = EvalContext::new().with("now", now);
        let prop = LexProposition::Lt {
            attr: "now".into(),
            value: future,
        };
        assert_eq!(evaluate(&prop, &ctx), Ok(true));
    }

    #[test]
    fn amount_cap_le() {
        let ctx = EvalContext::new().with("amount", num("9999"));
        let cap = LexProposition::Le {
            attr: "amount".into(),
            value: num("10000"),
        };
        assert_eq!(evaluate(&cap, &ctx), Ok(true));

        let ctx_over = EvalContext::new().with("amount", num("10001"));
        assert_eq!(evaluate(&cap, &ctx_over), Ok(false));
    }

    #[test]
    fn amount_cap_boundary() {
        let ctx = EvalContext::new().with("amount", num("10000"));
        let cap = LexProposition::Le {
            attr: "amount".into(),
            value: num("10000"),
        };
        assert_eq!(evaluate(&cap, &ctx), Ok(true));
        let strict = LexProposition::Lt {
            attr: "amount".into(),
            value: num("10000"),
        };
        assert_eq!(evaluate(&strict, &ctx), Ok(false));
    }

    #[test]
    fn membership_in_finite_set() {
        let mut s = BTreeSet::new();
        s.insert(LexValue::String("payment.create".into()));
        s.insert(LexValue::String("payment.cancel".into()));
        let prop = LexProposition::In {
            attr: "op_type".into(),
            values: s,
        };
        let ctx_ok = EvalContext::new().with("op_type", LexValue::String("payment.create".into()));
        let ctx_bad = EvalContext::new().with("op_type", LexValue::String("payment.refund".into()));
        assert_eq!(evaluate(&prop, &ctx_ok), Ok(true));
        assert_eq!(evaluate(&prop, &ctx_bad), Ok(false));
    }

    #[test]
    fn membership_in_ctx_set() {
        let authorised = set(vec![
            LexValue::String("payment.create".into()),
            LexValue::String("payment.cancel".into()),
        ]);
        let ctx = EvalContext::new()
            .with("op_type", LexValue::String("payment.create".into()))
            .with("authorised_ops", authorised);
        let prop = LexProposition::InCtx {
            attr: "op_type".into(),
            set_attr: "authorised_ops".into(),
        };
        assert_eq!(evaluate(&prop, &ctx), Ok(true));
    }

    #[test]
    fn empty_set_is_never_member() {
        let prop = LexProposition::In {
            attr: "op_type".into(),
            values: BTreeSet::new(),
        };
        let ctx = EvalContext::new().with("op_type", LexValue::String("payment.create".into()));
        assert_eq!(evaluate(&prop, &ctx), Ok(false));
    }

    #[test]
    fn unknown_attribute_errors() {
        let prop = LexProposition::Eq {
            attr: "missing".into(),
            value: LexValue::String("x".into()),
        };
        let ctx = EvalContext::new();
        assert!(matches!(
            evaluate(&prop, &ctx),
            Err(EvalError::UnknownAttribute(_))
        ));
    }

    #[test]
    fn type_mismatch_errors() {
        let prop = LexProposition::Eq {
            attr: "amount".into(),
            value: LexValue::String("not-a-number".into()),
        };
        let ctx = EvalContext::new().with("amount", num("100"));
        assert!(matches!(
            evaluate(&prop, &ctx),
            Err(EvalError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn ordering_on_string_errors() {
        let prop = LexProposition::Lt {
            attr: "op_type".into(),
            value: LexValue::String("z".into()),
        };
        let ctx = EvalContext::new().with("op_type", LexValue::String("payment".into()));
        assert!(matches!(
            evaluate(&prop, &ctx),
            Err(EvalError::UnorderedKind { .. })
        ));
    }

    #[test]
    fn deep_conjunction_short_circuits_on_false() {
        // If the first conjunct fails, the second is not evaluated — this
        // matters because the second refers to an unbound attribute that
        // would otherwise raise UnknownAttribute.
        let prop = LexProposition::And(
            Box::new(LexProposition::Bool(false)),
            Box::new(LexProposition::Eq {
                attr: "never_touched".into(),
                value: LexValue::Bool(true),
            }),
        );
        let ctx = EvalContext::new();
        assert_eq!(evaluate(&prop, &ctx), Ok(false));
    }

    #[test]
    fn deep_disjunction_short_circuits_on_true() {
        let prop = LexProposition::Or(
            Box::new(LexProposition::Bool(true)),
            Box::new(LexProposition::Eq {
                attr: "never_touched".into(),
                value: LexValue::Bool(true),
            }),
        );
        let ctx = EvalContext::new();
        assert_eq!(evaluate(&prop, &ctx), Ok(true));
    }

    #[test]
    fn timestamp_ctor_is_accessible() {
        // Smoke test: chrono TimeZone helper actually reachable and parseable.
        let t = Utc.with_ymd_and_hms(2026, 4, 19, 12, 0, 0).unwrap();
        let v = LexValue::Timestamp(t);
        assert_eq!(v.kind(), "Timestamp");
    }
}
