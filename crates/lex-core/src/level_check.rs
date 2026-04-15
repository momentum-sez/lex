//! Level-polymorphic schema enforcement for Lex meta-rules.
//!
//! Lex supports a stratified universe hierarchy where rules at level `ℓ` may
//! quantify over rules at levels strictly below `ℓ`. This module provides
//! structural checks on rule schemas (represented as JSON) to enforce this
//! stratification discipline:
//!
//! 1. **No self-application**: a meta-rule at level `ℓ` must not apply itself
//!    or quantify over its own level. This prevents Girard-style paradoxes
//!    in the rule language.
//!
//! 2. **Level monotonicity**: quantified rule variables in a meta-rule at
//!    level `ℓ` must be annotated with levels strictly less than `ℓ`.
//!
//! The primary entry point is [`check_level_polymorphism`], which validates
//! a rule schema and returns a structured error if stratification is violated.
//!
//! # Usage
//!
//! ```rust
//! use lex_core::level_check::{check_level_polymorphism, MetaRuleLevel};
//!
//! // A valid meta-rule at level 2 quantifying over level 1
//! let schema = serde_json::json!({
//!     "rule_name": "meta_audit",
//!     "level": 2,
//!     "quantifies_over": [
//!         { "var": "r", "level": 1 }
//!     ]
//! });
//! assert!(check_level_polymorphism(&schema).is_ok());
//!
//! // Self-application: level 2 quantifying over level 2 (rejected)
//! let bad = serde_json::json!({
//!     "rule_name": "self_apply",
//!     "level": 2,
//!     "quantifies_over": [
//!         { "var": "r", "level": 2 }
//!     ]
//! });
//! assert!(check_level_polymorphism(&bad).is_err());
//! ```

use serde::{Deserialize, Serialize};
use std::fmt;

// ---------------------------------------------------------------------------
// MetaRuleLevel — tracks which level a rule operates at
// ---------------------------------------------------------------------------

/// Tracks which universe level a meta-rule operates at and which levels
/// it quantifies over.
///
/// Used by the level checker to verify stratification: all quantified levels
/// must be strictly less than the rule's own level.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MetaRuleLevel {
    /// The name of the rule.
    pub rule_name: String,
    /// The universe level at which this rule operates.
    pub level: u64,
    /// The levels that this rule quantifies over (each must be < `level`).
    pub quantified_levels: Vec<QuantifiedVar>,
}

/// A quantified variable with its declared level.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct QuantifiedVar {
    /// The variable name.
    pub var: String,
    /// The universe level of the quantified variable.
    pub level: u64,
}

impl fmt::Display for MetaRuleLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let vars: Vec<String> = self
            .quantified_levels
            .iter()
            .map(|q| format!("{}@{}", q.var, q.level))
            .collect();
        write!(
            f,
            "MetaRuleLevel({} @ level {}, quantifies: [{}])",
            self.rule_name,
            self.level,
            vars.join(", "),
        )
    }
}

// ---------------------------------------------------------------------------
// LevelCheckError — violations of level stratification
// ---------------------------------------------------------------------------

/// Error returned when a rule schema violates the level-polymorphic
/// stratification discipline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LevelCheckError {
    /// A meta-rule quantifies over a level that is not strictly less than
    /// its own level. This includes self-application (quantifying at the
    /// same level).
    SelfApplication {
        /// Name of the offending rule.
        rule_name: String,
        /// The rule's own level.
        rule_level: u64,
        /// The variable that violates stratification.
        var_name: String,
        /// The level of the variable (>= rule_level).
        var_level: u64,
    },
    /// The schema is missing a required field.
    MissingField {
        /// The name of the missing field.
        field: String,
    },
    /// A field has an invalid type (e.g., "level" is not a number).
    InvalidFieldType {
        /// The name of the field.
        field: String,
        /// What was expected.
        expected: String,
    },
    /// The rule name is empty.
    EmptyRuleName,
    /// A quantified variable entry is malformed.
    MalformedQuantifier {
        /// Description of the problem.
        reason: String,
    },
}

impl fmt::Display for LevelCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LevelCheckError::SelfApplication {
                rule_name,
                rule_level,
                var_name,
                var_level,
            } => write!(
                f,
                "level stratification violation: rule '{}' at level {} \
                 quantifies over '{}' at level {} (must be < {})",
                rule_name, rule_level, var_name, var_level, rule_level,
            ),
            LevelCheckError::MissingField { field } => {
                write!(f, "missing required field: '{}'", field)
            }
            LevelCheckError::InvalidFieldType { field, expected } => {
                write!(f, "field '{}' has wrong type (expected {})", field, expected)
            }
            LevelCheckError::EmptyRuleName => write!(f, "rule_name must not be empty"),
            LevelCheckError::MalformedQuantifier { reason } => {
                write!(f, "malformed quantifier entry: {}", reason)
            }
        }
    }
}

impl std::error::Error for LevelCheckError {}

// ---------------------------------------------------------------------------
// check_level_polymorphism — main validation entry point
// ---------------------------------------------------------------------------

/// Validate that a rule schema satisfies the level-polymorphic stratification
/// discipline.
///
/// The schema is expected to be a JSON object with the following fields:
/// - `rule_name` (string): the name of the rule
/// - `level` (u64): the universe level at which the rule operates
/// - `quantifies_over` (array): each entry is an object with:
///   - `var` (string): the quantified variable name
///   - `level` (u64): the universe level of the quantified variable
///
/// # Errors
///
/// Returns [`LevelCheckError`] if:
/// - Required fields are missing or have wrong types
/// - The rule name is empty
/// - Any quantified variable has a level >= the rule's own level
///   (self-application or upward quantification)
pub fn check_level_polymorphism(
    rule: &serde_json::Value,
) -> Result<MetaRuleLevel, LevelCheckError> {
    let obj = rule
        .as_object()
        .ok_or(LevelCheckError::InvalidFieldType {
            field: "(root)".to_string(),
            expected: "object".to_string(),
        })?;

    // Extract rule_name
    let rule_name = obj
        .get("rule_name")
        .ok_or(LevelCheckError::MissingField {
            field: "rule_name".to_string(),
        })?
        .as_str()
        .ok_or(LevelCheckError::InvalidFieldType {
            field: "rule_name".to_string(),
            expected: "string".to_string(),
        })?;

    if rule_name.is_empty() {
        return Err(LevelCheckError::EmptyRuleName);
    }

    // Extract level
    let level = obj
        .get("level")
        .ok_or(LevelCheckError::MissingField {
            field: "level".to_string(),
        })?
        .as_u64()
        .ok_or(LevelCheckError::InvalidFieldType {
            field: "level".to_string(),
            expected: "non-negative integer".to_string(),
        })?;

    // Extract quantifies_over
    let quantifies_over = obj
        .get("quantifies_over")
        .ok_or(LevelCheckError::MissingField {
            field: "quantifies_over".to_string(),
        })?
        .as_array()
        .ok_or(LevelCheckError::InvalidFieldType {
            field: "quantifies_over".to_string(),
            expected: "array".to_string(),
        })?;

    let mut quantified_levels = Vec::with_capacity(quantifies_over.len());

    for (i, entry) in quantifies_over.iter().enumerate() {
        let entry_obj = entry.as_object().ok_or(LevelCheckError::MalformedQuantifier {
            reason: format!("entry {} is not an object", i),
        })?;

        let var = entry_obj
            .get("var")
            .ok_or(LevelCheckError::MalformedQuantifier {
                reason: format!("entry {} missing 'var' field", i),
            })?
            .as_str()
            .ok_or(LevelCheckError::MalformedQuantifier {
                reason: format!("entry {} 'var' is not a string", i),
            })?;

        if var.is_empty() {
            return Err(LevelCheckError::MalformedQuantifier {
                reason: format!("entry {} has empty 'var'", i),
            });
        }

        let var_level = entry_obj
            .get("level")
            .ok_or(LevelCheckError::MalformedQuantifier {
                reason: format!("entry {} missing 'level' field", i),
            })?
            .as_u64()
            .ok_or(LevelCheckError::MalformedQuantifier {
                reason: format!("entry {} 'level' is not a non-negative integer", i),
            })?;

        // Core stratification check: var_level must be strictly less than level
        if var_level >= level {
            return Err(LevelCheckError::SelfApplication {
                rule_name: rule_name.to_string(),
                rule_level: level,
                var_name: var.to_string(),
                var_level,
            });
        }

        quantified_levels.push(QuantifiedVar {
            var: var.to_string(),
            level: var_level,
        });
    }

    Ok(MetaRuleLevel {
        rule_name: rule_name.to_string(),
        level,
        quantified_levels,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- 1. Valid meta-rule passes ---------------------------------------------

    #[test]
    fn valid_meta_rule_passes() {
        let schema = serde_json::json!({
            "rule_name": "meta_audit_policy",
            "level": 2,
            "quantifies_over": [
                { "var": "base_rule", "level": 1 },
                { "var": "subrule", "level": 0 }
            ]
        });

        let result = check_level_polymorphism(&schema).unwrap();
        assert_eq!(result.rule_name, "meta_audit_policy");
        assert_eq!(result.level, 2);
        assert_eq!(result.quantified_levels.len(), 2);
        assert_eq!(result.quantified_levels[0].var, "base_rule");
        assert_eq!(result.quantified_levels[0].level, 1);
        assert_eq!(result.quantified_levels[1].var, "subrule");
        assert_eq!(result.quantified_levels[1].level, 0);
    }

    // -- 2. Self-application rejected (same level) ----------------------------

    #[test]
    fn self_application_same_level_rejected() {
        let schema = serde_json::json!({
            "rule_name": "self_apply",
            "level": 2,
            "quantifies_over": [
                { "var": "r", "level": 2 }
            ]
        });

        let err = check_level_polymorphism(&schema).unwrap_err();
        match err {
            LevelCheckError::SelfApplication {
                rule_name,
                rule_level,
                var_name,
                var_level,
            } => {
                assert_eq!(rule_name, "self_apply");
                assert_eq!(rule_level, 2);
                assert_eq!(var_name, "r");
                assert_eq!(var_level, 2);
            }
            other => panic!("expected SelfApplication, got {:?}", other),
        }
    }

    // -- 3. Upward quantification rejected (var_level > rule_level) -----------

    #[test]
    fn upward_quantification_rejected() {
        let schema = serde_json::json!({
            "rule_name": "upward_rule",
            "level": 1,
            "quantifies_over": [
                { "var": "higher", "level": 3 }
            ]
        });

        let err = check_level_polymorphism(&schema).unwrap_err();
        match err {
            LevelCheckError::SelfApplication {
                var_level,
                rule_level,
                ..
            } => {
                assert_eq!(rule_level, 1);
                assert_eq!(var_level, 3);
            }
            other => panic!("expected SelfApplication, got {:?}", other),
        }
    }

    // -- 4. Missing required fields -------------------------------------------

    #[test]
    fn missing_fields_rejected() {
        // Missing rule_name
        let schema = serde_json::json!({
            "level": 1,
            "quantifies_over": []
        });
        let err = check_level_polymorphism(&schema).unwrap_err();
        assert_eq!(
            err,
            LevelCheckError::MissingField {
                field: "rule_name".to_string(),
            }
        );

        // Missing level
        let schema = serde_json::json!({
            "rule_name": "test",
            "quantifies_over": []
        });
        let err = check_level_polymorphism(&schema).unwrap_err();
        assert_eq!(
            err,
            LevelCheckError::MissingField {
                field: "level".to_string(),
            }
        );

        // Missing quantifies_over
        let schema = serde_json::json!({
            "rule_name": "test",
            "level": 1
        });
        let err = check_level_polymorphism(&schema).unwrap_err();
        assert_eq!(
            err,
            LevelCheckError::MissingField {
                field: "quantifies_over".to_string(),
            }
        );
    }

    // -- 5. Empty rule name rejected ------------------------------------------

    #[test]
    fn empty_rule_name_rejected() {
        let schema = serde_json::json!({
            "rule_name": "",
            "level": 1,
            "quantifies_over": []
        });

        let err = check_level_polymorphism(&schema).unwrap_err();
        assert_eq!(err, LevelCheckError::EmptyRuleName);
    }

    // -- 6. Level-0 rule with no quantifiers passes ---------------------------

    #[test]
    fn level_zero_no_quantifiers_passes() {
        let schema = serde_json::json!({
            "rule_name": "ground_rule",
            "level": 0,
            "quantifies_over": []
        });

        let result = check_level_polymorphism(&schema).unwrap();
        assert_eq!(result.level, 0);
        assert!(result.quantified_levels.is_empty());
    }

    // -- 7. Non-object root rejected ------------------------------------------

    #[test]
    fn non_object_root_rejected() {
        let schema = serde_json::json!("just a string");
        let err = check_level_polymorphism(&schema).unwrap_err();
        match err {
            LevelCheckError::InvalidFieldType { field, expected } => {
                assert_eq!(field, "(root)");
                assert_eq!(expected, "object");
            }
            other => panic!("expected InvalidFieldType, got {:?}", other),
        }
    }

    // -- 8. Malformed quantifier entry ----------------------------------------

    #[test]
    fn malformed_quantifier_entry_rejected() {
        // Entry is not an object
        let schema = serde_json::json!({
            "rule_name": "bad_quant",
            "level": 2,
            "quantifies_over": ["not_an_object"]
        });
        let err = check_level_polymorphism(&schema).unwrap_err();
        match err {
            LevelCheckError::MalformedQuantifier { reason } => {
                assert!(reason.contains("not an object"));
            }
            other => panic!("expected MalformedQuantifier, got {:?}", other),
        }

        // Entry missing var
        let schema = serde_json::json!({
            "rule_name": "bad_quant2",
            "level": 2,
            "quantifies_over": [{ "level": 1 }]
        });
        let err = check_level_polymorphism(&schema).unwrap_err();
        match err {
            LevelCheckError::MalformedQuantifier { reason } => {
                assert!(reason.contains("var"));
            }
            other => panic!("expected MalformedQuantifier, got {:?}", other),
        }

        // Entry with empty var
        let schema = serde_json::json!({
            "rule_name": "bad_quant3",
            "level": 2,
            "quantifies_over": [{ "var": "", "level": 1 }]
        });
        let err = check_level_polymorphism(&schema).unwrap_err();
        match err {
            LevelCheckError::MalformedQuantifier { reason } => {
                assert!(reason.contains("empty"));
            }
            other => panic!("expected MalformedQuantifier, got {:?}", other),
        }
    }

    // -- 9. MetaRuleLevel display formatting ----------------------------------

    #[test]
    fn meta_rule_level_display() {
        let meta = MetaRuleLevel {
            rule_name: "my_meta".to_string(),
            level: 3,
            quantified_levels: vec![
                QuantifiedVar {
                    var: "r1".to_string(),
                    level: 1,
                },
                QuantifiedVar {
                    var: "r2".to_string(),
                    level: 2,
                },
            ],
        };

        let display = meta.to_string();
        assert!(display.contains("my_meta"));
        assert!(display.contains("level 3"));
        assert!(display.contains("r1@1"));
        assert!(display.contains("r2@2"));
    }

    // -- 10. Serde roundtrip for MetaRuleLevel --------------------------------

    #[test]
    fn serde_roundtrip() {
        let meta = MetaRuleLevel {
            rule_name: "audit_meta".to_string(),
            level: 4,
            quantified_levels: vec![
                QuantifiedVar {
                    var: "base".to_string(),
                    level: 2,
                },
            ],
        };

        let json = serde_json::to_string(&meta).unwrap();
        let deser: MetaRuleLevel = serde_json::from_str(&json).unwrap();
        assert_eq!(deser, meta);
    }

    // -- 11. LevelCheckError display ------------------------------------------

    #[test]
    fn level_check_error_display() {
        let err = LevelCheckError::SelfApplication {
            rule_name: "bad_rule".to_string(),
            rule_level: 2,
            var_name: "x".to_string(),
            var_level: 2,
        };
        let display = err.to_string();
        assert!(display.contains("bad_rule"));
        assert!(display.contains("level 2"));
        assert!(display.contains("'x'"));
        assert!(display.contains("must be < 2"));

        let err = LevelCheckError::EmptyRuleName;
        assert!(err.to_string().contains("empty"));

        let err = LevelCheckError::MissingField {
            field: "level".to_string(),
        };
        assert!(err.to_string().contains("level"));
    }

    // -- 12. Multiple quantifiers: first valid, second violates ---------------

    #[test]
    fn second_quantifier_violates() {
        let schema = serde_json::json!({
            "rule_name": "mixed_rule",
            "level": 3,
            "quantifies_over": [
                { "var": "ok", "level": 1 },
                { "var": "bad", "level": 5 }
            ]
        });

        let err = check_level_polymorphism(&schema).unwrap_err();
        match err {
            LevelCheckError::SelfApplication {
                var_name,
                var_level,
                rule_level,
                ..
            } => {
                assert_eq!(var_name, "bad");
                assert_eq!(var_level, 5);
                assert_eq!(rule_level, 3);
            }
            other => panic!("expected SelfApplication, got {:?}", other),
        }
    }
}
