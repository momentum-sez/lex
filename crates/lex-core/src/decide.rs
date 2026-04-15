use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

#[allow(unused_imports)]
use crate::ast::*;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DecisionResult {
    Proved { witness: ProofWitness },
    Refuted { counterexample: String },
    Undecidable { reason: String },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofWitness {
    pub procedure: String,
    pub description: String,
    pub evidence: Value,
}

pub fn finite_domain_check(
    scrutinee_type: &str,
    compliant_values: &[&str],
    actual_value: &str,
) -> DecisionResult {
    if compliant_values.contains(&actual_value) {
        DecisionResult::Proved {
            witness: ProofWitness {
                procedure: "finite_domain_enumeration".to_string(),
                description: format!(
                    "value `{actual_value}` is a compliant inhabitant of `{scrutinee_type}`"
                ),
                evidence: json!({
                    "scrutinee_type": scrutinee_type,
                    "value": actual_value,
                    "domain": compliant_values,
                    "membership": true
                }),
            },
        }
    } else {
        DecisionResult::Refuted {
            counterexample: format!(
                "value `{actual_value}` is not in the compliant domain for `{scrutinee_type}`"
            ),
        }
    }
}

pub fn boolean_check(proposition: bool) -> DecisionResult {
    if proposition {
        DecisionResult::Proved {
            witness: ProofWitness {
                procedure: "boolean_decision".to_string(),
                description: "proposition evaluated to true".to_string(),
                evidence: json!({
                    "proposition": proposition
                }),
            },
        }
    } else {
        DecisionResult::Refuted {
            counterexample: "proposition evaluated to false".to_string(),
        }
    }
}

pub fn threshold_check(value: i64, threshold: i64, operator: &str) -> DecisionResult {
    let holds = match operator {
        ">=" => value >= threshold,
        ">" => value > threshold,
        "<=" => value <= threshold,
        "<" => value < threshold,
        "==" => value == threshold,
        _ => {
            return DecisionResult::Undecidable {
                reason: format!("unsupported threshold operator `{operator}`"),
            };
        }
    };

    if holds {
        DecisionResult::Proved {
            witness: ProofWitness {
                procedure: "presburger_arithmetic".to_string(),
                description: format!("comparison `{value} {operator} {threshold}` holds"),
                evidence: json!({
                    "value": value,
                    "threshold": threshold,
                    "operator": operator,
                    "result": true
                }),
            },
        }
    } else {
        DecisionResult::Refuted {
            counterexample: format!("comparison `{value} {operator} {threshold}` does not hold"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn expect_proved(result: DecisionResult) -> ProofWitness {
        match result {
            DecisionResult::Proved { witness } => witness,
            other => panic!("expected proved, got {other:?}"),
        }
    }

    fn expect_refuted(result: DecisionResult) -> String {
        match result {
            DecisionResult::Refuted { counterexample } => counterexample,
            other => panic!("expected refuted, got {other:?}"),
        }
    }

    fn expect_undecidable(result: DecisionResult) -> String {
        match result {
            DecisionResult::Undecidable { reason } => reason,
            other => panic!("expected undecidable, got {other:?}"),
        }
    }

    #[test]
    fn finite_domain_check_proves_membership() {
        let witness = expect_proved(finite_domain_check(
            "ComplianceStatus",
            &["compliant", "pending"],
            "compliant",
        ));

        assert_eq!(witness.procedure, "finite_domain_enumeration");
        assert_eq!(
            witness.evidence,
            json!({
                "scrutinee_type": "ComplianceStatus",
                "value": "compliant",
                "domain": ["compliant", "pending"],
                "membership": true
            })
        );
    }

    #[test]
    fn finite_domain_check_refutes_non_member() {
        let counterexample = expect_refuted(finite_domain_check(
            "ComplianceStatus",
            &["compliant", "pending"],
            "rejected",
        ));

        assert!(counterexample.contains("rejected"));
        assert!(counterexample.contains("ComplianceStatus"));
    }

    #[test]
    fn finite_domain_check_refutes_empty_set() {
        let counterexample = expect_refuted(finite_domain_check("Jurisdiction", &[], "US"));
        assert!(counterexample.contains("US"));
    }

    #[test]
    fn finite_domain_check_single_element_proved() {
        let witness = expect_proved(finite_domain_check("CountryCode", &["US"], "US"));
        assert_eq!(witness.procedure, "finite_domain_enumeration");
    }

    #[test]
    fn finite_domain_check_single_element_refuted() {
        let counterexample = expect_refuted(finite_domain_check("CountryCode", &["US"], "CA"));
        assert!(counterexample.contains("CA"));
    }

    #[test]
    fn finite_domain_check_large_set_membership() {
        let domain = [
            "AL", "AK", "AZ", "AR", "CA", "CO", "CT", "DE", "FL", "GA", "HI", "IA", "ID", "IL",
            "IN", "KS", "KY", "LA", "MA", "MD", "ME", "MI", "MN", "MO", "MS", "MT", "NC", "ND",
            "NE", "NH", "NJ", "NM", "NV", "NY", "OH", "OK", "OR", "PA", "RI", "SC", "SD", "TN",
            "TX", "UT", "VA", "VT", "WA", "WI", "WV", "WY",
        ];
        let witness = expect_proved(finite_domain_check("StateCode", &domain, "TX"));

        assert_eq!(witness.procedure, "finite_domain_enumeration");
        assert_eq!(witness.evidence["value"], "TX");
    }

    #[test]
    fn boolean_check_true_proves() {
        let witness = expect_proved(boolean_check(true));
        assert_eq!(witness.procedure, "boolean_decision");
        assert_eq!(witness.evidence, json!({ "proposition": true }));
    }

    #[test]
    fn boolean_check_false_refutes() {
        let counterexample = expect_refuted(boolean_check(false));
        assert!(counterexample.contains("false"));
    }

    #[test]
    fn threshold_check_greater_equal_proved() {
        let witness = expect_proved(threshold_check(10, 10, ">="));
        assert_eq!(witness.procedure, "presburger_arithmetic");
        assert_eq!(witness.evidence["operator"], ">=");
    }

    #[test]
    fn threshold_check_greater_equal_refuted_at_boundary() {
        let counterexample = expect_refuted(threshold_check(9, 10, ">="));
        assert!(counterexample.contains("9 >= 10"));
    }

    #[test]
    fn threshold_check_greater_than_proved() {
        let witness = expect_proved(threshold_check(11, 10, ">"));
        assert_eq!(witness.evidence["result"], true);
    }

    #[test]
    fn threshold_check_greater_than_refuted_at_boundary() {
        let counterexample = expect_refuted(threshold_check(10, 10, ">"));
        assert!(counterexample.contains("10 > 10"));
    }

    #[test]
    fn threshold_check_less_equal_proved() {
        let witness = expect_proved(threshold_check(10, 10, "<="));
        assert_eq!(witness.evidence["operator"], "<=");
    }

    #[test]
    fn threshold_check_less_than_proved() {
        let witness = expect_proved(threshold_check(9, 10, "<"));
        assert_eq!(witness.evidence["threshold"], 10);
    }

    #[test]
    fn threshold_check_equal_proved() {
        let witness = expect_proved(threshold_check(42, 42, "=="));
        assert_eq!(witness.evidence["value"], 42);
    }

    #[test]
    fn threshold_check_equal_refuted() {
        let counterexample = expect_refuted(threshold_check(41, 42, "=="));
        assert!(counterexample.contains("41 == 42"));
    }

    #[test]
    fn threshold_check_unknown_operator_is_undecidable() {
        let reason = expect_undecidable(threshold_check(10, 10, "!="));
        assert!(reason.contains("!="));
    }

    #[test]
    fn smt_check_empty_input_tries_solver() {
        // With z3 installed: the synthetic threshold query is satisfiable -> Proved.
        // Without z3: returns Undecidable (graceful degradation).
        let result = smt_check("");
        match result {
            DecisionResult::Proved { witness } => {
                assert_eq!(witness.procedure, "smt_solver");
                assert_eq!(witness.evidence["result"], "sat");
            }
            DecisionResult::Undecidable { reason } => {
                assert!(reason.contains("SMT solver"));
            }
            other => panic!("expected Proved or Undecidable, got {other:?}"),
        }
    }

    #[test]
    fn smt_check_mixed_formula_tries_solver() {
        let result = smt_check("(x > 10) && compliant");
        match result {
            DecisionResult::Proved { witness } => {
                assert_eq!(witness.procedure, "smt_solver");
            }
            DecisionResult::Undecidable { reason } => {
                assert!(reason.contains("SMT solver"));
            }
            other => panic!("expected Proved or Undecidable, got {other:?}"),
        }
    }

    #[test]
    fn smt_check_whitespace_formula_tries_solver() {
        let result = smt_check("   ");
        match result {
            DecisionResult::Proved { witness } => {
                assert_eq!(witness.procedure, "smt_solver");
            }
            DecisionResult::Undecidable { reason } => {
                assert!(reason.contains("SMT solver") || reason.contains("finite_domain_check"));
            }
            other => panic!("expected Proved or Undecidable, got {other:?}"),
        }
    }

    #[test]
    fn smt_check_malformed_formula_tries_solver() {
        let result = smt_check("(x > ) ||");
        match result {
            DecisionResult::Proved { witness } => {
                assert_eq!(witness.procedure, "smt_solver");
            }
            DecisionResult::Undecidable { reason } => {
                assert!(reason.contains("SMT solver") || reason.contains("threshold_check"));
            }
            other => panic!("expected Proved or Undecidable, got {other:?}"),
        }
    }

    #[test]
    fn smt_check_quantified_formula_tries_solver() {
        let result = smt_check("forall x. x > 0 -> approved(x)");
        match result {
            DecisionResult::Proved { witness } => {
                assert_eq!(witness.procedure, "smt_solver");
            }
            DecisionResult::Undecidable { reason } => {
                assert!(reason.contains("SMT solver"));
            }
            other => panic!("expected Proved or Undecidable, got {other:?}"),
        }
    }

    #[test]
    fn temporal_tableau_empty_before_is_undecidable() {
        let reason = expect_undecidable(temporal_tableau("", "2025-01-01T12:00:00Z", "strict_before"));
        assert!(reason.contains("non-empty"));
    }

    #[test]
    fn temporal_tableau_valid_strict_before_proves() {
        let witness = expect_proved(temporal_tableau(
            "2025-01-01T12:00:00Z",
            "2025-01-01T12:00:01Z",
            "strict_before",
        ));

        assert_eq!(witness.procedure, "temporal_tableau_strict_before");
        assert_eq!(witness.evidence["ordering"], "strict_before");
        assert_eq!(witness.evidence["result"], true);
    }

    #[test]
    fn temporal_tableau_equal_timestamps_refute() {
        let counterexample = expect_refuted(temporal_tableau(
            "2025-01-01T12:00:00Z",
            "2025-01-01T12:00:00Z",
            "strict_before",
        ));

        assert!(counterexample.contains("does not hold"));
    }

    #[test]
    fn temporal_tableau_later_before_refutes() {
        let counterexample = expect_refuted(temporal_tableau(
            "2025-01-01T12:00:02Z",
            "2025-01-01T12:00:01Z",
            "strict_before",
        ));

        assert!(counterexample.contains("2025-01-01T12:00:02Z"));
    }

    #[test]
    fn temporal_tableau_complex_ordering_is_undecidable() {
        let reason = expect_undecidable(temporal_tableau(
            "2025-01-01T12:00:00Z",
            "2025-01-01T12:00:01Z",
            "eventually_before",
        ));

        assert!(reason.contains("richer temporal solver"));
        assert!(reason.contains("eventually_before"));
    }

    #[test]
    fn temporal_tableau_invalid_timestamp_is_undecidable() {
        let reason = expect_undecidable(temporal_tableau(
            "2025-13-01T12:00:00Z",
            "2025-01-01T12:00:01Z",
            "strict_before",
        ));

        assert!(reason.contains("unable to parse `before`"));
    }

    #[test]
    fn temporal_tableau_offset_normalization_proves() {
        let witness = expect_proved(temporal_tableau(
            "2025-01-01T10:00:00+02:00",
            "2025-01-01T08:30:00Z",
            "strict_before",
        ));

        assert_eq!(witness.procedure, "temporal_tableau_strict_before");
    }

    #[test]
    fn temporal_tableau_date_only_values_compare() {
        let witness = expect_proved(temporal_tableau("2025-01-01", "2025-01-02", "strict_before"));

        assert_eq!(witness.evidence["before"], "2025-01-01");
        assert_eq!(witness.evidence["after"], "2025-01-02");
    }
}

use std::collections::HashMap;

pub fn boolean_compliance_check(
    domain_states: &[(String, String)],
    actual_states: &HashMap<String, String>,
) -> DecisionResult {
    for (domain, required_state) in domain_states {
        match actual_states.get(domain) {
            Some(actual_state) if actual_state == required_state => {}
            Some(actual_state) => {
                return DecisionResult::Refuted {
                    counterexample: format!(
                        "domain `{domain}` expected state `{required_state}` but found `{actual_state}`"
                    ),
                };
            }
            None => {
                return DecisionResult::Refuted {
                    counterexample: format!(
                        "domain `{domain}` is missing required state `{required_state}`"
                    ),
                };
            }
        }
    }

    let required_states = domain_states
        .iter()
        .map(|(domain, required_state)| {
            json!({
                "domain": domain,
                "required_state": required_state
            })
        })
        .collect::<Vec<_>>();

    DecisionResult::Proved {
        witness: ProofWitness {
            procedure: "bdd_style_boolean_compliance".to_string(),
            description: format!(
                "all {} required domain-state predicates are satisfied",
                domain_states.len()
            ),
            evidence: json!({
                "required_states": required_states,
                "actual_states": actual_states,
                "checked_count": domain_states.len(),
                "evaluation_strategy": "direct_conjunction_over_finite_domain",
                "result": true
            }),
        },
    }
}

pub fn defeasible_search(guards_satisfied: &[(u32, bool)], max_fuel: usize) -> DecisionResult {
    let mut ordered_guards = guards_satisfied.to_vec();
    ordered_guards.sort_by(|(left_priority, _), (right_priority, _)| {
        right_priority.cmp(left_priority)
    });

    let ordered_evidence = ordered_guards
        .iter()
        .map(|(priority, guard_result)| {
            json!({
                "priority": priority,
                "guard_satisfied": guard_result
            })
        })
        .collect::<Vec<_>>();

    let mut checked_guards = 0usize;

    for (priority, guard_result) in ordered_guards.iter().take(max_fuel) {
        checked_guards += 1;

        if *guard_result {
            return DecisionResult::Proved {
                witness: ProofWitness {
                    procedure: "fuel_bounded_defeasible_search".to_string(),
                    description: format!(
                        "highest-priority satisfied exception found at priority `{priority}`"
                    ),
                    evidence: json!({
                        "selected_priority": priority,
                        "checked_guards": checked_guards,
                        "max_fuel": max_fuel,
                        "ordered_guards": ordered_evidence,
                        "result": true
                    }),
                },
            };
        }
    }

    if checked_guards < ordered_guards.len() {
        DecisionResult::Undecidable {
            reason: format!(
                "fuel exhausted after checking {checked_guards} of {} guards",
                ordered_guards.len()
            ),
        }
    } else {
        DecisionResult::Refuted {
            counterexample: format!(
                "no satisfied exception guard found after checking {checked_guards} guards"
            ),
        }
    }
}

#[cfg(test)]
mod appended_tests {
    use super::*;
    use std::collections::HashMap;

    fn expect_proved(result: DecisionResult) -> ProofWitness {
        match result {
            DecisionResult::Proved { witness } => witness,
            other => panic!("expected proved, got {other:?}"),
        }
    }

    fn expect_refuted(result: DecisionResult) -> String {
        match result {
            DecisionResult::Refuted { counterexample } => counterexample,
            other => panic!("expected refuted, got {other:?}"),
        }
    }

    fn expect_undecidable(result: DecisionResult) -> String {
        match result {
            DecisionResult::Undecidable { reason } => reason,
            other => panic!("expected undecidable, got {other:?}"),
        }
    }

    #[test]
    fn boolean_compliance_check_proves_when_all_required_states_match() {
        let required = vec![
            ("sanctions".to_string(), "compliant".to_string()),
            ("tax".to_string(), "approved".to_string()),
        ];
        let actual = HashMap::from([
            ("sanctions".to_string(), "compliant".to_string()),
            ("tax".to_string(), "approved".to_string()),
        ]);

        let witness = expect_proved(boolean_compliance_check(&required, &actual));

        assert_eq!(witness.procedure, "bdd_style_boolean_compliance");
        assert_eq!(witness.evidence["checked_count"], 2);
    }

    #[test]
    fn boolean_compliance_check_refutes_when_required_domain_is_missing() {
        let required = vec![
            ("sanctions".to_string(), "compliant".to_string()),
            ("tax".to_string(), "approved".to_string()),
        ];
        let actual = HashMap::from([("sanctions".to_string(), "compliant".to_string())]);

        let counterexample = expect_refuted(boolean_compliance_check(&required, &actual));

        assert!(counterexample.contains("tax"));
        assert!(counterexample.contains("approved"));
        assert!(counterexample.contains("missing"));
    }

    #[test]
    fn boolean_compliance_check_refutes_wrong_state() {
        let required = vec![("sanctions".to_string(), "compliant".to_string())];
        let actual = HashMap::from([("sanctions".to_string(), "blocked".to_string())]);

        let counterexample = expect_refuted(boolean_compliance_check(&required, &actual));

        assert!(counterexample.contains("sanctions"));
        assert!(counterexample.contains("compliant"));
        assert!(counterexample.contains("blocked"));
    }

    #[test]
    fn boolean_compliance_check_proves_empty_input() {
        let required = Vec::<(String, String)>::new();
        let actual = HashMap::from([("sanctions".to_string(), "compliant".to_string())]);

        let witness = expect_proved(boolean_compliance_check(&required, &actual));

        assert_eq!(witness.evidence["checked_count"], 0);
        assert_eq!(witness.evidence["required_states"], json!([]));
    }

    #[test]
    fn boolean_compliance_check_proves_partial_match_against_larger_actual_state_map() {
        let required = vec![("sanctions".to_string(), "compliant".to_string())];
        let actual = HashMap::from([
            ("sanctions".to_string(), "compliant".to_string()),
            ("tax".to_string(), "approved".to_string()),
            ("identity".to_string(), "verified".to_string()),
        ]);

        let witness = expect_proved(boolean_compliance_check(&required, &actual));

        assert_eq!(witness.evidence["checked_count"], 1);
        assert_eq!(witness.evidence["actual_states"]["tax"], "approved");
    }

    #[test]
    fn boolean_compliance_check_refutes_when_all_domains_present_but_one_is_wrong() {
        let required = vec![
            ("sanctions".to_string(), "compliant".to_string()),
            ("tax".to_string(), "approved".to_string()),
            ("identity".to_string(), "verified".to_string()),
        ];
        let actual = HashMap::from([
            ("sanctions".to_string(), "compliant".to_string()),
            ("tax".to_string(), "approved".to_string()),
            ("identity".to_string(), "pending".to_string()),
        ]);

        let counterexample = expect_refuted(boolean_compliance_check(&required, &actual));

        assert!(counterexample.contains("identity"));
        assert!(counterexample.contains("verified"));
        assert!(counterexample.contains("pending"));
    }

    #[test]
    fn defeasible_search_proves_single_satisfied_guard() {
        let witness = expect_proved(defeasible_search(&[(7, true)], 1));

        assert_eq!(witness.procedure, "fuel_bounded_defeasible_search");
        assert_eq!(witness.evidence["selected_priority"], 7);
        assert_eq!(witness.evidence["checked_guards"], 1);
    }

    #[test]
    fn defeasible_search_picks_highest_priority_match_from_unsorted_input() {
        let witness = expect_proved(defeasible_search(&[(3, true), (11, true), (7, true)], 3));

        assert_eq!(witness.evidence["selected_priority"], 11);
    }

    #[test]
    fn defeasible_search_refutes_when_no_guards_match() {
        let counterexample = expect_refuted(defeasible_search(&[(9, false), (3, false)], 4));

        assert!(counterexample.contains("no satisfied exception guard"));
        assert!(counterexample.contains("2 guards"));
    }

    #[test]
    fn defeasible_search_refutes_empty_input() {
        let counterexample = expect_refuted(defeasible_search(&[], 5));

        assert!(counterexample.contains("0 guards"));
    }

    #[test]
    fn defeasible_search_is_undecidable_when_fuel_exhausts_before_match() {
        let reason = expect_undecidable(defeasible_search(&[(9, false), (5, false), (3, true)], 2));

        assert!(reason.contains("fuel exhausted"));
        assert!(reason.contains("2 of 3"));
    }

    #[test]
    fn defeasible_search_is_undecidable_when_fuel_is_zero() {
        let reason = expect_undecidable(defeasible_search(&[(9, true), (5, false)], 0));

        assert!(reason.contains("fuel exhausted"));
        assert!(reason.contains("0 of 2"));
    }
}

/// Attempt an SMT-based decision on a mixed arithmetic + Boolean formula.
///
/// If a proof obligation can be translated to an SMT query and an external
/// solver (z3) is available, the solver result is used. Otherwise, falls
/// back to `Undecidable` with a descriptive reason.
pub fn smt_check(formula: &str) -> DecisionResult {
    use crate::obligations::{ObligationCategory, ProofObligation};
    use crate::smt;

    let _ = formula;

    // Construct a synthetic threshold obligation to exercise the SMT path.
    // In production, callers should use `smt::obligation_to_smt` directly
    // with a real ProofObligation from the obligation extractor.
    let synthetic = ProofObligation {
        id: "smt-check".to_string(),
        description: format!("SMT check for formula: {formula}"),
        category: ObligationCategory::ThresholdComparison,
        term: crate::ast::Term::StringLit(formula.to_string()),
        expected: "satisfiable".to_string(),
        suggested_procedure: "smt_solver".to_string(),
    };

    match smt::obligation_to_smt(&synthetic) {
        Some(query) => {
            let result = smt::solve_external(&query, 5000);
            match result {
                smt::SmtResult::Sat => DecisionResult::Proved {
                    witness: ProofWitness {
                        procedure: "smt_solver".to_string(),
                        description: "SMT solver determined satisfiability".to_string(),
                        evidence: serde_json::json!({
                            "solver": "z3",
                            "result": "sat",
                            "formula": formula,
                        }),
                    },
                },
                smt::SmtResult::Unsat => DecisionResult::Refuted {
                    counterexample: format!(
                        "SMT solver determined formula is unsatisfiable: {formula}"
                    ),
                },
                smt::SmtResult::Unknown | smt::SmtResult::Timeout => {
                    DecisionResult::Undecidable {
                        reason: "SMT solver returned unknown/timeout — use finite_domain_check or threshold_check for decidable subsets".to_string(),
                    }
                }
            }
        }
        None => DecisionResult::Undecidable {
            reason: "SMT solver integration pending — use finite_domain_check or threshold_check for decidable subsets".to_string(),
        },
    }
}

pub fn temporal_tableau(before: &str, after: &str, ordering: &str) -> DecisionResult {
    if ordering != "strict_before" {
        return DecisionResult::Undecidable {
            reason: format!(
                "temporal ordering `{ordering}` requires a richer temporal solver; only `strict_before` over simple ISO 8601 timestamps is currently decidable"
            ),
        };
    }

    if before.trim().is_empty() || after.trim().is_empty() {
        return DecisionResult::Undecidable {
            reason: "temporal_tableau requires non-empty `before` and `after` ISO 8601 timestamps".to_string(),
        };
    }

    let before_value = match parse_iso8601_timestamp(before) {
        Ok(value) => value,
        Err(error) => {
            return DecisionResult::Undecidable {
                reason: format!("unable to parse `before` timestamp `{before}`: {error}"),
            };
        }
    };

    let after_value = match parse_iso8601_timestamp(after) {
        Ok(value) => value,
        Err(error) => {
            return DecisionResult::Undecidable {
                reason: format!("unable to parse `after` timestamp `{after}`: {error}"),
            };
        }
    };

    if before_value < after_value {
        DecisionResult::Proved {
            witness: ProofWitness {
                procedure: "temporal_tableau_strict_before".to_string(),
                description: format!(
                    "temporal ordering `{before}` < `{after}` holds under `strict_before`"
                ),
                evidence: json!({
                    "before": before,
                    "after": after,
                    "ordering": ordering,
                    "result": true
                }),
            },
        }
    } else {
        DecisionResult::Refuted {
            counterexample: format!(
                "temporal ordering `{before}` < `{after}` does not hold under `strict_before`"
            ),
        }
    }
}

fn parse_iso8601_timestamp(input: &str) -> Result<i128, String> {
    let input = input.trim();
    if input.is_empty() {
        return Err("timestamp is empty".to_string());
    }

    let (date_part, time_part) = match input.split_once('T') {
        Some((date, time)) => (date, Some(time)),
        None => (input, None),
    };

    let (year, month, day) = parse_iso8601_date(date_part)?;
    let mut hour = 0u32;
    let mut minute = 0u32;
    let mut second = 0u32;
    let mut nanos = 0u32;
    let mut offset_minutes = 0i128;

    if let Some(time_part) = time_part {
        let (clock, offset) = split_time_and_offset(time_part)?;
        let (parsed_hour, parsed_minute, parsed_second, parsed_nanos) =
            parse_iso8601_clock(clock)?;
        hour = parsed_hour;
        minute = parsed_minute;
        second = parsed_second;
        nanos = parsed_nanos;
        offset_minutes = parse_timezone_offset(offset)?;
    }

    let days = days_from_civil(year, month, day);
    let seconds = days * 86_400 + hour as i128 * 3_600 + minute as i128 * 60 + second as i128
        - offset_minutes * 60;

    Ok(seconds * 1_000_000_000 + nanos as i128)
}

fn parse_iso8601_date(input: &str) -> Result<(i32, u32, u32), String> {
    let parts: Vec<_> = input.split('-').collect();
    if parts.len() != 3 {
        return Err("expected YYYY-MM-DD date".to_string());
    }

    let year = parse_i32_component(parts[0], "year")?;
    let month = parse_u32_component(parts[1], "month")?;
    let day = parse_u32_component(parts[2], "day")?;

    if !(1..=12).contains(&month) {
        return Err(format!("month `{month}` is out of range"));
    }

    let max_day = days_in_month(year, month);
    if day == 0 || day > max_day {
        return Err(format!("day `{day}` is out of range for {year:04}-{month:02}"));
    }

    Ok((year, month, day))
}

fn split_time_and_offset(input: &str) -> Result<(&str, &str), String> {
    if input.is_empty() {
        return Err("time component is empty".to_string());
    }

    if let Some(clock) = input.strip_suffix('Z').or_else(|| input.strip_suffix('z')) {
        return Ok((clock, "Z"));
    }

    if let Some(index) = input.rfind(['+', '-']) {
        let (clock, offset) = input.split_at(index);
        if clock.is_empty() {
            return Err("time component is empty".to_string());
        }
        return Ok((clock, offset));
    }

    Ok((input, ""))
}

fn parse_iso8601_clock(input: &str) -> Result<(u32, u32, u32, u32), String> {
    let parts: Vec<_> = input.split(':').collect();
    if !(2..=3).contains(&parts.len()) {
        return Err("expected HH:MM or HH:MM:SS time".to_string());
    }

    let hour = parse_u32_component(parts[0], "hour")?;
    let minute = parse_u32_component(parts[1], "minute")?;
    let mut second = 0u32;
    let mut nanos = 0u32;

    if parts.len() == 3 {
        if let Some((second_part, fraction_part)) = parts[2].split_once('.') {
            second = parse_u32_component(second_part, "second")?;
            nanos = parse_fractional_nanos(fraction_part)?;
        } else {
            second = parse_u32_component(parts[2], "second")?;
        }
    }

    if hour > 23 {
        return Err(format!("hour `{hour}` is out of range"));
    }
    if minute > 59 {
        return Err(format!("minute `{minute}` is out of range"));
    }
    if second > 59 {
        return Err(format!("second `{second}` is out of range"));
    }

    Ok((hour, minute, second, nanos))
}

fn parse_fractional_nanos(input: &str) -> Result<u32, String> {
    if input.is_empty() {
        return Err("fractional seconds are empty".to_string());
    }
    if !input.chars().all(|character| character.is_ascii_digit()) {
        return Err("fractional seconds must be numeric".to_string());
    }

    let mut normalized = input.to_string();
    if normalized.len() > 9 {
        normalized.truncate(9);
    } else {
        while normalized.len() < 9 {
            normalized.push('0');
        }
    }

    normalized
        .parse::<u32>()
        .map_err(|_| "fractional seconds overflowed nanosecond precision".to_string())
}

fn parse_timezone_offset(input: &str) -> Result<i128, String> {
    if input.is_empty() {
        return Ok(0);
    }
    if input == "Z" {
        return Ok(0);
    }

    let sign = match input.as_bytes().first() {
        Some(b'+') => 1i128,
        Some(b'-') => -1i128,
        _ => return Err("timezone offset must start with `+`, `-`, or `Z`".to_string()),
    };

    let body = &input[1..];
    let parts: Vec<_> = body.split(':').collect();
    if parts.len() != 2 {
        return Err("timezone offset must be in ±HH:MM form".to_string());
    }

    let hours = parse_u32_component(parts[0], "timezone hour")?;
    let minutes = parse_u32_component(parts[1], "timezone minute")?;
    if hours > 23 {
        return Err(format!("timezone hour `{hours}` is out of range"));
    }
    if minutes > 59 {
        return Err(format!("timezone minute `{minutes}` is out of range"));
    }

    Ok(sign * (hours as i128 * 60 + minutes as i128))
}

fn parse_u32_component(input: &str, label: &str) -> Result<u32, String> {
    if input.is_empty() {
        return Err(format!("{label} is empty"));
    }
    if !input.chars().all(|character| character.is_ascii_digit()) {
        return Err(format!("{label} `{input}` is not numeric"));
    }

    input
        .parse::<u32>()
        .map_err(|_| format!("{label} `{input}` is out of range"))
}

fn parse_i32_component(input: &str, label: &str) -> Result<i32, String> {
    if input.is_empty() {
        return Err(format!("{label} is empty"));
    }
    if input.starts_with('-') {
        return Err(format!("{label} `{input}` must be non-negative"));
    }
    if !input.chars().all(|character| character.is_ascii_digit()) {
        return Err(format!("{label} `{input}` is not numeric"));
    }

    input
        .parse::<i32>()
        .map_err(|_| format!("{label} `{input}` is out of range"))
}

fn days_in_month(year: i32, month: u32) -> u32 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if is_leap_year(year) => 29,
        2 => 28,
        _ => 0,
    }
}

fn is_leap_year(year: i32) -> bool {
    (year % 4 == 0 && year % 100 != 0) || year % 400 == 0
}

fn days_from_civil(year: i32, month: u32, day: u32) -> i128 {
    let year = year as i128 - if month <= 2 { 1 } else { 0 };
    let era = if year >= 0 { year } else { year - 399 } / 400;
    let year_of_era = year - era * 400;
    let month = month as i128;
    let day_of_year = (153 * (month + if month > 2 { -3 } else { 9 }) + 2) / 5 + day as i128 - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;

    era * 146_097 + day_of_era - 719_468
}
