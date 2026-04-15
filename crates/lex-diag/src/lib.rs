//! # mez-diag — Structured Diagnostic Ontology
//!
//! Every Lex elaboration failure maps to a finite, named, legally meaningful
//! error category. Error messages are published in controlled English, not
//! Lex syntax. The compiler is considered incomplete if it produces an error
//! outside the ontology — error ontology coverage is a soundness property.

pub mod category;
pub mod coverage;
pub mod error;
pub mod render;

pub use category::DiagnosticCategory;
pub use coverage::{check_ontology_coverage, find_uncovered_indices};
pub use error::{DiagError, DiagnosticReport, Severity, StructuredDiagnostic};
pub use render::{render_diagnostic, render_diagnostic_oneline, DiagContext, SourceSpan};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_categories_have_nonempty_display_name() {
        let categories = [
            DiagnosticCategory::TypeMismatch,
            DiagnosticCategory::UnboundVariable,
            DiagnosticCategory::NotAFunction,
            DiagnosticCategory::NotASort,
            DiagnosticCategory::CannotInfer,
            DiagnosticCategory::AdmissibilityViolation,
            DiagnosticCategory::AmbiguousOverload,
            DiagnosticCategory::FuelExhaustion,
            DiagnosticCategory::TerminationFailure,
            DiagnosticCategory::SubstitutionBlowup,
            DiagnosticCategory::LevelOverflow,
            DiagnosticCategory::TemporalStratificationViolation,
            DiagnosticCategory::LevelUnsatisfiable,
            DiagnosticCategory::LevelCyclicDependency,
            DiagnosticCategory::MetaRuleViolation,
            DiagnosticCategory::TribunalScopeViolation,
            DiagnosticCategory::InsufficientAuthority,
            DiagnosticCategory::ScopeClosureFailure,
            DiagnosticCategory::EffectViolation,
            DiagnosticCategory::BranchSensitiveWithoutUnlock,
            DiagnosticCategory::DefeasibilityConflict,
            DiagnosticCategory::RuleDefeated,
            DiagnosticCategory::DiscretionHoleUnfilled,
            DiagnosticCategory::PrincipleConflict,
            DiagnosticCategory::FiberCompositionConflict,
            DiagnosticCategory::RefinementPreservationFailure,
            DiagnosticCategory::ProofObligationFailed,
            DiagnosticCategory::ObligationNotDischarged,
            DiagnosticCategory::UnknownAccessor,
            DiagnosticCategory::NotAVerdict,
            DiagnosticCategory::NoMatchingBranch,
            DiagnosticCategory::NotALambda,
            DiagnosticCategory::EmptyDecisionTable,
            DiagnosticCategory::InvalidVerdict,
            DiagnosticCategory::EmptyAccessor,
            DiagnosticCategory::ThresholdTooLarge,
            DiagnosticCategory::ClockBeforeEpoch,
            DiagnosticCategory::CanonicalizationFailed,
            DiagnosticCategory::UnknownJurisdiction,
            DiagnosticCategory::SchemaIncompatible,
            DiagnosticCategory::Unknown,
        ];
        for cat in &categories {
            let name = cat.display_name();
            assert!(!name.is_empty(), "display_name empty for {:?}", cat);
        }
    }

    #[test]
    fn all_categories_have_nonempty_description() {
        let categories = [
            DiagnosticCategory::TypeMismatch,
            DiagnosticCategory::UnboundVariable,
            DiagnosticCategory::FuelExhaustion,
            DiagnosticCategory::TemporalStratificationViolation,
            DiagnosticCategory::EffectViolation,
            DiagnosticCategory::DefeasibilityConflict,
            DiagnosticCategory::DiscretionHoleUnfilled,
            DiagnosticCategory::PrincipleConflict,
            DiagnosticCategory::FiberCompositionConflict,
            DiagnosticCategory::RefinementPreservationFailure,
            DiagnosticCategory::Unknown,
        ];
        for cat in &categories {
            let desc = cat.description();
            assert!(!desc.is_empty(), "description empty for {:?}", cat);
            // Controlled English: should not contain Lex-internal syntax
            assert!(
                !desc.contains("De Bruijn") && !desc.contains("Pi-type"),
                "description for {:?} contains internal jargon: {}",
                cat,
                desc,
            );
        }
    }

    #[test]
    fn only_rule_defeated_is_not_hard_error() {
        assert!(!DiagnosticCategory::RuleDefeated.is_hard_error());
        assert!(DiagnosticCategory::TypeMismatch.is_hard_error());
        assert!(DiagnosticCategory::Unknown.is_hard_error());
    }

    #[test]
    fn only_unknown_is_unknown() {
        assert!(DiagnosticCategory::Unknown.is_unknown());
        assert!(!DiagnosticCategory::TypeMismatch.is_unknown());
        assert!(!DiagnosticCategory::FuelExhaustion.is_unknown());
    }

    #[test]
    fn structured_diagnostic_display() {
        let diag = StructuredDiagnostic::error(
            DiagnosticCategory::TypeMismatch,
            DiagContext::new("aml.lex", 10, 5),
        )
        .with_detail("expected Bool, found Verdict");
        let s = format!("{}", diag);
        assert!(s.contains("error:"));
        assert!(s.contains("[Type Mismatch]"));
        assert!(s.contains("aml.lex:10:5"));
        assert!(s.contains("expected Bool, found Verdict"));
    }

    #[test]
    fn diagnostic_report_counts() {
        let mut report = DiagnosticReport::new("test-suite");
        report.push(StructuredDiagnostic::error(
            DiagnosticCategory::TypeMismatch,
            DiagContext::new("a.lex", 1, 1),
        ));
        report.push(StructuredDiagnostic::warning(
            DiagnosticCategory::RuleDefeated,
            DiagContext::new("b.lex", 2, 1),
        ));
        report.push(StructuredDiagnostic::info(
            DiagnosticCategory::RuleDefeated,
            DiagContext::new("c.lex", 3, 1),
        ));
        report.push(StructuredDiagnostic::error(
            DiagnosticCategory::EffectViolation,
            DiagContext::new("d.lex", 4, 1),
        ));

        assert_eq!(report.error_count(), 2);
        assert_eq!(report.warning_count(), 1);
        assert_eq!(report.info_count(), 1);
        assert_eq!(report.len(), 4);
        assert!(!report.is_empty());
        assert!(report.has_errors());
        assert!(!report.has_unknown_categories());

        let summary = report.summary();
        assert!(summary.contains("2 error(s)"));
        assert!(summary.contains("1 warning(s)"));
        assert!(summary.contains("1 info(s)"));
    }

    #[test]
    fn diagnostic_report_detects_unknown() {
        let mut report = DiagnosticReport::new("incomplete-compiler");
        report.push(StructuredDiagnostic::error(
            DiagnosticCategory::Unknown,
            DiagContext::new("mystery.lex", 99, 1),
        ));
        assert!(report.has_unknown_categories());
        assert!(!check_ontology_coverage(&report.diagnostics));
    }

    #[test]
    fn diagnostic_report_empty_summary() {
        let report = DiagnosticReport::new("clean-module");
        assert!(!report.has_errors());
        assert!(report.is_empty());
        assert!(report.summary().contains("no diagnostics"));
    }

    #[test]
    fn severity_display_and_blocking() {
        assert_eq!(Severity::Error.display_name(), "error");
        assert_eq!(Severity::Warning.display_name(), "warning");
        assert_eq!(Severity::Info.display_name(), "info");
        assert!(Severity::Error.is_blocking());
        assert!(!Severity::Warning.is_blocking());
        assert!(!Severity::Info.is_blocking());
    }

    #[test]
    fn category_serde_roundtrip() {
        let cat = DiagnosticCategory::TemporalStratificationViolation;
        let json = serde_json::to_string(&cat).expect("serialize category");
        let back: DiagnosticCategory =
            serde_json::from_str(&json).expect("deserialize category");
        assert_eq!(cat, back);
    }

    #[test]
    fn structured_diagnostic_serde_roundtrip() {
        let diag = StructuredDiagnostic::error(
            DiagnosticCategory::FiberCompositionConflict,
            DiagContext::new("corridors/pk-ae.lex", 7, 12)
                .with_jurisdiction("pk")
                .with_snippet("fiber activate pk-aml"),
        )
        .with_suggestion("Deactivate the existing pk-aml fiber before activating a new one.")
        .with_detail("fiber pk-aml already active on entity E-1234");

        let json = serde_json::to_string(&diag).expect("serialize diagnostic");
        let back: StructuredDiagnostic =
            serde_json::from_str(&json).expect("deserialize diagnostic");
        assert_eq!(back.category, DiagnosticCategory::FiberCompositionConflict);
        assert_eq!(back.severity, Severity::Error);
        assert_eq!(back.context.file, "corridors/pk-ae.lex");
        assert_eq!(back.context.jurisdiction.as_deref(), Some("pk"));
        assert!(back.suggestion.is_some());
        assert!(back.detail.is_some());
    }

    #[test]
    fn source_span_from_diag_context() {
        let ctx = DiagContext::new("test.lex", 42, 7);
        let span = SourceSpan::from(&ctx);
        assert_eq!(span.file, "test.lex");
        assert_eq!(span.line, 42);
        assert_eq!(span.column, 7);
    }

    #[test]
    fn category_display_impl() {
        let cat = DiagnosticCategory::DiscretionHoleUnfilled;
        let s = format!("{}", cat);
        assert_eq!(s, "Discretion Hole Unfilled");
    }
}
