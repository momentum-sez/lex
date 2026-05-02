//! Ontology coverage checking.
//!
//! Error ontology coverage is a soundness property: the compiler is considered
//! incomplete if it produces any diagnostic with category `Unknown`. This module
//! provides the coverage check that CI gates and release attestation can call.

use crate::error::StructuredDiagnostic;

/// Returns `true` if every diagnostic in the slice has a known (non-`Unknown`) category.
///
/// Returns `false` if any diagnostic's category is `Unknown`, which means the
/// diagnostic ontology is incomplete — the compiler has produced an error that
/// does not map to any named, legally meaningful category.
///
/// An empty slice is considered covered (vacuously true).
pub fn check_ontology_coverage(diagnostics: &[StructuredDiagnostic]) -> bool {
    !diagnostics.iter().any(|d| d.is_unknown_category())
}

/// Returns the indices of all diagnostics with `Unknown` category.
///
/// If the returned vector is non-empty, the ontology is incomplete and must
/// be extended before the compiler can be considered sound.
pub fn find_uncovered_indices(diagnostics: &[StructuredDiagnostic]) -> Vec<usize> {
    diagnostics
        .iter()
        .enumerate()
        .filter(|(_, d)| d.is_unknown_category())
        .map(|(i, _)| i)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::category::DiagnosticCategory;
    use crate::error::Severity;
    use crate::render::DiagContext;

    fn make_diag(cat: DiagnosticCategory) -> StructuredDiagnostic {
        StructuredDiagnostic {
            category: cat,
            context: DiagContext::new("test.lex", 1, 1),
            severity: Severity::Error,
            suggestion: None,
            detail: None,
        }
    }

    #[test]
    fn empty_slice_is_covered() {
        assert!(check_ontology_coverage(&[]));
    }

    #[test]
    fn all_known_categories_covered() {
        let diags = vec![
            make_diag(DiagnosticCategory::TypeMismatch),
            make_diag(DiagnosticCategory::UnboundVariable),
            make_diag(DiagnosticCategory::EffectViolation),
        ];
        assert!(check_ontology_coverage(&diags));
    }

    #[test]
    fn unknown_category_fails_coverage() {
        let diags = vec![
            make_diag(DiagnosticCategory::TypeMismatch),
            make_diag(DiagnosticCategory::Unknown),
        ];
        assert!(!check_ontology_coverage(&diags));
    }

    #[test]
    fn find_uncovered_returns_correct_indices() {
        let diags = vec![
            make_diag(DiagnosticCategory::TypeMismatch),
            make_diag(DiagnosticCategory::Unknown),
            make_diag(DiagnosticCategory::FuelExhaustion),
            make_diag(DiagnosticCategory::Unknown),
        ];
        let indices = find_uncovered_indices(&diags);
        assert_eq!(indices, vec![1, 3]);
    }
}
