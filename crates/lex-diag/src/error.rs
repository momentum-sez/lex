use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::category::DiagnosticCategory;
use crate::render::DiagContext;

/// Errors internal to the mez-diag crate itself (not Lex elaboration errors).
#[derive(Debug, Error)]
pub enum DiagError {
    #[error("unknown diagnostic category: {0}")]
    UnknownCategory(String),

    #[error("render failed: {0}")]
    RenderFailed(String),

    #[error("serialization error: {0}")]
    Serialization(#[from] serde_json::Error),
}

/// Severity of a structured diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Severity {
    /// Blocks compilation or evaluation. Must be resolved.
    Error,
    /// Does not block, but indicates a likely problem.
    Warning,
    /// Informational — e.g., a defeasible rule was defeated as expected.
    Info,
}

impl Severity {
    /// Returns the controlled-English display name.
    pub fn display_name(&self) -> &'static str {
        match self {
            Self::Error => "error",
            Self::Warning => "warning",
            Self::Info => "info",
        }
    }

    /// Returns true if this severity blocks compilation.
    pub fn is_blocking(&self) -> bool {
        matches!(self, Self::Error)
    }
}

impl std::fmt::Display for Severity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display_name())
    }
}

/// A structured diagnostic emitted by the Lex compilation pipeline.
///
/// Each diagnostic carries a named category from the finite ontology, a source
/// context, a severity, and an optional suggestion for resolution.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StructuredDiagnostic {
    /// The category from the finite diagnostic ontology.
    pub category: DiagnosticCategory,
    /// Source location and context.
    pub context: DiagContext,
    /// Severity: error, warning, or info.
    pub severity: Severity,
    /// An optional controlled-English suggestion for resolution.
    pub suggestion: Option<String>,
    /// An optional detail string with additional context (e.g., expected vs. found types).
    pub detail: Option<String>,
}

impl StructuredDiagnostic {
    /// Creates a new error-severity diagnostic.
    pub fn error(category: DiagnosticCategory, context: DiagContext) -> Self {
        Self {
            category,
            context,
            severity: Severity::Error,
            suggestion: None,
            detail: None,
        }
    }

    /// Creates a new warning-severity diagnostic.
    pub fn warning(category: DiagnosticCategory, context: DiagContext) -> Self {
        Self {
            category,
            context,
            severity: Severity::Warning,
            suggestion: None,
            detail: None,
        }
    }

    /// Creates a new info-severity diagnostic.
    pub fn info(category: DiagnosticCategory, context: DiagContext) -> Self {
        Self {
            category,
            context,
            severity: Severity::Info,
            suggestion: None,
            detail: None,
        }
    }

    /// Builder: attach a suggestion.
    pub fn with_suggestion(mut self, suggestion: impl Into<String>) -> Self {
        self.suggestion = Some(suggestion.into());
        self
    }

    /// Builder: attach a detail string.
    pub fn with_detail(mut self, detail: impl Into<String>) -> Self {
        self.detail = Some(detail.into());
        self
    }

    /// Returns true if this diagnostic's category is `Unknown` — a soundness violation.
    pub fn is_unknown_category(&self) -> bool {
        self.category.is_unknown()
    }
}

impl std::fmt::Display for StructuredDiagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: [{}] at {}:{}:{}",
            self.severity,
            self.category.display_name(),
            self.context.file,
            self.context.line,
            self.context.column,
        )?;
        if let Some(ref detail) = self.detail {
            write!(f, " — {}", detail)?;
        }
        Ok(())
    }
}

/// A collection of structured diagnostics with summary statistics.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiagnosticReport {
    /// All diagnostics in emission order.
    pub diagnostics: Vec<StructuredDiagnostic>,
    /// The source file or rule set that produced this report.
    pub source: String,
}

impl DiagnosticReport {
    /// Creates an empty report for the given source.
    pub fn new(source: impl Into<String>) -> Self {
        Self {
            diagnostics: Vec::new(),
            source: source.into(),
        }
    }

    /// Appends a diagnostic to the report.
    pub fn push(&mut self, diagnostic: StructuredDiagnostic) {
        self.diagnostics.push(diagnostic);
    }

    /// Returns the number of diagnostics at error severity.
    pub fn error_count(&self) -> usize {
        self.diagnostics
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .count()
    }

    /// Returns the number of diagnostics at warning severity.
    pub fn warning_count(&self) -> usize {
        self.diagnostics
            .iter()
            .filter(|d| d.severity == Severity::Warning)
            .count()
    }

    /// Returns the number of diagnostics at info severity.
    pub fn info_count(&self) -> usize {
        self.diagnostics
            .iter()
            .filter(|d| d.severity == Severity::Info)
            .count()
    }

    /// Returns true if the report contains any error-severity diagnostics.
    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| d.severity == Severity::Error)
    }

    /// Returns true if the report is empty (no diagnostics at all).
    pub fn is_empty(&self) -> bool {
        self.diagnostics.is_empty()
    }

    /// Returns the total number of diagnostics.
    pub fn len(&self) -> usize {
        self.diagnostics.len()
    }

    /// Returns true if any diagnostic has category `Unknown` — ontology is incomplete.
    pub fn has_unknown_categories(&self) -> bool {
        self.diagnostics.iter().any(|d| d.is_unknown_category())
    }

    /// Returns a controlled-English summary of the report.
    pub fn summary(&self) -> String {
        if self.diagnostics.is_empty() {
            return format!("{}: no diagnostics.", self.source);
        }
        format!(
            "{}: {} error(s), {} warning(s), {} info(s).",
            self.source,
            self.error_count(),
            self.warning_count(),
            self.info_count(),
        )
    }
}

impl std::fmt::Display for DiagnosticReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "--- Diagnostic Report: {} ---", self.source)?;
        for diag in &self.diagnostics {
            writeln!(f, "  {}", diag)?;
        }
        write!(f, "{}", self.summary())
    }
}
