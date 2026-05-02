use serde::{Deserialize, Serialize};

use crate::category::DiagnosticCategory;

/// Source-location context for a diagnostic message.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiagContext {
    /// The Lex source file (or rule identifier) where the diagnostic originates.
    pub file: String,
    /// 1-based line number within the file.
    pub line: usize,
    /// 1-based column number within the line.
    pub column: usize,
    /// An optional snippet of the source text surrounding the error site.
    pub snippet: Option<String>,
    /// The jurisdiction context, if the diagnostic is jurisdiction-specific.
    pub jurisdiction: Option<String>,
}

impl DiagContext {
    /// Creates a new diagnostic context.
    pub fn new(file: impl Into<String>, line: usize, column: usize) -> Self {
        Self {
            file: file.into(),
            line,
            column,
            snippet: None,
            jurisdiction: None,
        }
    }

    /// Builder: attach a source snippet.
    pub fn with_snippet(mut self, snippet: impl Into<String>) -> Self {
        self.snippet = Some(snippet.into());
        self
    }

    /// Builder: attach a jurisdiction context.
    pub fn with_jurisdiction(mut self, jurisdiction: impl Into<String>) -> Self {
        self.jurisdiction = Some(jurisdiction.into());
        self
    }
}

/// Source location for a diagnostic (legacy compat, re-exported).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceSpan {
    pub file: String,
    pub line: usize,
    pub column: usize,
}

impl From<&DiagContext> for SourceSpan {
    fn from(ctx: &DiagContext) -> Self {
        Self {
            file: ctx.file.clone(),
            line: ctx.line,
            column: ctx.column,
        }
    }
}

/// Renders a diagnostic category and context into a controlled-English message.
///
/// The output is suitable for non-technical readers (regulators, compliance officers).
/// It never contains Lex syntax, de Bruijn indices, or internal type representations.
pub fn render_diagnostic(category: &DiagnosticCategory, context: &DiagContext) -> String {
    let mut parts = Vec::with_capacity(4);

    // Header: category display name
    parts.push(format!("[{}]", category.display_name()));

    // Location
    let location = if let Some(ref jurisdiction) = context.jurisdiction {
        format!(
            "at {}:{}:{} (jurisdiction: {})",
            context.file, context.line, context.column, jurisdiction,
        )
    } else {
        format!("at {}:{}:{}", context.file, context.line, context.column)
    };
    parts.push(location);

    // Description — the controlled-English explanation
    parts.push(category.description().to_string());

    // Snippet, if available
    if let Some(ref snippet) = context.snippet {
        parts.push(format!("Source: {}", snippet));
    }

    parts.join("\n")
}

/// Renders a diagnostic into a single-line summary suitable for log output.
pub fn render_diagnostic_oneline(category: &DiagnosticCategory, context: &DiagContext) -> String {
    let jurisdiction_suffix = context
        .jurisdiction
        .as_ref()
        .map(|j| format!(" [{}]", j))
        .unwrap_or_default();
    format!(
        "{}: {}:{}:{}{}: {}",
        category.display_name(),
        context.file,
        context.line,
        context.column,
        jurisdiction_suffix,
        // Use the first sentence of the description for the one-liner.
        category
            .description()
            .split(". ")
            .next()
            .unwrap_or(category.description()),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn render_basic_diagnostic() {
        let ctx = DiagContext::new("modules/lex/prospera/aml.lex", 42, 10);
        let msg = render_diagnostic(&DiagnosticCategory::TypeMismatch, &ctx);
        assert!(msg.contains("[Type Mismatch]"));
        assert!(msg.contains("modules/lex/prospera/aml.lex:42:10"));
        assert!(msg.contains("expected a value of one kind"));
    }

    #[test]
    fn render_with_jurisdiction_and_snippet() {
        let ctx = DiagContext::new("modules/lex/luxembourg/corporate.lex", 15, 3)
            .with_jurisdiction("lu")
            .with_snippet("let x = sanctions_check(entity)");
        let msg = render_diagnostic(&DiagnosticCategory::EffectViolation, &ctx);
        assert!(msg.contains("(jurisdiction: lu)"));
        assert!(msg.contains("Source: let x = sanctions_check(entity)"));
        assert!(msg.contains("not permitted in its current context"));
    }

    #[test]
    fn render_oneline() {
        let ctx = DiagContext::new("test.lex", 1, 1).with_jurisdiction("hn-prospera");
        let msg = render_diagnostic_oneline(&DiagnosticCategory::UnboundVariable, &ctx);
        assert!(msg.contains("Unbound Variable"));
        assert!(msg.contains("test.lex:1:1"));
        assert!(msg.contains("[hn-prospera]"));
    }
}
