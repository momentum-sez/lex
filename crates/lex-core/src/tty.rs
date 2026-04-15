//! lex-tty — Structured text projection for accessibility.
//!
//! Canonical plain-text linearization of every proof term, descent obstruction,
//! and discretion hole, consumable by screen readers and line-based terminals.
//!
//! This module provides text rendering functions that produce accessible
//! representations of Lex objects without requiring a graphical IDE.

use serde::{Deserialize, Serialize};

/// A text-projected Lex term for accessible rendering.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TtyProjection {
    /// The term's type category (proof, obstruction, hole, fiber, etc.).
    pub category: TermCategory,
    /// Plain-text rendering for screen readers.
    pub text: String,
    /// Indentation depth for structure.
    pub depth: usize,
    /// Child projections (for hierarchical terms).
    pub children: Vec<TtyProjection>,
}

/// Category of term being projected.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TermCategory {
    /// A proof step.
    ProofStep,
    /// A descent obstruction.
    DescentObstruction,
    /// A typed discretion hole requiring human judgment.
    DiscretionHole,
    /// A fiber declaration.
    FiberDeclaration,
    /// A rule evaluation result.
    RuleResult,
    /// An error diagnostic.
    Diagnostic,
    /// A principle balancing step.
    PrincipleBalancing,
    /// Structural grouping (no semantic content).
    Group,
}

impl TtyProjection {
    /// Create a new projection.
    pub fn new(category: TermCategory, text: impl Into<String>) -> Self {
        Self {
            category,
            text: text.into(),
            depth: 0,
            children: Vec::new(),
        }
    }

    /// Add a child projection.
    pub fn with_child(mut self, child: TtyProjection) -> Self {
        self.children.push(child);
        self
    }

    /// Set depth.
    pub fn at_depth(mut self, depth: usize) -> Self {
        self.depth = depth;
        self
    }

    /// Render to plain text with indentation.
    ///
    /// Each line is indented by `depth * 2` spaces. Children are rendered
    /// at `depth + 1`. Suitable for screen readers and line-based terminals.
    pub fn render(&self) -> String {
        let mut output = String::new();
        self.render_to(&mut output, self.depth);
        output
    }

    fn render_to(&self, output: &mut String, depth: usize) {
        let indent = "  ".repeat(depth);
        let prefix = match self.category {
            TermCategory::ProofStep => "[PROOF]",
            TermCategory::DescentObstruction => "[OBSTRUCTION]",
            TermCategory::DiscretionHole => "[DISCRETION]",
            TermCategory::FiberDeclaration => "[FIBER]",
            TermCategory::RuleResult => "[RESULT]",
            TermCategory::Diagnostic => "[DIAG]",
            TermCategory::PrincipleBalancing => "[BALANCE]",
            TermCategory::Group => "",
        };
        if prefix.is_empty() {
            output.push_str(&format!("{indent}{}\n", self.text));
        } else {
            output.push_str(&format!("{indent}{prefix} {}\n", self.text));
        }
        for child in &self.children {
            child.render_to(output, depth + 1);
        }
    }
}

/// Render a discretion hole as accessible text.
///
/// Format: "DISCRETION HOLE: [type] required from [authority]"
pub fn render_discretion_hole(judgment_type: &str, authority: &str) -> TtyProjection {
    TtyProjection::new(
        TermCategory::DiscretionHole,
        format!("Judgment of type '{judgment_type}' required from authority '{authority}'. Mechanical computation stops here."),
    )
}

/// Render a descent obstruction as accessible text.
pub fn render_obstruction(domains: &[String], zone_a: &str, zone_b: &str) -> TtyProjection {
    let domain_list = domains.join(", ");
    TtyProjection::new(
        TermCategory::DescentObstruction,
        format!("Composition conflict between {zone_a} and {zone_b} in domains: {domain_list}"),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn discretion_hole_rendering() {
        let proj = render_discretion_hole("FitAndProperDetermination", "ADGM_FSRA");
        let text = proj.render();
        assert!(text.contains("DISCRETION"));
        assert!(text.contains("FitAndProperDetermination"));
        assert!(text.contains("ADGM_FSRA"));
        assert!(text.contains("Mechanical computation stops here"));
    }

    #[test]
    fn obstruction_rendering() {
        let proj = render_obstruction(
            &["Sanctions".to_string(), "AML".to_string()],
            "ADGM",
            "Seychelles",
        );
        let text = proj.render();
        assert!(text.contains("OBSTRUCTION"));
        assert!(text.contains("Sanctions, AML"));
        assert!(text.contains("ADGM"));
        assert!(text.contains("Seychelles"));
    }

    #[test]
    fn hierarchical_rendering() {
        let proj = TtyProjection::new(TermCategory::Group, "Fiber evaluation results")
            .with_child(TtyProjection::new(TermCategory::RuleResult, "AML: Compliant"))
            .with_child(TtyProjection::new(TermCategory::RuleResult, "Sanctions: Pending"))
            .with_child(
                TtyProjection::new(TermCategory::DiscretionHole, "KYC determination required")
                    .with_child(TtyProjection::new(
                        TermCategory::Group,
                        "Authority: Seychelles FSA",
                    )),
            );
        let text = proj.render();
        assert!(text.contains("Fiber evaluation results"));
        assert!(text.contains("AML: Compliant"));
        assert!(text.contains("KYC determination required"));
        assert!(text.contains("Authority: Seychelles FSA"));
    }

    #[test]
    fn empty_text_renders() {
        let proj = TtyProjection::new(TermCategory::Group, "");
        let text = proj.render();
        assert!(!text.is_empty()); // At least a newline.
    }
}
