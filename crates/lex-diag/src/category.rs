use serde::{Deserialize, Serialize};

/// Finite, named, legally meaningful error categories for Lex elaboration failures.
///
/// Every error emitted by the Lex compiler pipeline (parser, de Bruijn, type checker,
/// effect checker, level solver, evaluator, decision table compiler, obligation extractor,
/// certificate issuer) maps to exactly one variant here. If a new error does not fit any
/// variant, the ontology must be extended — emitting `Unknown` is a soundness violation.
///
/// Error ontology coverage is a soundness property: the compiler is considered incomplete
/// if it produces an error outside this ontology.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DiagnosticCategory {
    // ── Type system ──────────────────────────────────────────────────

    /// Type mismatch: expected one type, found another during bidirectional
    /// type checking. Maps to `TypeError::Mismatch`.
    TypeMismatch,

    /// A variable name or de Bruijn index is not bound by any enclosing binder.
    /// Maps to `TypeError::UnboundVar`, `DebruijnError::Unbound`.
    UnboundVariable,

    /// A term was applied as a function but does not have a Pi (function) type.
    /// Maps to `TypeError::NotAFunction`.
    NotAFunction,

    /// Expected a sort (Type/Kind) but found a non-sort term.
    /// Maps to `TypeError::NotASort`.
    NotASort,

    /// A bare term (e.g., unannotated lambda) cannot be type-inferred in synthesis
    /// mode. Maps to `TypeError::CannotInfer`.
    CannotInfer,

    /// The term violates the admissibility fragment — it is outside the decidable
    /// subset accepted by the type checker. Maps to `TypeError::Admissibility`.
    AdmissibilityViolation,

    /// Overloaded name resolves to more than one binding with distinct types.
    /// Requires explicit qualification to disambiguate.
    AmbiguousOverload,

    // ── Termination and resource limits ──────────────────────────────

    /// Evaluation or reduction fuel exhausted — the term requires too many
    /// reduction steps. Maps to `TypeError::ReductionLimitExceeded`,
    /// `EvalError::ReductionLimitExceeded`.
    FuelExhaustion,

    /// Recursion depth exceeded during type checking, de Bruijn conversion,
    /// or evaluation. Maps to `TypeError::RecursionLimitExceeded`,
    /// `DebruijnError::RecursionLimit`, `EvalError::RecursionLimitExceeded`.
    TerminationFailure,

    /// Substitution produced a term exceeding the maximum AST node count — likely
    /// an exponential blowup. Maps to `TypeError::SubstitutionBlowup`.
    SubstitutionBlowup,

    /// Universe level overflow — a level exceeds the omega limit or u64 range.
    /// Maps to `TypeError::LevelOverflow`, `LevelError::OmegaLimitViolation`.
    LevelOverflow,

    // ── Temporal stratification ─────────────────────────────────────

    /// Temporal constraint violation: a term references a time stratum it is not
    /// permitted to access (frozen historical time vs. derived legal time).
    /// Maps to Lex temporal sort violations.
    TemporalStratificationViolation,

    /// Level constraint set is unsatisfiable — the temporal ordering demanded by
    /// the rule body cannot be realized. Maps to `LevelError::Unsatisfiable`.
    LevelUnsatisfiable,

    /// A positive cycle was detected in the level constraint graph.
    /// Maps to `LevelError::CyclicDependency`.
    LevelCyclicDependency,

    /// A meta-rule at level l quantifies over Rule_{l'} where l' >= l.
    /// Maps to `LevelError::MetaRuleViolation`.
    MetaRuleViolation,

    // ── Authority and scope ─────────────────────────────────────────

    /// A tribunal or authority scope constraint is violated — the operation
    /// exceeds the authority granted to the current evaluator.
    TribunalScopeViolation,

    /// Authority insufficient for the attempted operation (read/write beyond
    /// granted scope). Maps to general authority checks.
    InsufficientAuthority,

    /// A scope closure failed — a bound variable escaped its enclosing scope.
    ScopeClosureFailure,

    // ── Effects ─────────────────────────────────────────────────────

    /// Effect row subsumption failure: the term's effects are not a subset of
    /// the permitted effect row. Maps to `EffectError::SubsumptionFailure`.
    EffectViolation,

    /// A branch-sensitive effect row was used without an explicit unlock.
    /// Maps to `EffectError::BranchSensitiveWithoutUnlock`.
    BranchSensitiveWithoutUnlock,

    // ── Defeasibility ───────────────────────────────────────────────

    /// Two or more defeasible rules fire simultaneously with conflicting
    /// conclusions and no priority ordering resolves the conflict.
    DefeasibilityConflict,

    /// A defeasible rule was defeated by an exception — informational, not
    /// necessarily an error, but recorded when the defeat is unexpected.
    RuleDefeated,

    // ── Discretion and principles ───────────────────────────────────

    /// A typed discretion hole in the Lex program has not been filled by a
    /// human judgment — the rule cannot evaluate mechanically.
    DiscretionHoleUnfilled,

    /// Two or more legal principles are in balance and no balancing step
    /// resolves which takes priority.
    PrincipleConflict,

    // ── Fibers and composition ──────────────────────────────────────

    /// A fiber activation conflicts with an already-active fiber on the same
    /// entity or corridor — concurrent activation is not permitted.
    FiberCompositionConflict,

    /// A refinement (subtyping) preservation property was violated during
    /// cross-jurisdictional composition — the target jurisdiction's rules
    /// are not a refinement of the source.
    RefinementPreservationFailure,

    // ── Obligations ─────────────────────────────────────────────────

    /// A proof obligation emitted by the obligation extractor could not be
    /// discharged by the SMT solver or external verifier.
    ProofObligationFailed,

    /// An obligation has not been discharged within its deadline.
    ObligationNotDischarged,

    // ── Evaluation ──────────────────────────────────────────────────

    /// An accessor referenced by the rule is not present in the runtime context.
    /// Maps to `EvalError::UnknownAccessor`.
    UnknownAccessor,

    /// The term reduced to a form that is not a recognized verdict constant.
    /// Maps to `EvalError::NotAVerdict`.
    NotAVerdict,

    /// A match expression had no matching branch for the scrutinee value.
    /// Maps to `EvalError::NoMatchingBranch`.
    NoMatchingBranch,

    /// The rule is not a lambda abstraction at the top level.
    /// Maps to `EvalError::NotALambda`.
    NotALambda,

    // ── Decision table compilation ──────────────────────────────────

    /// The decision table is empty — no rules were provided.
    /// Maps to `CompileError::EmptyTable`.
    EmptyDecisionTable,

    /// An invalid verdict string was used (must be Compliant/NonCompliant/Pending).
    /// Maps to `CompileError::InvalidVerdict`.
    InvalidVerdict,

    /// An accessor path in a decision table condition is empty.
    /// Maps to `CompileError::EmptyAccessor`.
    EmptyAccessor,

    /// A threshold value in a decision table condition exceeds the maximum
    /// allowed value. Maps to `CompileError::ThresholdTooLarge`.
    ThresholdTooLarge,

    // ── Certificate issuance ────────────────────────────────────────

    /// The system clock is before the UNIX epoch — cannot issue a timestamp.
    /// Maps to `CertificateError::ClockBeforeEpoch`.
    ClockBeforeEpoch,

    /// Canonical serialization of the compliance certificate failed.
    /// Maps to `CertificateError::CanonicalizationFailed`.
    CanonicalizationFailed,

    // ── Jurisdiction ────────────────────────────────────────────────

    /// The jurisdiction identifier is not recognized by any loaded zone manifest.
    UnknownJurisdiction,

    /// Schema version is incompatible — the Lex rule file targets a schema
    /// version that this compiler does not support.
    SchemaIncompatible,

    // ── Catch-all (soundness violation if ever emitted in production) ─

    /// An error occurred that does not map to any known category.
    /// Emitting this variant in production is a soundness violation:
    /// it means the diagnostic ontology is incomplete.
    Unknown,
}

impl DiagnosticCategory {
    /// Returns the controlled-English display name for this category.
    pub fn display_name(&self) -> &'static str {
        match self {
            // Type system
            Self::TypeMismatch => "Type Mismatch",
            Self::UnboundVariable => "Unbound Variable",
            Self::NotAFunction => "Not a Function",
            Self::NotASort => "Not a Sort",
            Self::CannotInfer => "Cannot Infer Type",
            Self::AdmissibilityViolation => "Admissibility Violation",
            Self::AmbiguousOverload => "Ambiguous Overload",

            // Termination / resources
            Self::FuelExhaustion => "Reduction Fuel Exhausted",
            Self::TerminationFailure => "Recursion Limit Exceeded",
            Self::SubstitutionBlowup => "Substitution Size Exceeded",
            Self::LevelOverflow => "Universe Level Overflow",

            // Temporal
            Self::TemporalStratificationViolation => "Temporal Stratification Violation",
            Self::LevelUnsatisfiable => "Level Constraints Unsatisfiable",
            Self::LevelCyclicDependency => "Level Cyclic Dependency",
            Self::MetaRuleViolation => "Meta-Rule Level Violation",

            // Authority / scope
            Self::TribunalScopeViolation => "Tribunal Scope Violation",
            Self::InsufficientAuthority => "Insufficient Authority",
            Self::ScopeClosureFailure => "Scope Closure Failure",

            // Effects
            Self::EffectViolation => "Effect Violation",
            Self::BranchSensitiveWithoutUnlock => "Branch-Sensitive Effect Without Unlock",

            // Defeasibility
            Self::DefeasibilityConflict => "Defeasibility Conflict",
            Self::RuleDefeated => "Defeasible Rule Defeated",

            // Discretion / principles
            Self::DiscretionHoleUnfilled => "Discretion Hole Unfilled",
            Self::PrincipleConflict => "Principle Conflict",

            // Fibers / composition
            Self::FiberCompositionConflict => "Fiber Composition Conflict",
            Self::RefinementPreservationFailure => "Refinement Preservation Failure",

            // Obligations
            Self::ProofObligationFailed => "Proof Obligation Failed",
            Self::ObligationNotDischarged => "Obligation Not Discharged",

            // Evaluation
            Self::UnknownAccessor => "Unknown Accessor",
            Self::NotAVerdict => "Not a Verdict",
            Self::NoMatchingBranch => "No Matching Branch",
            Self::NotALambda => "Not a Lambda",

            // Decision table
            Self::EmptyDecisionTable => "Empty Decision Table",
            Self::InvalidVerdict => "Invalid Verdict",
            Self::EmptyAccessor => "Empty Accessor",
            Self::ThresholdTooLarge => "Threshold Too Large",

            // Certificate
            Self::ClockBeforeEpoch => "Clock Before Epoch",
            Self::CanonicalizationFailed => "Canonicalization Failed",

            // Jurisdiction
            Self::UnknownJurisdiction => "Unknown Jurisdiction",
            Self::SchemaIncompatible => "Schema Version Incompatible",

            // Catch-all
            Self::Unknown => "Unknown Error Category",
        }
    }

    /// Returns a controlled-English description suitable for non-technical readers
    /// (regulators, compliance officers). Avoids Lex syntax.
    pub fn description(&self) -> &'static str {
        match self {
            Self::TypeMismatch => {
                "A rule expected a value of one kind but received a value of a different kind. \
                 For example, a rule expected a monetary amount but received a text string."
            }
            Self::UnboundVariable => {
                "A rule references a name that is not defined in the current scope. \
                 This usually means the rule references data that has not been provided."
            }
            Self::NotAFunction => {
                "A value was used as if it were a rule or computation, but it is a plain value \
                 that cannot be applied to arguments."
            }
            Self::NotASort => {
                "A classification was expected (such as a type or kind) but a plain value was \
                 found instead."
            }
            Self::CannotInfer => {
                "The system cannot determine the type of a term without an explicit annotation. \
                 The rule must be annotated with its expected type."
            }
            Self::AdmissibilityViolation => {
                "A term falls outside the fragment of logic that the system can decide \
                 mechanically. Human review or reformulation is required."
            }
            Self::AmbiguousOverload => {
                "A name refers to more than one definition with different types. \
                 The reference must be qualified to indicate which definition is intended."
            }
            Self::FuelExhaustion => {
                "Evaluating the rule required more computation steps than the allowed budget. \
                 The rule may contain an unbounded loop or excessively deep nesting."
            }
            Self::TerminationFailure => {
                "The rule nesting depth exceeded the safety limit. \
                 This prevents runaway computation on deeply recursive rules."
            }
            Self::SubstitutionBlowup => {
                "Substituting values into the rule produced an expression exceeding the maximum \
                 allowed size. This is typically caused by exponential expansion in nested rules."
            }
            Self::LevelOverflow => {
                "A universe level in the rule hierarchy exceeded the maximum permitted depth. \
                 Rules about rules about rules may not nest this deeply."
            }
            Self::TemporalStratificationViolation => {
                "A rule references a time period it is not permitted to access. Historical \
                 (frozen) facts and derived legal conclusions occupy different time strata \
                 and must not be mixed incorrectly."
            }
            Self::LevelUnsatisfiable => {
                "The ordering constraints on rule levels cannot all be satisfied simultaneously. \
                 The rule hierarchy contains contradictory ordering requirements."
            }
            Self::LevelCyclicDependency => {
                "The rule level ordering contains a circular dependency: rule A requires rule B \
                 at a higher level, which in turn requires rule A at a higher level."
            }
            Self::MetaRuleViolation => {
                "A meta-rule (a rule about rules) quantifies over rules at a level that is not \
                 strictly lower than itself, violating the stratification hierarchy."
            }
            Self::TribunalScopeViolation => {
                "The operation exceeds the jurisdictional authority of the evaluating tribunal. \
                 A tribunal may only evaluate rules within its granted scope."
            }
            Self::InsufficientAuthority => {
                "The current evaluator does not have sufficient authority to perform the \
                 requested read or write operation on the referenced data."
            }
            Self::ScopeClosureFailure => {
                "A locally-defined name escaped its enclosing scope, creating a dangling \
                 reference. The rule must be restructured so all names remain within their scope."
            }
            Self::EffectViolation => {
                "The rule performs an operation (such as reading or writing external data) that \
                 is not permitted in its current context. The allowed operations are specified \
                 by the effect annotation."
            }
            Self::BranchSensitiveWithoutUnlock => {
                "A branch-sensitive operation was invoked without first obtaining an explicit \
                 unlock. Branch-sensitive effects require acknowledgment before use."
            }
            Self::DefeasibilityConflict => {
                "Two or more rules fire simultaneously with conflicting conclusions, and no \
                 priority ordering or exception mechanism resolves the conflict."
            }
            Self::RuleDefeated => {
                "A rule that would otherwise apply was overridden by a more specific exception. \
                 The exception takes priority under the defeasibility ordering."
            }
            Self::DiscretionHoleUnfilled => {
                "The rule contains a discretion hole — a point where human judgment is required. \
                 The system cannot proceed mechanically until the hole is filled."
            }
            Self::PrincipleConflict => {
                "Two or more legal principles are in tension and no balancing step has been \
                 provided to determine which takes priority in this context."
            }
            Self::FiberCompositionConflict => {
                "A compliance fiber cannot be activated because it conflicts with an already-active \
                 fiber on the same entity or corridor."
            }
            Self::RefinementPreservationFailure => {
                "The target jurisdiction's rules are not a refinement of the source jurisdiction's \
                 rules. Cross-jurisdictional composition requires that the target is at least as \
                 restrictive as the source on every relevant domain."
            }
            Self::ProofObligationFailed => {
                "A proof obligation emitted by the rule could not be discharged. The required \
                 property could not be verified mechanically."
            }
            Self::ObligationNotDischarged => {
                "An obligation has not been fulfilled within its required timeframe."
            }
            Self::UnknownAccessor => {
                "The rule references a data field that is not present in the current evaluation \
                 context. The entity or transaction may be missing the required field."
            }
            Self::NotAVerdict => {
                "The rule evaluated to a value that is not a recognized compliance verdict \
                 (Compliant, NonCompliant, Pending, NotApplicable, or Exempt)."
            }
            Self::NoMatchingBranch => {
                "A case analysis in the rule did not have a branch matching the actual value. \
                 The rule may need a default or wildcard case."
            }
            Self::NotALambda => {
                "The top-level rule is not a function. Rules must be defined as functions that \
                 accept an evaluation context and produce a verdict."
            }
            Self::EmptyDecisionTable => {
                "The decision table contains no rules. At least one rule is required to \
                 produce a compliance determination."
            }
            Self::InvalidVerdict => {
                "A verdict value in the rule is not one of the recognized compliance verdicts: \
                 Compliant, NonCompliant, or Pending."
            }
            Self::EmptyAccessor => {
                "An accessor path in the decision table is empty. Every condition must reference \
                 at least one data field."
            }
            Self::ThresholdTooLarge => {
                "A numeric threshold in the decision table exceeds the maximum permitted value. \
                 This limit prevents excessive branch enumeration during compilation."
            }
            Self::ClockBeforeEpoch => {
                "The system clock reports a time before the UNIX epoch (January 1, 1970). \
                 A valid timestamp is required for certificate issuance."
            }
            Self::CanonicalizationFailed => {
                "The compliance certificate could not be serialized into its canonical form. \
                 This is an internal error that prevents certificate issuance."
            }
            Self::UnknownJurisdiction => {
                "The referenced jurisdiction is not recognized by any loaded zone manifest. \
                 The jurisdiction identifier may be misspelled or the zone may not be deployed."
            }
            Self::SchemaIncompatible => {
                "The rule file targets a schema version that this compiler does not support. \
                 The rule file or the compiler must be updated."
            }
            Self::Unknown => {
                "An error occurred that does not map to any known diagnostic category. \
                 This indicates the diagnostic ontology is incomplete and must be extended."
            }
        }
    }

    /// Returns true if this category represents a hard error that blocks compilation.
    /// Warnings and informational categories (e.g., `RuleDefeated`) return false.
    pub fn is_hard_error(&self) -> bool {
        !matches!(self, Self::RuleDefeated)
    }

    /// Returns true if this is the `Unknown` sentinel — a soundness violation.
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }
}

impl std::fmt::Display for DiagnosticCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display_name())
    }
}
