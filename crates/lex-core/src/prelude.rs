//! Compliance prelude for the Lex admissible fragment.
//!
//! The current rule suites encode domain entities, statuses, and constructors
//! as `Term::Constant` nodes. This module provides the smallest global
//! signature needed to resolve those names inside [`crate::typecheck::Context`].
//!
//! All registered types live at universe level 0 (`Type_0`). Constructor
//! families partition the flat `ComplianceTag` namespace into semantic groups
//! (Jurisdiction, Status, EntityType, RiskLevel, LicenseType, etc.) so that
//! the type-checker can reject nonsensical pattern matches (e.g. matching
//! `audit_status` against a jurisdiction constructor like `ADGM`).

use crate::ast::Term;
use crate::typecheck::Context;

const CORE_TYPES: &[&str] = &[
    "IncorporationContext",
    "ComplianceVerdict",
    "SanctionsResult",
    "Bool",
    "Nat",
    "ComplianceTag",
    // 17 C.F.R. §230.503(a)(1) — Reg D Form D filing deadline arithmetic on
    // calendar-day Gregorian dates. Added for the usa/regulation_d_503.lex
    // rule corpus (typed discretion hole for first-sale-date attestation,
    // Rule 9 / §230.503(a)(1)). At universe level 0 like the other core
    // types; day arithmetic is left to the obligation daemon for now.
    "Date",
];

const VERDICT_CONSTRUCTORS: &[&str] = &["Compliant", "NonCompliant", "Pending"];
const BOOL_CONSTRUCTORS: &[&str] = &["True", "False"];
const NAT_CONSTRUCTORS: &[&str] = &["Zero"];

/// Prefix for the value-carrying non-zero-natural marker constructor name.
///
/// `Nat` has exactly one *named* prelude constructor, `Zero`. A positive
/// natural has no peano `Succ` constructor in the surface; instead the runtime
/// encodes a concrete positive count `n` as the synthetic constructor name
/// `"<prefix>n"` (e.g. `__NonZeroNat:2`). This is the SAME encoding the
/// evaluator produces for a positive `Nat` scrutinee
/// (`crate::evaluate`'s `runtime_value_to_constant_name`), so a Nat-literal
/// match pattern lowered to this name matches the evaluated scrutinee by exact
/// constructor-name equality — the existing match machinery, with no special
/// case. The prefix contains a `:` so it can never collide with an authored
/// constructor (a single identifier cannot lex with a `:` in it), and it never
/// equals `Zero`, so a positive natural still falls through `| Zero =>` to a
/// wildcard exactly as before.
///
/// This constant is the single source of truth for the marker shape; it MUST
/// stay byte-identical to `crate::evaluate`'s `NON_ZERO_NAT_PREFIX` (asserted
/// by the `nat_marker_prefix_matches_evaluator` test).
pub(crate) const NON_ZERO_NAT_PREFIX: &str = "__NonZeroNat:";

/// Returns `true` if `name` is a value-carrying non-zero-natural marker
/// constructor (`__NonZeroNat:<n>` for some natural `n`). Such a name is an
/// admissible *value pattern* of the `Nat` datatype — the positive-count
/// counterpart of the named `Zero` constructor.
pub(crate) fn is_non_zero_nat_marker(name: &str) -> bool {
    name.strip_prefix(NON_ZERO_NAT_PREFIX)
        .is_some_and(|rest| !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()))
}

/// Returns `true` if `name` is an admissible constructor of the `Nat` datatype:
/// either the named `Zero` constructor or a value-carrying positive-count
/// marker (`__NonZeroNat:<n>`).
pub(crate) fn is_nat_constructor(name: &str) -> bool {
    NAT_CONSTRUCTORS.contains(&name) || is_non_zero_nat_marker(name)
}

/// Encode a positive natural `n` as its value-carrying `Nat` marker
/// constructor name. The single canonical producer of the marker shape used by
/// the parser's Nat-literal pattern lowering, kept in lock-step with the
/// evaluator via [`NON_ZERO_NAT_PREFIX`].
pub(crate) fn encode_non_zero_nat_marker(n: u64) -> String {
    format!("{NON_ZERO_NAT_PREFIX}{n}")
}
const SANCTIONS_CONSTRUCTORS: &[&str] = &[
    "Clear",
    // ── G2 closure (2026-05-07) — MISSING-PRELUDE migration ──────────
    // SanctionsResult discriminator extensions surfaced by
    // modules/lex/cayman/sanctions_screening_loop.lex (rule body
    // `match ctx.sanctions_check return ComplianceVerdict with
    // | Clear => Compliant | Match => NonCompliant | PotentialMatch => Pending`).
    "Match",
    "PotentialMatch",
];

/// Constructor names that are *also* admissible members of the flat
/// `ComplianceTag` status-value universe, in addition to the primary
/// datatype they are registered/typed under.
///
/// `ComplianceTag` is the open universe of status-value tags a status
/// accessor (e.g. `economic_substance_status`) can return. The runtime
/// matches tag scrutinees purely by constructor name
/// ([`crate::evaluate`]'s `runtime_value_to_constant_name`), so a status
/// accessor can legitimately yield a value whose name coincides with a
/// constructor that the prelude *primarily* classifies elsewhere.
///
/// `Pending` is the one such overload in the published rule corpus: a
/// regulator-review-in-progress status is written `| Pending => …` against
/// status accessors (cayman / luxembourg economic-substance rules) while
/// `Pending` remains the indeterminate [`ComplianceVerdict`]. It is kept in
/// its primary `ComplianceVerdict` registration (so the `Pending` *constant*
/// types as a verdict and pure-verdict matches resolve unchanged); this set
/// only widens `ComplianceTag` *membership* for match admissibility, never
/// the registered type. No other constructor name collides across datatypes
/// (asserted by `no_unintended_constructor_collisions`).
const TAG_OVERLOADED_CONSTRUCTORS: &[&str] = &["Pending"];

const TAG_CONSTRUCTORS: &[&str] = &[
    "ADGM",
    "Active",
    "Adequate",
    "ArbitrationAvailable",
    "ArbitrationNotAvailable",
    "AdequateJurisdiction",
    "AgmDispensed",
    "AgmDue",
    "AgmHeld",
    "AgmOverdue",
    "AgreementInPlace",
    "AgreementPending",
    "AllApproved",
    "AmlCompliant",
    "AmlFailed",
    "AmlRemediationRequired",
    "Applied",
    "ApprovalPending",
    "AtLeast7Years",
    "AuditComplete",
    "AuditDue",
    "AuditExempt",
    "AuditOverdue",
    "AuditRequired",
    "BC",
    "Bearer",
    "BelowThreshold",
    "BreachNotified",
    "BreachNotNotified",
    "CapitalAdequate",
    "CapitalInsufficient",
    "CapitalPending",
    "Category1",
    "Category2",
    "Category3A",
    "Category3B",
    "Category3C",
    "Category4",
    "CddComplete",
    "CddExpired",
    "CddIncomplete",
    "ChangeOverdue",
    "ChangePendingWithin15Days",
    "CharterNotRegistered",
    "CharterPending",
    "CharterRegistered",
    "CnicNotVerified",
    "CnicPending",
    "CnicVerified",
    "CmsCorporateFinanceAdvice",
    "CmsCreditRating",
    "CmsCustodialServices",
    "CmsDealingCapitalMarkets",
    "CmsFundManagement",
    "CobsCompliant",
    "CobsUnderReview",
    "ConfirmationStatementFiled",
    "ConfirmationStatementOverdue",
    "ConsentNotObtained",
    "ConsentObtained",
    "CorrespondentDdComplete",
    "CorrespondentDdPending",
    "Daily",
    "DisclosureComplete",
    "DisclosureIncomplete",
    "DisclosureUnderReview",
    "DpCompliant",
    "DpNonCompliant",
    "DpRemediationPending",
    "DueSoon",
    "EddComplete",
    "EddIncomplete",
    "EddRequired",
    "EmploymentAgreementFiled",
    "EmploymentAgreementMissing",
    "EmploymentStandardsMet",
    "EmploymentStandardsNotMet",
    "Exempt",
    "ExemptLimitedOfferees",
    "ExemptMinimumSubscription",
    "ExemptProfessionalInvestor",
    "ExemptSmallOffer",
    "ExemptedCompany",
    "FcaApplied",
    "FdiApproved",
    "FdiRejected",
    "FdiScreeningPending",
    "FmuCompliant",
    "FmuInvestigationOpen",
    "FmuNonCompliant",
    "FcaAuthorized",
    "Filed",
    "FitAndProperFailed",
    "FitAndProperSatisfied",
    "FitAndProperUnderReview",
    "FullLicense",
    "GB",
    "Granted",
    "HN",
    "HK",
    "HighRisk",
    "HighRiskEddComplete",
    "HighRiskEddPending",
    "HighRiskProhibited",
    "IBC",
    "ImpactAssessmentComplete",
    "ImpactAssessmentRequired",
    "InadequateJurisdiction",
    "InPrincipleApproval",
    "InsufficientMajority",
    "JointVentureCompliant",
    "JointVentureExempt",
    "JointVentureRequired",
    "KY",
    "LU",
    "LateNotice",
    "LessThan7Years",
    "LicensedExchange",
    "Limited",
    "LowRisk",
    "Ltd",
    "MediumRisk",
    "MonitoringActive",
    "MonitoringLapsed",
    "Monthly",
    "NoExemption",
    "NoTransferMechanism",
    "NotApplicable",
    "NotFiled",
    "NotListed",
    "NotRegistered",
    "NotRestricted",
    "NotSatisfied",
    "NotarizedFiled",
    "NotarizedMissing",
    "NotarizedPending",
    "NtnNotVerified",
    "NtnPending",
    "NtnVerified",
    "OrdinaryResolution",
    "OriginatorInfoComplete",
    "OriginatorInfoMissing",
    "Overdue",
    "Paid",
    "PK",
    "PepClear",
    "PepIdentified",
    "PepIdentifiedEddComplete",
    "PepIdentifiedEddFailed",
    "PepIdentifiedEddPending",
    "PepNotIdentified",
    "ProfessionalFund",
    "ProfessionalObligationMet",
    "ProfessionalObligationNotMet",
    "PromotionApproved",
    "PromotionUnapproved",
    "ProspectusFiledForResale",
    "ProtectedCell",
    "PscChangeOverdue",
    "PscRegisterCurrent",
    "PscRegisterMissing",
    "PublicCompany",
    "PublicOffering",
    "Quarterly",
    "RbeCompliant",
    "RbeNonCompliant",
    "RbePending",
    "RcsNotRegistered",
    "RcsPending",
    "RcsRegistered",
    "RecordsCurrent",
    "RecordsExpired",
    "RegisterCurrent",
    "RegisterMissing",
    "Registered",
    "RepatriationApproved",
    "RepatriationDenied",
    "RepatriationPending",
    "Restricted",
    "RestrictionPeriodExpired",
    "RetentionCompliant",
    "RetentionNonCompliant",
    "Revoked",
    "SA",
    "SARL",
    "SC",
    "SG",
    "SarFiled",
    "SarNotFiled",
    "SarPending",
    "Satisfied",
    "SbpForexApproved",
    "SbpForexDenied",
    "SbpForexPending",
    "SecpNotRegistered",
    "SecpPending",
    "SecpRegistered",
    "Segregated",
    "SegregationPending",
    "SezApproved",
    "SezNotApproved",
    "SezPending",
    "SfcType1DealingSecurities",
    "SfcType4AdvisingSecurities",
    "SfcType6CorporateFinance",
    "SfcType9AssetManagement",
    "ShellBankDetected",
    "SifcApproved",
    "SifcNotApproved",
    "SifcPending",
    "SifcSectorApproved",
    "SifcSectorPending",
    "SifcSectorRestricted",
    "SifcTaxHolidayGranted",
    "SifcTaxHolidayIneligible",
    "SifcTaxHolidayPending",
    "SpecialLicense",
    "SpecialResolution75",
    "StrFiledWithFiu",
    "StrFiledWithNca",
    "StrNotRequired",
    "StrPendingFiling",
    "Suspended",
    "TaxExempt",
    "TaxNotRegistered",
    "TaxRegistered",
    "TransferMechanismInPlace",
    "UnderReview",
    "UnlicensedExchange",
    "VG",
    "Weekly",
    "Within14Days",
    "Within30Days",
    "WithinFilingDeadline",
    "WithinRestrictionPeriod",
    "WithinOneMonthOfAnniversary",
    // ── USA Reg D §230.503 constructor families (Phase 5.2 extension) ──
    //
    // These 28 constructors land the usa/regulation_d_503.lex rule surface.
    // They are grouped by family below rather than interleaved alphabetically
    // so the Reg D semantic bundle stays visible as one unit (per the
    // "Group new symbols by family" directive). Existing prelude entries
    // above remain in their original alphabetical layout.
    //
    // Family: ExemptionCode (17 C.F.R. §§230.501–230.506, §230.504, Sec 4(a)(2),
    // Regulation S, Regulation CF (17 C.F.R. §§227.100 et seq.), Regulation A
    // (17 C.F.R. §§230.251 et seq.); the existing `Registered` ShareForm
    // constructor is re-used for the fully-registered-offering match arm).
    "RegA",
    "RegCF",
    "RegS",
    "Rule504",
    "Rule506b",
    "Rule506c",
    "Section4a2",
    // Family: FormDFilingStatus (17 C.F.R. §230.503(a); issuer-side Form D
    // preparation lifecycle; existing `Filed` Status constructor is the
    // canonical terminal success state).
    "Drafted",
    "FiledLate",
    "NotDue",
    "ReadyForCounsel",
    "Superseded",
    // Family: FormDDeadlineStatus (17 C.F.R. §230.503(a)(1) — 15-day deadline
    // bucket produced by the obligation daemon from first-sale date +
    // calendar-day arithmetic).
    "NoFirstSale",
    "PastDeadline",
    "Within15Days",
    // Family: AccreditedVerificationStatus (17 C.F.R. §230.506(c)(2)(ii) —
    // Rule 506(c) reasonable-steps verification of accredited-investor
    // status; Rule 506(b) self-certification routes to NotRequired).
    "NotRequired",
    "VerificationComplete",
    "VerificationFailed",
    "VerificationPending",
    // Family: SolicitationStatus (17 C.F.R. §230.506(b)(1) vs §230.506(c) —
    // Rule 506(b) prohibits general solicitation; Rule 506(c) permits it).
    "NoSolicitation",
    "PermittedSolicitation506c",
    "ProhibitedSolicitation506b",
    // Family: BadActorStatus (17 C.F.R. §230.506(d) — covered-person
    // disqualifying-event screen; waivers granted on SEC good-cause showing
    // under §230.506(d)(2)(iii); existing `UnderReview` Status is re-used).
    "Disqualified",
    "NoDisqualification",
    "Waived",
    // Family: EdgarCredentialStatus (SEC EDGAR CIK/access-code provisioning
    // for Form D filing; counsel-mediated filing path for the manual-receipt
    // capture flow).
    "CounselFilingPath",
    "CredentialsAbsent",
    "CredentialsProvisioned",
    // ── G2 closure (2026-05-07) — MISSING-PRELUDE migration ──────────
    //
    // Constructors lifted out of `-- MISSING-PRELUDE: <name>` markers in
    // ~/kernel/modules/lex/{adgm,bermuda,bvi,cayman,de,eu,guernsey,
    // hong_kong,iom,jersey,luxembourg,prospera,singapore,uae,uk,usa}/*.lex.
    // Per the F51-LEX-COVERAGE convention (`F51-LEX-COVERAGE.md:139`)
    // each marker named a typed accessor or constructor that the kernel-
    // side Lex programs evaluate counsel-attested at runtime. This block
    // closes the typed seam so those programs can typecheck through the
    // prelude rather than relying on out-of-band counsel attestation.
    //
    // ── Family: Jurisdiction extensions ─────────────────────────────
    // Delaware (USA-state-level — DGCL §132 registered-office gate from
    // modules/lex/usa/states/us-de/dgcl_corporate_governance.lex Rule 12;
    // shipped as `USDE` to disambiguate from country-level codes; joins
    // the existing 10-jurisdiction set: ADGM/GB/HK/HN/KY/LU/PK/SC/SG/VG).
    "USDE",
    // Bermuda (BM), Jersey (JE), Guernsey (GG), Isle of Man (IM),
    // Germany (DE), European Union (EU). Used as harbor markers in
    // composed AML-CDD bundles (`modules/lex/aml_cdd_composition.lex`)
    // and per-jurisdiction PoA programs.
    "BM",
    "JE",
    "GG",
    "IM",
    "DE",
    "EU",
    "AE",
    "BV",
    // ── Family: AmlCddRegime ─────────────────────────────────────────
    // Per-jurisdiction AML-CDD regulation tags scrutinised by
    // `aml_cdd_jurisdiction` accessor matches in the Step-4 PoA
    // programs (`modules/lex/{cayman,uk,usa,...}/aml_cdd_*.lex`). Each
    // names the binding rule-set (statute / regulation / regulator
    // notice / handbook).
    "KyCimaAmlr",       // Cayman AML Regulations 2020 + CIMA Guidance Notes
    "BmBmaGuidance",    // Bermuda BMA AML/ATF Sector-Specific Guidance
    "JeJfscHandbook",   // Jersey JFSC AML/CFT Handbook
    "GgGfscHandbook",   // Guernsey GFSC Handbook for FSBs
    "ImIomfsaHandbook", // Isle of Man IOMFSA AML/CFT Handbook
    "VgFscCode",        // BVI FSC AML Regulations + Code of Practice
    "UkMlr2017",        // UK Money Laundering Regulations 2017
    "UsCipMinimum",     // USA Customer Identification Program (FinCEN minimum)
    "SgMasNotice626",   // Singapore MAS Notice 626 (Banks)
    "SgVccN01",         // Singapore VCC Act + MAS Notice VCC-N01
    "SgSfa04N02",       // Singapore SFA-04-N02 (Capital Markets)
    "HkAmloSch2",       // Hong Kong AMLO Schedule 2
    "HkHkmaGuideline",  // Hong Kong HKMA AML/CFT Guideline
    "HkSfcGuideline",   // Hong Kong SFC AML/CFT Guideline
    "DeGwG",            // Germany Geldwäschegesetz (GwG)
    "EuFiveAmld",       // EU 5th AML Directive (2018/843)
    "EuSixAmld",        // EU 6th AML Directive (2018/1673)
    "EuAmlr",           // EU AML Regulation (in force from 2027)
    "AeCbuaeStandards", // UAE Central Bank AML/CFT Standards
    "AeScaRegulations", // UAE Securities and Commodities Authority Regs
    "AeDifcDfsa",       // DIFC DFSA AML Module
    "AeAdgmFsra",       // ADGM FSRA AML Rulebook
    // ── Family: Status extensions (G2 wave) ──────────────────────────
    // Bare-status constructors used by the kernel-side Step-4 / Step-9
    // programs that don't fit Reg D / existing families. Most are
    // pass-through ladder rungs (Compliant / NonCompliant / Pending
    // bucket-shaping) on bespoke accessors.
    "Appointed",    // mlro_appointment_status — MLRO designated under reg.5
    "NotAppointed", // mlro_appointment_status — designation absent
    "AuditCurrent", // aml_audit_status — independent annual review current
    "Breached",     // recordkeeping_status — five-year retention failed
    "NoMatchReportingNotRequired", // fiu_report_status — no STR matter to report
    "MatchReportedToFiu", // fiu_report_status — STR filed with FIU
    "MatchPendingReport", // fiu_report_status — STR matter pending filing
    "MatchUnreported", // fiu_report_status — STR matter unfiled (breach)
    "OfacClear",    // ofac_sdn_screening_status — no SDN match
    "OfacMatch",    // ofac_sdn_screening_status — confirmed SDN hit
    "OfacPotentialMatch", // ofac_sdn_screening_status — name-similarity hit pending review
    "OfacNotApplicable", // ofac_sdn_screening_status — counterparty outside OFAC nexus
    "FreshWithin24h", // screening_freshness_status — sanctions-list cache <24h
    "ExpiredBeyond24h", // screening_freshness_status — cache expired beyond TTL
    // (`Adequate` is already declared above (line 48) in the JurisdictionAdequacy
    // family; the adequate_employees_and_premises_status / adequate_opex_status
    // accessors accept both JurisdictionAdequacy and Status.)
    "Inadequate", // adequate_employees_and_premises_status / adequate_opex_status
    "ReducedSubstanceMet", // holding_company_reduced_substance_status — pure-equity test met
    "ReducedSubstanceNotMet", // holding_company_reduced_substance_status — pure-equity test failed
    "CigaPerformedLocally", // ciga_status — CIGA in Cayman
    "CigaOutsourcedExternally", // ciga_status — CIGA outsourced offshore (breach)
    "CigaNotPerformed", // ciga_status — CIGA absent
    "TravelRuleImplemented", // travel_rule_status — VARA/FATF Rec 16 implemented
    "TravelRuleMissing", // travel_rule_status — implementation absent
    "TravelRulePartial", // travel_rule_status — partial coverage
    "TechAuditPassed", // technology_audit_status — third-party tech audit current
    "TechAuditFailed", // technology_audit_status — audit failure recorded
    "TechAuditPending", // technology_audit_status — audit underway
    "ProgramApproved", // aml_program_status — programme attested by MLRO
    "ProgramRejected", // aml_program_status — programme rejected
    "AssessmentPending", // aml_program_status — review pending
    "ClassificationFiled", // token_classification_status — VASP token-class declaration filed
    "ClassificationMissing", // token_classification_status — declaration absent
    "ClassificationDisputed", // token_classification_status — regulator-disputed classification
    // (`Segregated` already declared above in the original Status block.)
    "NotSegregated",           // segregation_status — client/firm assets co-mingled
    "AllPrincipalsClear",      // pep_screening_status — all principals OFAC/PEP clear
    "AnyPrincipalFailed",      // pep_screening_status — at least one principal failed
    "NoPepIdentified",         // pep_screening_status — no PEP among principals
    "PepIdentifiedEddCurrent", // pep_screening_status — PEP identified, EDD current
    "Current",                 // ongoing_monitoring_status — monitoring current
    "Lapsed",                  // ongoing_monitoring_status — monitoring lapsed
    "CapitalMet",              // vasp_capital_adequacy — minimum-capital test met
    "CapitalShortfall",        // vasp_capital_adequacy — shortfall recorded
    "SupervisionCurrent",      // vasp_supervision_status — VASP supervision active
    "SupervisionInProgress",   // vasp_supervision_status — supervision in progress
    "SupervisionOverdue",      // vasp_supervision_status — supervision lapsed
    "FsraAuthorized",          // fsra_authorization_status — FSRA authorisation granted (Prospera)
    "FsraSubmitted",           // fsra_authorization_status — application submitted
    "FsraRejected",            // fsra_authorization_status — application rejected
    "KycApproved",             // kyc_status — investor KYC cleared
    "KycPending",              // kyc_status — investor KYC pending
    "KycFailed",               // kyc_status — investor KYC failed
    // ── Family: VaspLicenseCategory ─────────────────────────────────
    // Cayman VASP Act 2020 license-category classifier scrutinised by
    // `vasp_license_category` accessor matches in
    // `modules/lex/cayman/vasp_act.lex`.
    "VaspLicenseCustodian",       // Custodian-only VASP license
    "VaspLicenseTradingPlatform", // Trading-platform VASP license
    "VaspRegistrationOnly",       // Registration without full license (transitional)
                                  // (Note: `Match` / `PotentialMatch` are SanctionsResult constructors,
                                  // registered above in SANCTIONS_CONSTRUCTORS, not TAG_CONSTRUCTORS —
                                  // they are scrutinised against SanctionsResult-typed accessors like
                                  // `ctx.sanctions_check` per modules/lex/cayman/sanctions_screening_loop.lex.)
];

const NAT_ACCESSORS: &[&str] = &[
    "director_count",
    "natural_person_director_count",
    "shareholder_count",
    // ── G2 closure (2026-05-07) — MISSING-PRELUDE migration ──────────
    // AIFMD Article 18 substance counts (Luxembourg AIFM CSSF
    // supervision; modules/lex/luxembourg/aifmd_aif_substance.lex).
    "aifm_local_staff_count",
    "aifm_conducting_officer_count",
    // VARA Rulebook (Dubai); count of VAS activity classes the licensee
    // is authorised to conduct under the VA Capital Markets Module.
    "vas_activity_classes",
    // FATF Recommendation 16 (Travel Rule) — per-transfer USD-equivalent
    // amount used for the USD-1000 threshold gate
    // (modules/lex/adgm/fatf_travel_rule.lex).
    "transfer_amount_usd",
    // Cayman ES Act 2024 — count of relevant-activity classes the
    // entity is in scope for (modules/lex/cayman/economic_substance_test.lex).
    "es_activity_class_count",
];

const BOOL_ACCESSORS: &[&str] = &[
    "all_identified",
    "all_parties_identified",
    "articles_permit_free_transfer",
    "board_approved_share_transfer",
    "complex_transaction_structure",
    "conducts_business_with_seychelles_residents",
    "conducts_regulated_activity",
    "digital_asset_business",
    "director_has_material_interest",
    "director_interest_disclosed",
    "directors_identified",
    // 17 C.F.R. §230.503 — proxy boolean for whether Form D has been
    // completed and filed with SEC EDGAR. Composed from
    // ctx.form_d_filing_status via the obligation daemon.
    "form_d_filed",
    "fsa_administrator_exemption",
    "fsra_authorization_required",
    "high_risk_jurisdiction_counterparty",
    "holds_client_assets",
    "incorporator_identified",
    "insider_trading_flag",
    // 17 C.F.R. §230.506(d) — "covered person" gate. True when the
    // subject is within the Rule 506(d) covered-person population
    // (issuer, directors, executive officers, 20%+ beneficial owners,
    // promoters, investment managers, compensated solicitors, and
    // 20%+ beneficial owners of compensated solicitors).
    "issuer_is_covered_person",
    "local_resident_director",
    "market_manipulation_flag",
    "minimum_subscription_met",
    // 17 C.F.R. §230.503(a)(3) — anniversary-amendment trigger. True
    // when the offering is still being sold on the anniversary of the
    // most recent previously filed Form D.
    "offering_still_active",
    "operating_in_adgm",
    "owners_identified",
    "parent_entity_kyc_compliant",
    "pep_or_associate",
    "processes_personal_data",
    "processes_sensitive_data",
    "public_company_authorized_capital_satisfied",
    "regulated_activity_exemption",
    "relevant_activity",
    "requires_local_partner",
    "sifc_facilitated_investment",
    "transfers_data_cross_border",
    // ── G2 closure (2026-05-07) — MISSING-PRELUDE migration ──────────
    // PoA evidentiary surface — composed across harbors per
    // modules/lex/aml_cdd_composition.lex and the sixteen per-jurisdiction
    // PoA programs. True iff a `ProfileDocument` of type ProofOfAddress
    // is on file, current under the per-jurisdiction freshness window,
    // and signature/verification chain is valid.
    "proof_of_address_on_file",
    // True iff any applicable harbor (residence-side OR issuer-side)
    // pulls PoA into the composed CDD requirement; computed by the
    // composition resolver (Step 1 swarm — multi-harbor wire-up).
    "requires_poa_composed",
    // True iff the distribution path (BD CIP / 506(c) safe-harbor /
    // sub-bank / RIA elected CIP) independently pulls PoA on,
    // independent of harbor-side composition.
    "path_requires_poa",
    // AIFMD Art. 18 substance — physical office in Luxembourg.
    "aifm_physical_office_in_lu",
    // Cayman ES Act s.4(5) — pure-equity-holding-company reduced-substance
    // toggle (Bool form, used in `unless` defeasibility clause).
    "holding_company_reduced_substance",
    // Cayman ES Act — applicability attestation (DITC/counsel record
    // that the entity is/isn't in scope for the substance test).
    "economic_substance_applicability_attestation",
    // Cayman AML Regulations 2020 reg.11 — SDD eligibility predicate.
    "simplified_due_diligence_eligible",
];

const SANCTIONS_ACCESSORS: &[&str] = &["adgm_statutory_sanctions_screen", "sanctions_check"];

const TAG_ACCESSORS: &[&str] = &[
    "accounting_records_retention_status",
    // 17 C.F.R. §230.506(c)(2)(ii) — Rule 506(c) reasonable-steps
    // verification of accredited-investor status.
    "accredited_investor_verification_status",
    "acra_registration_status",
    "agm_status",
    "aml_compliance_officer_status",
    "aml_record_keeping_status",
    "annual_accounts_filing_status",
    "annual_license_fee_status",
    "annual_return_filing_status",
    "approved_individuals_status",
    "approved_persons_status",
    "audit_status",
    // 17 C.F.R. §230.506(d) — covered-person disqualifying-event screen.
    "bad_actor_disqualification_status",
    "beneficial_owners",
    "beneficial_ownership_register_status",
    "breach_notification_status",
    "capital_adequacy_status",
    "cdd_status",
    "charter_registration_status",
    "cima_registration_status",
    "client_money_status",
    "cms_licence_status",
    "cnic_verification_status",
    "company_class",
    "company_secretary",
    "conduct_of_business_status",
    "confirmation_statement_filing_status",
    "confirmation_statement_status",
    "correspondent_banking_status",
    "counterparty_jurisdiction_risk",
    "cr_registration_status",
    "cross_border_transfer_status",
    "csp_license_status",
    "custodian_status",
    "customer_risk_rating",
    "data_processor_agreement_status",
    "data_protection_status",
    "data_retention_status",
    "data_subject_consent_status",
    "disclosure_completeness_status",
    "dispute_resolution_status",
    "dissolution_resolution_status",
    "dp_registration_status",
    "dpia_status",
    "economic_substance_status",
    "edd_status",
    // 17 C.F.R. §230.503 — EDGAR CIK/access-code provisioning status for
    // Form D filing; CounselFilingPath covers the manual-receipt capture
    // flow when the issuer's kernel deployment has not been credentialed.
    "edgar_credential_status",
    "employment_agreement_status",
    "employment_standards_status",
    "entity_type",
    // 17 C.F.R. §230.501–230.506 + §4(a)(2); Regulation S; Regulation CF;
    // Regulation A; fully-registered offerings. The exemption (or
    // full-registration) route the issuer is relying upon for the
    // offering.
    "exemption_relied_on",
    "fca_authorization_status",
    "fdi_screening_status",
    "financial_promotion_status",
    "fit_and_proper_status",
    "fmu_compliance_status",
    // 17 C.F.R. §230.503(a)(1) — 15-day deadline bucket produced by the
    // obligation daemon from first-sale date + calendar-day arithmetic.
    // Distinct from form_d_filing_status (issuer-side preparation
    // lifecycle) — the deadline bucket names WHEN the obligation fires.
    "form_d_deadline_status",
    // 17 C.F.R. §230.503(a) — issuer-side Form D preparation lifecycle:
    // NotDue → ReadyForCounsel → Drafted → Filed (terminal success) or
    // FiledLate (terminal post-deadline) / Superseded (amended).
    "form_d_filing_status",
    "fsra_authorization_status",
    "fsra_permission_status",
    "fsc_license_status",
    "fund_administrator_status",
    "fund_auditor_status",
    "fund_class",
    "fund_license_status",
    // 17 C.F.R. §230.506(b)(1) — Rule 506(b) prohibits general
    // solicitation and general advertising; §230.506(c) permits them.
    // NoSolicitation / PermittedSolicitation506c / ProhibitedSolicitation506b.
    "general_solicitation_status",
    "joint_venture_status",
    "kyc_aml_status",
    "listing_venue_status",
    "memorandum_filing_status",
    "minimum_capital_status",
    "name_suffix",
    "nav_frequency_status",
    "notarization_status",
    "ntn_verification_status",
    "offering_exemption_status",
    "offering_type",
    "office_country",
    "ongoing_monitoring_status",
    "pep_screening_status",
    "professional_obligation_status",
    "prospectus_filing_status",
    "psc_register_status",
    "rbe_status",
    "rcs_registration_status",
    "registered_agent",
    "registered_agent_change_notice_status",
    "registered_office_country",
    "registered_office_location",
    "regulated_activity_category",
    "repatriation_status",
    "resale_restriction_status",
    "sar_status",
    "sbp_forex_account_status",
    "secp_registration_status",
    "securities_dealer_license_status",
    "sez_status",
    "sfc_licence_status",
    "share_form",
    "sifc_approval_status",
    "sifc_sector_classification",
    "sifc_tax_holiday_status",
    "significant_controllers_register_status",
    "str_filing_status",
    "str_filing_to_crf_status",
    "systems_controls_status",
    "tax_registration_status",
    "transfer_jurisdiction_adequacy",
    "vasp_license_status",
    "wire_transfer_compliance_status",
    // ── G2 closure (2026-05-07) — MISSING-PRELUDE migration ──────────
    //
    // Per-jurisdiction AML-CDD regime tag (`AmlCddRegime` family;
    // scrutinised in modules/lex/{cayman,uk,usa,...}/aml_cdd_*.lex
    // PoA programs to identify the binding rule-set).
    "aml_cdd_jurisdiction",
    // Cayman AML 2020 Recordkeeping (reg.25 + PoCA s.136B) — five-year
    // retention compliance ladder.
    "recordkeeping_status",
    // Cayman AML 2020 Compliance Officer (reg.5) — MLRO designation.
    "mlro_appointment_status",
    // Cayman CIMA AML programme audit (CIMA Guidance Notes Ch.5).
    "aml_audit_status",
    // OFAC SDN screening — sanctions screening loop status accessor.
    "ofac_sdn_screening_status",
    // Sanctions screening cache freshness (24h TTL gate).
    "screening_freshness_status",
    // Cayman VASP Act 2020 — license-category classifier.
    "vasp_license_category",
    // VASP segregation of client/firm assets (VASP Act + custody rules).
    "segregation_status",
    // VARA prudential VA module status (modules/lex/adgm/vara_digital_assets.lex).
    "prudential_va_module_status",
    // Cayman ES Act — annual ES return filing status accessor.
    "es_filing_status",
    // Cayman ES Act — CIGA adequacy.
    "ciga_status",
    // Cayman ES Act — adequate-employees-and-premises adequacy.
    "adequate_employees_and_premises_status",
    // Cayman ES Act — adequate-OPEX adequacy.
    "adequate_opex_status",
    // Cayman ES Act — pure-equity holding-company reduced-substance test status.
    "holding_company_reduced_substance_status",
    // Cayman DITC — CRS / FATCA / CbCR enrolment + filing statuses
    // (modules/lex/cayman/tax_neutrality.lex).
    "ditc_enrolment_status",
    "crs_filing_status",
    "cbcr_filing_status",
    "self_certification_status",
    "tax_exemption_undertaking_status",
    // UK HMRC — corporation-tax / VAT filing statuses
    // (modules/lex/uk/tax_corporation_tax.lex).
    "ct_filing_status",
    "vat_registration_status",
    // Singapore IRAS — corporate-income-tax / GST filing statuses
    // (modules/lex/singapore/tax_treaties.lex).
    "cit_filing_status",
    "gst_registration_status",
    // Cayman/Cayman-VASP — STR/FIU report status accessor.
    "fiu_report_status",
    // Cayman VASP Act — supervision / capital-adequacy / tech-audit /
    // travel-rule / token-classification statuses.
    "vasp_supervision_status",
    "vasp_capital_adequacy",
    "technology_audit_status",
    "travel_rule_status",
    "token_classification_status",
    // Cayman AML 2020 — AML programme review status.
    "aml_program_status",
    // Prospera regime selector — selected ZEDE regime status accessor
    // (modules/lex/prospera/regime_selector.lex).
    "selected_regime_status",
    // Prospera reciprocity attestation (corridor-recognition surface).
    "reciprocity_attestation_status",
    // Prospera — ZEDE Council resolution receipt status
    // (modules/lex/prospera/authority_council_approval.lex).
    "council_approval_receipt_status",
    // Prospera — investor classification status (kyc_status accessor
    // separate from cross-jurisdictional kyc_aml_status).
    "kyc_status",
    // AIFMD Art. 18 — portfolio-manager and risk-manager physical
    // location accessors.
    "aifm_portfolio_manager_location",
    "aifm_risk_manager_location",
    // FATF Rec. 16 — beneficiary VASP jurisdiction (Travel Rule).
    "beneficiary_vasp_jurisdiction",
];

// ---------------------------------------------------------------------------
// Constructor families — semantic grouping of ComplianceTag constructors
// ---------------------------------------------------------------------------

/// Semantic family for a `ComplianceTag` constructor.
///
/// Each TAG_CONSTRUCTOR belongs to exactly one family. Accessors declare which
/// families they accept, enabling the type-checker to reject nonsensical
/// pattern matches (e.g. matching `audit_status` against `ADGM`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConstructorFamily {
    /// Jurisdiction codes: ADGM, SC, PK, HK, SG, GB, LU, KY, VG, HN, SA.
    Jurisdiction,
    /// Compliance / process statuses (the large cross-cutting group).
    Status,
    /// Entity type classifiers: IBC, PublicCompany, ExemptedCompany, etc.
    EntityType,
    /// Risk level classifiers: HighRisk, MediumRisk, LowRisk.
    RiskLevel,
    /// License / authorization type classifiers.
    LicenseType,
    /// Regulatory activity categories.
    RegulatoryCategory,
    /// Reporting / filing frequency: Daily, Weekly, Monthly, Quarterly.
    Frequency,
    /// Share form: Bearer, Registered.
    ShareForm,
    /// Offering type classifiers: PublicOffering, ExemptLimitedOfferees, etc.
    OfferingType,
    /// Resolution type classifiers: OrdinaryResolution, SpecialResolution75, etc.
    ResolutionType,
    /// Fund classification: ProfessionalFund, ProtectedCell.
    FundClass,
    /// Name suffix classification: Ltd, Limited, BC, SA, SARL.
    NameSuffix,
    /// Jurisdictional adequacy assessment.
    JurisdictionAdequacy,
    /// Time/deadline thresholds: Within14Days, AtLeast7Years, etc.
    TimePeriod,
    // ── USA Reg D §230.503 families (Phase 5.2 extension) ──
    /// 17 C.F.R. §§230.501–230.506 + §4(a)(2) + Reg S + Reg CF + Reg A +
    /// fully-registered offerings. Federal offering-exemption classifier for
    /// the §230.503 notice-filing obligation and its NSMIA preemption
    /// semantics. The `Registered` constructor is shared with the ShareForm
    /// family; the Reg D `exemption_relied_on` accessor accepts both.
    ExemptionCode,
    /// 17 C.F.R. §230.503(a) — issuer-side Form D preparation lifecycle:
    /// NotDue / ReadyForCounsel / Drafted (on counsel review) /
    /// Filed (terminal success — reuses Status family `Filed`) /
    /// FiledLate (terminal post-deadline) / Superseded (amended).
    FormDFilingStatus,
    /// 17 C.F.R. §230.503(a)(1) — 15-day deadline bucket produced by the
    /// obligation daemon from first-sale-date + calendar-day arithmetic:
    /// NoFirstSale (obligation not yet triggered) / Within15Days
    /// (obligation active but within grace window) / PastDeadline (breach
    /// tick fired, §230.503(a)(1) obligation breach recorded).
    FormDDeadlineStatus,
    /// 17 C.F.R. §230.506(c)(2)(ii) — Rule 506(c) reasonable-steps
    /// verification of accredited-investor status:
    /// VerificationComplete / VerificationPending / VerificationFailed /
    /// NotRequired (Rule 506(b) self-certification route).
    AccreditedVerificationStatus,
    /// 17 C.F.R. §230.506(b)(1) vs §230.506(c) — general-solicitation
    /// prohibition asymmetry:
    /// NoSolicitation / PermittedSolicitation506c / ProhibitedSolicitation506b.
    SolicitationStatus,
    /// 17 C.F.R. §230.506(d) — covered-person disqualifying-event screen:
    /// NoDisqualification / Disqualified / Waived (on SEC good-cause
    /// showing under §230.506(d)(2)(iii)). UnderReview is shared with the
    /// Status family.
    BadActorStatus,
    /// 17 C.F.R. §230.503 — SEC EDGAR CIK/access-code provisioning status
    /// for Form D filing; CounselFilingPath is the manual-receipt capture
    /// flow when the issuer's kernel deployment has not been credentialed:
    /// CredentialsProvisioned / CredentialsAbsent / CounselFilingPath.
    EdgarCredentialStatus,
    // ── G2 closure (2026-05-07) — MISSING-PRELUDE migration ──────────
    /// AML/CDD per-jurisdiction regime tag scrutinised by the
    /// `aml_cdd_jurisdiction` accessor in the Step-4 PoA programs.
    /// Each constructor names the binding rule-set:
    ///   * `KyCimaAmlr` — Cayman AML Regulations 2020 + CIMA Guidance Notes
    ///   * `BmBmaGuidance` — Bermuda BMA AML/ATF Sector-Specific Guidance
    ///   * `JeJfscHandbook` — Jersey JFSC AML/CFT Handbook
    ///   * `GgGfscHandbook` — Guernsey GFSC Handbook for FSBs
    ///   * `ImIomfsaHandbook` — Isle of Man IOMFSA AML/CFT Handbook
    ///   * `VgFscCode` — BVI FSC AML Regulations + Code of Practice
    ///   * `UkMlr2017` — UK Money Laundering Regulations 2017
    ///   * `UsCipMinimum` — USA Customer Identification Program (FinCEN minimum)
    ///   * `SgMasNotice626` / `SgVccN01` / `SgSfa04N02` — Singapore MAS Notices
    ///   * `HkAmloSch2` / `HkHkmaGuideline` / `HkSfcGuideline` — Hong Kong instruments
    ///   * `DeGwG` — Germany Geldwäschegesetz
    ///   * `EuFiveAmld` / `EuSixAmld` / `EuAmlr` — EU AMLD 5 / 6 / AMLR
    ///   * `AeCbuaeStandards` / `AeScaRegulations` / `AeDifcDfsa` / `AeAdgmFsra` — UAE instruments
    AmlCddRegime,
}

/// Look up the constructor family for a TAG_CONSTRUCTOR name.
///
/// Returns `None` for names that are not TAG_CONSTRUCTORS (including
/// constructors of other prelude types like `Compliant`, `True`, `Clear`).
pub fn constructor_family(name: &str) -> Option<ConstructorFamily> {
    use ConstructorFamily::*;
    match name {
        // ── Jurisdiction ────────────────────────────────────────────
        // Original 10-jurisdiction set + G2 additions: USDE (Delaware
        // state-level — the dgcl_corporate_governance.lex registered-
        // office gate), BM/JE/GG/IM/DE/EU/AE/BV (per-jurisdiction
        // harbor-marker codes used by the composed AML-CDD bundle).
        "ADGM" | "GB" | "HK" | "HN" | "KY" | "LU" | "PK" | "SC" | "SG" | "VG"
        | "USDE" | "BM" | "JE" | "GG" | "IM" | "DE" | "EU" | "AE" | "BV" => Some(Jurisdiction),

        // ── Entity type ─────────────────────────────────────────────
        "IBC" | "ExemptedCompany" | "PublicCompany" | "ProtectedCell" => Some(EntityType),

        // ── Risk level ──────────────────────────────────────────────
        "HighRisk" | "MediumRisk" | "LowRisk" => Some(RiskLevel),

        // ── License / authorization type ────────────────────────────
        "FcaApplied"
        | "FcaAuthorized"
        | "FullLicense"
        | "SpecialLicense"
        | "InPrincipleApproval"
        | "LicensedExchange"
        | "UnlicensedExchange"
        | "SfcType1DealingSecurities"
        | "SfcType4AdvisingSecurities"
        | "SfcType6CorporateFinance"
        | "SfcType9AssetManagement"
        | "CmsCorporateFinanceAdvice"
        | "CmsCreditRating"
        | "CmsCustodialServices"
        | "CmsDealingCapitalMarkets"
        | "CmsFundManagement"
        // G2 — Cayman VASP Act 2020 license-category constructors used
        // in modules/lex/cayman/vasp_act.lex Rule 5 (vasp_license_category
        // accessor).
        | "VaspLicenseCustodian"
        | "VaspLicenseTradingPlatform"
        | "VaspRegistrationOnly" => Some(LicenseType),

        // ── Regulatory category ─────────────────────────────────────
        "Category1" | "Category2" | "Category3A" | "Category3B" | "Category3C" | "Category4" => {
            Some(RegulatoryCategory)
        }

        // ── Frequency ───────────────────────────────────────────────
        "Daily" | "Weekly" | "Monthly" | "Quarterly" => Some(Frequency),

        // ── Share form ──────────────────────────────────────────────
        "Bearer" | "Registered" => Some(ShareForm),

        // ── Offering type ───────────────────────────────────────────
        "PublicOffering"
        | "ExemptLimitedOfferees"
        | "ExemptMinimumSubscription"
        | "ExemptProfessionalInvestor"
        | "ExemptSmallOffer"
        | "NoExemption"
        | "ProspectusFiledForResale" => Some(OfferingType),

        // ── Resolution type ─────────────────────────────────────────
        "OrdinaryResolution" | "SpecialResolution75" | "InsufficientMajority" => {
            Some(ResolutionType)
        }

        // ── Fund class ──────────────────────────────────────────────
        "ProfessionalFund" => Some(FundClass),

        // ── Name suffix ─────────────────────────────────────────────
        "Ltd" | "Limited" | "BC" | "SA" | "SARL" => Some(NameSuffix),

        // ── Jurisdiction adequacy ───────────────────────────────────
        "Adequate" | "AdequateJurisdiction" | "InadequateJurisdiction" => {
            Some(JurisdictionAdequacy)
        }

        // ── Time period thresholds ──────────────────────────────────
        "AtLeast7Years"
        | "LessThan7Years"
        | "Within14Days"
        | "Within30Days"
        | "WithinFilingDeadline"
        | "WithinRestrictionPeriod"
        | "WithinOneMonthOfAnniversary" => Some(TimePeriod),

        // ── Status (the large cross-cutting family) ─────────────────
        "Active"
        | "AgreementInPlace"
        | "AgreementPending"
        | "AllApproved"
        | "AmlCompliant"
        | "AmlFailed"
        | "AmlRemediationRequired"
        | "Applied"
        | "ApprovalPending"
        | "ArbitrationAvailable"
        | "ArbitrationNotAvailable"
        | "AgmDispensed"
        | "AgmDue"
        | "AgmHeld"
        | "AgmOverdue"
        | "AuditComplete"
        | "AuditDue"
        | "AuditExempt"
        | "AuditOverdue"
        | "AuditRequired"
        | "BelowThreshold"
        | "BreachNotified"
        | "BreachNotNotified"
        | "CapitalAdequate"
        | "CapitalInsufficient"
        | "CapitalPending"
        | "CddComplete"
        | "CddExpired"
        | "CddIncomplete"
        | "ChangeOverdue"
        | "ChangePendingWithin15Days"
        | "CharterNotRegistered"
        | "CharterPending"
        | "CharterRegistered"
        | "CnicNotVerified"
        | "CnicPending"
        | "CnicVerified"
        | "CobsCompliant"
        | "CobsUnderReview"
        | "ConfirmationStatementFiled"
        | "ConfirmationStatementOverdue"
        | "ConsentNotObtained"
        | "ConsentObtained"
        | "CorrespondentDdComplete"
        | "CorrespondentDdPending"
        | "DisclosureComplete"
        | "DisclosureIncomplete"
        | "DisclosureUnderReview"
        | "DpCompliant"
        | "DpNonCompliant"
        | "DpRemediationPending"
        | "DueSoon"
        | "EddComplete"
        | "EddIncomplete"
        | "EddRequired"
        | "EmploymentAgreementFiled"
        | "EmploymentAgreementMissing"
        | "EmploymentStandardsMet"
        | "EmploymentStandardsNotMet"
        | "Exempt"
        | "FdiApproved"
        | "FdiRejected"
        | "FdiScreeningPending"
        | "Filed"
        | "FitAndProperFailed"
        | "FitAndProperSatisfied"
        | "FitAndProperUnderReview"
        | "FmuCompliant"
        | "FmuInvestigationOpen"
        | "FmuNonCompliant"
        | "Granted"
        | "HighRiskEddComplete"
        | "HighRiskEddPending"
        | "HighRiskProhibited"
        | "ImpactAssessmentComplete"
        | "ImpactAssessmentRequired"
        | "JointVentureCompliant"
        | "JointVentureExempt"
        | "JointVentureRequired"
        | "LateNotice"
        | "MonitoringActive"
        | "MonitoringLapsed"
        | "NoTransferMechanism"
        | "NotApplicable"
        | "NotFiled"
        | "NotListed"
        | "NotRegistered"
        | "NotRestricted"
        | "NotSatisfied"
        | "NotarizedFiled"
        | "NotarizedMissing"
        | "NotarizedPending"
        | "NtnNotVerified"
        | "NtnPending"
        | "NtnVerified"
        | "OriginatorInfoComplete"
        | "OriginatorInfoMissing"
        | "Overdue"
        | "Paid"
        | "PepClear"
        | "PepIdentified"
        | "PepIdentifiedEddComplete"
        | "PepIdentifiedEddFailed"
        | "PepIdentifiedEddPending"
        | "PepNotIdentified"
        | "ProfessionalObligationMet"
        | "ProfessionalObligationNotMet"
        | "PromotionApproved"
        | "PromotionUnapproved"
        | "PscChangeOverdue"
        | "PscRegisterCurrent"
        | "PscRegisterMissing"
        | "RbeCompliant"
        | "RbeNonCompliant"
        | "RbePending"
        | "RcsNotRegistered"
        | "RcsPending"
        | "RcsRegistered"
        | "RecordsCurrent"
        | "RecordsExpired"
        | "RegisterCurrent"
        | "RegisterMissing"
        | "RepatriationApproved"
        | "RepatriationDenied"
        | "RepatriationPending"
        | "Restricted"
        | "RestrictionPeriodExpired"
        | "RetentionCompliant"
        | "RetentionNonCompliant"
        | "Revoked"
        | "Satisfied"
        | "SarFiled"
        | "SarNotFiled"
        | "SarPending"
        | "SbpForexApproved"
        | "SbpForexDenied"
        | "SbpForexPending"
        | "SecpNotRegistered"
        | "SecpPending"
        | "SecpRegistered"
        | "Segregated"
        | "SegregationPending"
        | "SezApproved"
        | "SezNotApproved"
        | "SezPending"
        | "ShellBankDetected"
        | "SifcApproved"
        | "SifcNotApproved"
        | "SifcPending"
        | "SifcSectorApproved"
        | "SifcSectorPending"
        | "SifcSectorRestricted"
        | "SifcTaxHolidayGranted"
        | "SifcTaxHolidayIneligible"
        | "SifcTaxHolidayPending"
        | "StrFiledWithFiu"
        | "StrFiledWithNca"
        | "StrNotRequired"
        | "StrPendingFiling"
        | "Suspended"
        | "TaxExempt"
        | "TaxNotRegistered"
        | "TaxRegistered"
        | "TransferMechanismInPlace"
        | "UnderReview"
        // ── G2 closure (2026-05-07) — MISSING-PRELUDE migration ──────
        // Cayman AML 2020 + CIMA Guidance Notes ladder rungs.
        | "Appointed"
        | "NotAppointed"
        | "AuditCurrent"
        | "Breached"
        // FIU/STR — Cayman PoCA + FRA reporting.
        | "NoMatchReportingNotRequired"
        | "MatchReportedToFiu"
        | "MatchPendingReport"
        | "MatchUnreported"
        // OFAC SDN screening.
        | "OfacClear"
        | "OfacMatch"
        | "OfacPotentialMatch"
        | "OfacNotApplicable"
        // Sanctions cache freshness (24h TTL gate).
        | "FreshWithin24h"
        | "ExpiredBeyond24h"
        // Cayman ES Act adequacy ladder.
        // (`Adequate` lives in JurisdictionAdequacy above; the
        // adequate_employees_and_premises_status / adequate_opex_status
        // accessors accept both JurisdictionAdequacy AND Status.)
        | "Inadequate"
        | "ReducedSubstanceMet"
        | "ReducedSubstanceNotMet"
        | "CigaPerformedLocally"
        | "CigaOutsourcedExternally"
        | "CigaNotPerformed"
        // VASP technology / supervision / capital / travel-rule ladders.
        | "TravelRuleImplemented"
        | "TravelRuleMissing"
        | "TravelRulePartial"
        | "TechAuditPassed"
        | "TechAuditFailed"
        | "TechAuditPending"
        | "ProgramApproved"
        | "ProgramRejected"
        | "AssessmentPending"
        | "ClassificationFiled"
        | "ClassificationMissing"
        | "ClassificationDisputed"
        | "NotSegregated"
        // PEP / monitoring extensions.
        | "AllPrincipalsClear"
        | "AnyPrincipalFailed"
        | "NoPepIdentified"
        | "PepIdentifiedEddCurrent"
        | "Current"
        | "Lapsed"
        // VASP capital + supervision.
        | "CapitalMet"
        | "CapitalShortfall"
        | "SupervisionCurrent"
        | "SupervisionInProgress"
        | "SupervisionOverdue"
        // Prospera FSRA application + KYC ladder rungs.
        | "FsraAuthorized"
        | "FsraSubmitted"
        | "FsraRejected"
        | "KycApproved"
        | "KycPending"
        | "KycFailed" => Some(Status),

        // ── USA Reg D §230.503 — ExemptionCode family ───────────────
        // (17 C.F.R. §§230.501–230.506, §4(a)(2), Reg S, Reg CF, Reg A.
        //  `Registered` is shared with the ShareForm family and stays
        //  ShareForm above — the exemption_relied_on accessor accepts
        //  both ExemptionCode and ShareForm to cover that overlap.)
        "RegA" | "RegCF" | "RegS" | "Rule504" | "Rule506b" | "Rule506c" | "Section4a2" => {
            Some(ExemptionCode)
        }

        // ── USA Reg D §230.503(a) — FormDFilingStatus family ─────────
        // (Issuer-side preparation lifecycle. `Filed` stays in Status —
        //  form_d_filing_status accessor accepts both families.)
        "Drafted" | "FiledLate" | "NotDue" | "ReadyForCounsel" | "Superseded" => {
            Some(FormDFilingStatus)
        }

        // ── USA Reg D §230.503(a)(1) — FormDDeadlineStatus family ────
        "NoFirstSale" | "PastDeadline" | "Within15Days" => Some(FormDDeadlineStatus),

        // ── USA Reg D §230.506(c)(2)(ii) — AccreditedVerificationStatus ──
        "NotRequired" | "VerificationComplete" | "VerificationFailed" | "VerificationPending" => {
            Some(AccreditedVerificationStatus)
        }

        // ── USA Reg D §230.506(b)(1) / §230.506(c) — SolicitationStatus ──
        "NoSolicitation" | "PermittedSolicitation506c" | "ProhibitedSolicitation506b" => {
            Some(SolicitationStatus)
        }

        // ── USA Reg D §230.506(d) — BadActorStatus family ────────────
        // (`UnderReview` stays in Status — bad_actor_disqualification_status
        //  accessor accepts both families.)
        "Disqualified" | "NoDisqualification" | "Waived" => Some(BadActorStatus),

        // ── USA Reg D §230.503 — EdgarCredentialStatus family ────────
        "CounselFilingPath" | "CredentialsAbsent" | "CredentialsProvisioned" => {
            Some(EdgarCredentialStatus)
        }

        // ── G2 closure (2026-05-07) — AmlCddRegime family ───────────
        // Per-jurisdiction AML/CDD regulation tags scrutinised by
        // `aml_cdd_jurisdiction` accessor matches.
        "KyCimaAmlr"
        | "BmBmaGuidance"
        | "JeJfscHandbook"
        | "GgGfscHandbook"
        | "ImIomfsaHandbook"
        | "VgFscCode"
        | "UkMlr2017"
        | "UsCipMinimum"
        | "SgMasNotice626"
        | "SgVccN01"
        | "SgSfa04N02"
        | "HkAmloSch2"
        | "HkHkmaGuideline"
        | "HkSfcGuideline"
        | "DeGwG"
        | "EuFiveAmld"
        | "EuSixAmld"
        | "EuAmlr"
        | "AeCbuaeStandards"
        | "AeScaRegulations"
        | "AeDifcDfsa"
        | "AeAdgmFsra" => Some(AmlCddRegime),

        _ => None,
    }
}

/// Look up the set of constructor families valid for a TAG_ACCESSOR.
///
/// Returns `None` for names that are not TAG_ACCESSORS. Returns `Some(&[..])`
/// with the families whose constructors are semantically valid as match
/// patterns for this accessor.
pub fn accessor_families(accessor: &str) -> Option<&'static [ConstructorFamily]> {
    use ConstructorFamily::*;
    match accessor {
        // ── Jurisdiction-typed accessors ─────────────────────────────
        "office_country" | "registered_office_country" | "registered_office_location" => {
            Some(&[Jurisdiction])
        }

        // ── Entity type ─────────────────────────────────────────────
        "entity_type" | "company_class" => Some(&[EntityType]),

        // ── Risk level ──────────────────────────────────────────────
        "customer_risk_rating" | "counterparty_jurisdiction_risk" => Some(&[RiskLevel]),

        // ── License / authorization status ──────────────────────────
        "fca_authorization_status"
        | "fsra_authorization_status"
        | "fsra_permission_status"
        | "fsc_license_status"
        | "csp_license_status"
        | "fund_license_status"
        | "vasp_license_status"
        | "securities_dealer_license_status"
        | "sfc_licence_status"
        | "cms_licence_status"
        | "cima_registration_status"
        | "listing_venue_status" => Some(&[LicenseType, Status]),

        // ── Regulatory category ─────────────────────────────────────
        "regulated_activity_category" => Some(&[RegulatoryCategory]),

        // ── Frequency ───────────────────────────────────────────────
        "nav_frequency_status" => Some(&[Frequency]),

        // ── Share form ──────────────────────────────────────────────
        "share_form" => Some(&[ShareForm]),

        // ── Offering type / exemption ───────────────────────────────
        "offering_type" | "offering_exemption_status" => Some(&[OfferingType, Status]),

        // ── Resolution type ─────────────────────────────────────────
        "dissolution_resolution_status" => Some(&[ResolutionType, Status]),

        // ── Fund class ──────────────────────────────────────────────
        "fund_class" => Some(&[FundClass]),

        // ── Name suffix ─────────────────────────────────────────────
        "name_suffix" => Some(&[NameSuffix]),

        // ── Jurisdiction adequacy ───────────────────────────────────
        "transfer_jurisdiction_adequacy" => Some(&[JurisdictionAdequacy]),

        // ── Retention / records (status + time period) ──────────────
        "accounting_records_retention_status"
        | "aml_record_keeping_status"
        | "data_retention_status" => Some(&[Status, TimePeriod]),

        // ── Registration status accessors (status only) ─────────────
        "acra_registration_status"
        | "cr_registration_status"
        | "dp_registration_status"
        | "rcs_registration_status"
        | "secp_registration_status"
        | "tax_registration_status" => Some(&[Status]),

        // ── Pure status accessors (the large group) ─────────────────
        "agm_status"
        | "aml_compliance_officer_status"
        | "annual_accounts_filing_status"
        | "annual_license_fee_status"
        | "annual_return_filing_status"
        | "approved_individuals_status"
        | "approved_persons_status"
        | "audit_status"
        | "beneficial_owners"
        | "beneficial_ownership_register_status"
        | "breach_notification_status"
        | "capital_adequacy_status"
        | "cdd_status"
        | "charter_registration_status"
        | "client_money_status"
        | "cnic_verification_status"
        | "company_secretary"
        | "conduct_of_business_status"
        | "confirmation_statement_filing_status"
        | "confirmation_statement_status"
        | "correspondent_banking_status"
        | "cross_border_transfer_status"
        | "custodian_status"
        | "data_processor_agreement_status"
        | "data_protection_status"
        | "data_subject_consent_status"
        | "disclosure_completeness_status"
        | "dispute_resolution_status"
        | "dpia_status"
        | "economic_substance_status"
        | "edd_status"
        | "employment_agreement_status"
        | "employment_standards_status"
        | "fdi_screening_status"
        | "financial_promotion_status"
        | "fit_and_proper_status"
        | "fmu_compliance_status"
        | "fund_administrator_status"
        | "fund_auditor_status"
        | "joint_venture_status"
        | "kyc_aml_status"
        | "memorandum_filing_status"
        | "minimum_capital_status"
        | "notarization_status"
        | "ntn_verification_status"
        | "ongoing_monitoring_status"
        | "pep_screening_status"
        | "professional_obligation_status"
        | "prospectus_filing_status"
        | "psc_register_status"
        | "rbe_status"
        | "registered_agent"
        | "registered_agent_change_notice_status"
        | "repatriation_status"
        | "resale_restriction_status"
        | "sar_status"
        | "sbp_forex_account_status"
        | "sez_status"
        | "sifc_approval_status"
        | "sifc_sector_classification"
        | "sifc_tax_holiday_status"
        | "significant_controllers_register_status"
        | "str_filing_status"
        | "str_filing_to_crf_status"
        | "systems_controls_status"
        | "wire_transfer_compliance_status" => Some(&[Status]),

        // ── USA Reg D §230.503 accessors (Phase 5.2 extension) ───────
        // Each accessor's family set covers its natural constructor
        // family PLUS any sibling family whose constructors are also
        // matched in the Reg D rule corpus. `exemption_relied_on`
        // accepts both ExemptionCode and ShareForm because the
        // fully-registered-offering arm uses the pre-existing ShareForm
        // `Registered` constructor. `form_d_filing_status` and
        // `bad_actor_disqualification_status` both extend into Status
        // because `Filed` and `UnderReview` already live there.
        "exemption_relied_on" => Some(&[ExemptionCode, ShareForm]),
        "form_d_filing_status" => Some(&[FormDFilingStatus, Status]),
        "form_d_deadline_status" => Some(&[FormDDeadlineStatus]),
        "accredited_investor_verification_status" => Some(&[AccreditedVerificationStatus]),
        "general_solicitation_status" => Some(&[SolicitationStatus]),
        "bad_actor_disqualification_status" => Some(&[BadActorStatus, Status]),
        "edgar_credential_status" => Some(&[EdgarCredentialStatus]),

        // ── G2 closure (2026-05-07) — accessor families ──────────────
        //
        // Per-jurisdiction AML/CDD regime tag accessor (Step-4 PoA programs).
        "aml_cdd_jurisdiction" => Some(&[AmlCddRegime]),
        // Cayman AML 2020 + Cayman AML programme review status accessors.
        "recordkeeping_status"
        | "mlro_appointment_status"
        | "aml_audit_status"
        | "aml_program_status"
        | "screening_freshness_status"
        | "ofac_sdn_screening_status"
        | "fiu_report_status"
        | "es_filing_status"
        | "ciga_status"
        // Cayman DITC (CRS / FATCA / CbCR) — pure-status ladders.
        | "ditc_enrolment_status"
        | "crs_filing_status"
        | "cbcr_filing_status"
        | "self_certification_status"
        | "tax_exemption_undertaking_status"
        // UK HMRC — corporation-tax / VAT.
        | "ct_filing_status"
        | "vat_registration_status"
        // Singapore IRAS — corporate-income-tax / GST.
        | "cit_filing_status"
        | "gst_registration_status"
        // Cayman holding-company reduced-substance test (Status only).
        | "holding_company_reduced_substance_status"
        // VARA prudential VA module (modules/lex/adgm/vara_digital_assets.lex).
        | "prudential_va_module_status"
        // Cayman VASP supervision / capital / tech-audit / travel-rule /
        // token-classification / AML-program ladders.
        | "vasp_supervision_status"
        | "vasp_capital_adequacy"
        | "technology_audit_status"
        | "travel_rule_status"
        | "token_classification_status"
        // Cayman VASP segregation status (Status family).
        | "segregation_status"
        // Prospera regime selector / reciprocity / Council resolution receipt.
        | "selected_regime_status"
        | "reciprocity_attestation_status"
        | "council_approval_receipt_status"
        // Prospera investor classification — distinct from kyc_aml_status.
        | "kyc_status" => Some(&[Status]),

        // Cayman ES adequacy accessors accept both JurisdictionAdequacy
        // and Status families (Adequate/Inadequate constructors live in
        // JurisdictionAdequacy; the bespoke adequacy ladders extend Status).
        "adequate_employees_and_premises_status" | "adequate_opex_status" => {
            Some(&[JurisdictionAdequacy, Status])
        }

        // Cayman VASP Act 2020 — license-category accessor accepts both
        // LicenseType (the new VaspLicense* constructors) and Status
        // (existing licensing-status ladder rungs).
        "vasp_license_category" => Some(&[LicenseType, Status]),

        // Jurisdiction-typed accessors added in G2:
        // AIFMD Art. 18 substance — manager physical-location accessors.
        "aifm_portfolio_manager_location" | "aifm_risk_manager_location" => {
            Some(&[Jurisdiction])
        }
        // FATF Rec. 16 — beneficiary VASP jurisdiction (Travel Rule).
        "beneficiary_vasp_jurisdiction" => Some(&[Jurisdiction]),

        _ => None,
    }
}

/// Validate that a constructor belongs to a family compatible with the given
/// accessor.
///
/// Returns `true` if the constructor is from a family that the accessor
/// accepts, or if either the accessor or constructor is unknown (conservative
/// — unknown names are not rejected). Returns `false` only when both are
/// known and the constructor's family is not in the accessor's family set.
///
/// This function operates on the semantic layer above the type system: both
/// the accessor and constructor are typed as `ComplianceTag` in the prelude,
/// but the family check catches nonsensical combinations that the flat type
/// would miss.
pub fn validate_match_family(accessor: &str, constructor: &str) -> bool {
    let families = match accessor_families(accessor) {
        Some(f) => f,
        None => return true, // unknown accessor — conservative accept
    };
    let family = match constructor_family(constructor) {
        Some(f) => f,
        None => return true, // unknown constructor — conservative accept
    };
    families.contains(&family)
}

#[cfg(test)]
const RULE_REFERENCED_CONSTANTS: &[&str] = &[
    "ComplianceVerdict",
    "Compliant",
    "Cons",
    "Date",
    "IncorporationContext",
    "NonCompliant",
    "Pending",
    "SanctionsResult",
    "US_SEC_Counsel",
    "accounting_records_retention_status",
    "accredited_investor_verification_status",
    "acra_registration_status",
    "adgm_statutory_sanctions_screen",
    "agm_status",
    "all_identified",
    "all_parties_identified",
    "aml_compliance_officer_status",
    "aml_record_keeping_status",
    "annual_accounts_filing_status",
    "annual_license_fee_status",
    "annual_return_filing_status",
    "approved_individuals_status",
    "approved_persons_status",
    "articles_permit_free_transfer",
    "audit_status",
    "bad_actor_disqualification_status",
    "beneficial_owners",
    "beneficial_ownership_register_status",
    "board_approved_share_transfer",
    "breach_notification_status",
    "capital_adequacy_status",
    "cdd_status",
    "charter_registration_status",
    "cima_registration_status",
    "client_money_status",
    "cms_licence_status",
    "cnic_verification_status",
    "company_class",
    "company_secretary",
    "complex_transaction_structure",
    "conduct_of_business_status",
    "conducts_business_with_seychelles_residents",
    "conducts_regulated_activity",
    "confirmation_statement_filing_status",
    "confirmation_statement_status",
    "correspondent_banking_status",
    "counterparty_jurisdiction_risk",
    "cr_registration_status",
    "cross_border_transfer_status",
    "csp_license_status",
    "custodian_status",
    "customer_risk_rating",
    "data_processor_agreement_status",
    "data_protection_status",
    "data_retention_status",
    "data_subject_consent_status",
    "digital_asset_business",
    "director_count",
    "director_has_material_interest",
    "director_interest_disclosed",
    "directors_identified",
    "disclosure_completeness_status",
    "dispute_resolution_status",
    "dissolution_resolution_status",
    "dp_registration_status",
    "dpia_status",
    "economic_substance_status",
    "edd_status",
    "edgar_credential_status",
    "employment_agreement_status",
    "employment_standards_status",
    "entity_type",
    "exemption_relied_on",
    "fca_authorization_status",
    "fdi_screening_status",
    "financial_promotion_status",
    "fit_and_proper_status",
    "fmu_compliance_status",
    "form_d_deadline_status",
    "form_d_filed",
    "form_d_filing_status",
    "fsa_administrator_exemption",
    "fsra_authorization_required",
    "fsra_authorization_status",
    "fsra_permission_status",
    "fsc_license_status",
    "fund_administrator_status",
    "fund_auditor_status",
    "fund_class",
    "fund_license_status",
    "general_solicitation_status",
    "high_risk_jurisdiction_counterparty",
    "holds_client_assets",
    "incorporator_identified",
    "insider_trading_flag",
    "issuer_is_covered_person",
    "joint_venture_status",
    "kyc_aml_status",
    "listing_venue_status",
    "local_resident_director",
    "market_manipulation_flag",
    "memorandum_filing_status",
    "minimum_capital_status",
    "minimum_subscription_met",
    "name_suffix",
    "natural_person_director_count",
    "nav_frequency_status",
    "notarization_status",
    "ntn_verification_status",
    "offering_exemption_status",
    "offering_still_active",
    "offering_type",
    "office_country",
    "ongoing_monitoring_status",
    "operating_in_adgm",
    "owners_identified",
    "parent_entity_kyc_compliant",
    "pep_or_associate",
    "pep_screening_status",
    "processes_personal_data",
    "processes_sensitive_data",
    "professional_obligation_status",
    "prospectus_filing_status",
    "psc_register_status",
    "public_company_authorized_capital_satisfied",
    "rbe_status",
    "rcs_registration_status",
    "registered_agent",
    "registered_agent_change_notice_status",
    "registered_office_country",
    "registered_office_location",
    "regulated_activity_category",
    "regulated_activity_exemption",
    "relevant_activity",
    "repatriation_status",
    "requires_local_partner",
    "resale_restriction_status",
    "sanctions_check",
    "sar_status",
    "sbp_forex_account_status",
    "secp_registration_status",
    "securities_dealer_license_status",
    "sez_status",
    "sfc_licence_status",
    "share_form",
    "shareholder_count",
    "sifc_approval_status",
    "sifc_facilitated_investment",
    "sifc_sector_classification",
    "sifc_tax_holiday_status",
    "significant_controllers_register_status",
    "str_filing_status",
    "str_filing_to_crf_status",
    "systems_controls_status",
    "tax_registration_status",
    "transfer_jurisdiction_adequacy",
    "transfers_data_cross_border",
    "vasp_license_status",
    "wire_transfer_compliance_status",
];

#[cfg(test)]
const RULE_REFERENCED_CONSTRUCTORS: &[&str] = &[
    "ADGM",
    "Active",
    "Adequate",
    "AdequateJurisdiction",
    "AgmDispensed",
    "AgmDue",
    "AgmHeld",
    "AgmOverdue",
    "AgreementInPlace",
    "AgreementPending",
    "AllApproved",
    "AmlCompliant",
    "AmlFailed",
    "AmlRemediationRequired",
    "Applied",
    "ApprovalPending",
    "ArbitrationAvailable",
    "ArbitrationNotAvailable",
    "AtLeast7Years",
    "AuditComplete",
    "AuditDue",
    "AuditExempt",
    "AuditOverdue",
    "AuditRequired",
    "BC",
    "Bearer",
    "BelowThreshold",
    "BreachNotified",
    "BreachNotNotified",
    "CapitalAdequate",
    "CapitalInsufficient",
    "CapitalPending",
    "Category1",
    "Category2",
    "Category3A",
    "Category3B",
    "Category3C",
    "Category4",
    "CddComplete",
    "CddExpired",
    "CddIncomplete",
    "ChangeOverdue",
    "ChangePendingWithin15Days",
    "CharterNotRegistered",
    "CharterPending",
    "CharterRegistered",
    "Clear",
    "CmsCorporateFinanceAdvice",
    "CmsCreditRating",
    "CmsCustodialServices",
    "CmsDealingCapitalMarkets",
    "CmsFundManagement",
    "CnicNotVerified",
    "CnicPending",
    "CnicVerified",
    "CobsCompliant",
    "CobsUnderReview",
    "ConfirmationStatementFiled",
    "ConfirmationStatementOverdue",
    "ConsentNotObtained",
    "ConsentObtained",
    "CorrespondentDdComplete",
    "CorrespondentDdPending",
    "Daily",
    "DisclosureComplete",
    "DisclosureIncomplete",
    "DisclosureUnderReview",
    "DpCompliant",
    "DpNonCompliant",
    "DpRemediationPending",
    "DueSoon",
    "EddComplete",
    "EddIncomplete",
    "EddRequired",
    "EmploymentAgreementFiled",
    "EmploymentAgreementMissing",
    "EmploymentStandardsMet",
    "EmploymentStandardsNotMet",
    "Exempt",
    "ExemptLimitedOfferees",
    "ExemptMinimumSubscription",
    "ExemptProfessionalInvestor",
    "ExemptSmallOffer",
    "ExemptedCompany",
    "False",
    "FcaApplied",
    "FcaAuthorized",
    "FdiApproved",
    "FdiRejected",
    "FdiScreeningPending",
    "Filed",
    "FitAndProperFailed",
    "FitAndProperSatisfied",
    "FitAndProperUnderReview",
    "FmuCompliant",
    "FmuInvestigationOpen",
    "FmuNonCompliant",
    "FullLicense",
    "GB",
    "Granted",
    "HK",
    "HN",
    "HighRisk",
    "HighRiskEddComplete",
    "HighRiskEddPending",
    "HighRiskProhibited",
    "IBC",
    "ImpactAssessmentComplete",
    "ImpactAssessmentRequired",
    "InadequateJurisdiction",
    "InPrincipleApproval",
    "InsufficientMajority",
    "JointVentureCompliant",
    "JointVentureExempt",
    "JointVentureRequired",
    "KY",
    "LU",
    "LateNotice",
    "LessThan7Years",
    "LicensedExchange",
    "Limited",
    "LowRisk",
    "Ltd",
    "MediumRisk",
    "MonitoringActive",
    "MonitoringLapsed",
    "Monthly",
    "Nil",
    "NoExemption",
    "NoTransferMechanism",
    "None",
    "NotApplicable",
    "NotFiled",
    "NotListed",
    "NotRegistered",
    "NotRestricted",
    "NotSatisfied",
    "NotarizedFiled",
    "NotarizedMissing",
    "NotarizedPending",
    "NtnNotVerified",
    "NtnPending",
    "NtnVerified",
    "OrdinaryResolution",
    "OriginatorInfoComplete",
    "OriginatorInfoMissing",
    "Overdue",
    "Paid",
    "PK",
    "PepClear",
    "PepIdentified",
    "PepIdentifiedEddComplete",
    "PepIdentifiedEddFailed",
    "PepIdentifiedEddPending",
    "PepNotIdentified",
    "ProfessionalFund",
    "ProfessionalObligationMet",
    "ProfessionalObligationNotMet",
    "PromotionApproved",
    "PromotionUnapproved",
    "ProspectusFiledForResale",
    "ProtectedCell",
    "PscChangeOverdue",
    "PscRegisterCurrent",
    "PscRegisterMissing",
    "PublicCompany",
    "PublicOffering",
    "Quarterly",
    "RbeCompliant",
    "RbeNonCompliant",
    "RbePending",
    "RcsNotRegistered",
    "RcsPending",
    "RcsRegistered",
    "RecordsCurrent",
    "RecordsExpired",
    "RegisterCurrent",
    "RegisterMissing",
    "Registered",
    "RepatriationApproved",
    "RepatriationDenied",
    "RepatriationPending",
    "Restricted",
    "RestrictionPeriodExpired",
    "RetentionCompliant",
    "RetentionNonCompliant",
    "Revoked",
    "SA",
    "SARL",
    "SC",
    "SG",
    "SarFiled",
    "SarNotFiled",
    "SarPending",
    "Satisfied",
    "SbpForexApproved",
    "SbpForexDenied",
    "SbpForexPending",
    "SecpNotRegistered",
    "SecpPending",
    "SecpRegistered",
    "Segregated",
    "SegregationPending",
    "SezApproved",
    "SezNotApproved",
    "SezPending",
    "SfcType1DealingSecurities",
    "SfcType4AdvisingSecurities",
    "SfcType6CorporateFinance",
    "SfcType9AssetManagement",
    "ShellBankDetected",
    "SifcApproved",
    "SifcNotApproved",
    "SifcPending",
    "Some",
    "SpecialLicense",
    "SpecialResolution75",
    "StrFiledWithFiu",
    "StrFiledWithNca",
    "StrNotRequired",
    "StrPendingFiling",
    "Suspended",
    "TaxExempt",
    "TaxNotRegistered",
    "TaxRegistered",
    "TransferMechanismInPlace",
    "True",
    "UnderReview",
    "UnlicensedExchange",
    "VG",
    "Weekly",
    "Within14Days",
    "Within30Days",
    "WithinFilingDeadline",
    "WithinRestrictionPeriod",
    "WithinOneMonthOfAnniversary",
    "Zero",
    // ── USA Reg D §230.503 constructors (Phase 5.2 extension) ──────
    // Family-grouped block. Existing `Registered`, `Filed`, and
    // `UnderReview` are re-used from the ShareForm / Status families
    // above and not re-declared here.
    // ExemptionCode family:
    "RegA",
    "RegCF",
    "RegS",
    "Rule504",
    "Rule506b",
    "Rule506c",
    "Section4a2",
    // FormDFilingStatus family:
    "Drafted",
    "FiledLate",
    "NotDue",
    "ReadyForCounsel",
    "Superseded",
    // FormDDeadlineStatus family:
    "NoFirstSale",
    "PastDeadline",
    "Within15Days",
    // AccreditedVerificationStatus family:
    "NotRequired",
    "VerificationComplete",
    "VerificationFailed",
    "VerificationPending",
    // SolicitationStatus family:
    "NoSolicitation",
    "PermittedSolicitation506c",
    "ProhibitedSolicitation506b",
    // BadActorStatus family:
    "Disqualified",
    "NoDisqualification",
    "Waived",
    // EdgarCredentialStatus family:
    "CounselFilingPath",
    "CredentialsAbsent",
    "CredentialsProvisioned",
];

fn type0() -> Term {
    Term::type_sort(0)
}

fn constant(name: &str) -> Term {
    Term::constant(name)
}

fn arrow(domain: Term, codomain: Term) -> Term {
    Term::pi("_", domain, codomain)
}

fn register_all(ctx: Context, names: &[&str], ty: &Term) -> Context {
    names
        .iter()
        .fold(ctx, |acc, name| acc.with_named_constant(name, ty.clone()))
}

fn register_unary_accessors(ctx: Context, names: &[&str], codomain: &str) -> Context {
    let ty = arrow(constant("IncorporationContext"), constant(codomain));
    register_all(ctx, names, &ty)
}

/// Returns `true` if `name` is a constructor registered in the compliance
/// prelude (i.e., a constructor belonging to one of the prelude inductive
/// types: `ComplianceVerdict`, `Bool`, `Nat`, `SanctionsResult`,
/// `ComplianceTag`).
///
/// This is used by the admissibility checker to allow `Match` expressions
/// that pattern-match on prelude types without requiring full inductive
/// type metadata.
pub fn is_prelude_constructor(name: &str) -> bool {
    VERDICT_CONSTRUCTORS.contains(&name)
        || BOOL_CONSTRUCTORS.contains(&name)
        || is_nat_constructor(name)
        || SANCTIONS_CONSTRUCTORS.contains(&name)
        || TAG_CONSTRUCTORS.contains(&name)
}

/// Returns `true` if `name` is one of the core prelude types
/// (`ComplianceVerdict`, `ComplianceTag`, `Bool`, `Nat`, `SanctionsResult`,
/// `IncorporationContext`).
pub fn is_prelude_type(name: &str) -> bool {
    CORE_TYPES.contains(&name)
}

/// Runtime registry of finite prelude datatypes used by the admissibility
/// checker for lightweight match validation.
pub struct PreludeRegistry;

impl PreludeRegistry {
    /// Return the full constructor list for a named prelude datatype, or
    /// `None` if `datatype_name` is not a known prelude type.
    ///
    /// For `ComplianceTag` the list includes the
    /// [`TAG_OVERLOADED_CONSTRUCTORS`] (e.g. `Pending`) that are admissible
    /// tag values in addition to the constructors registered with the tag
    /// type. This is the constructor universe used for match-branch
    /// membership and exhaustiveness checks; `ComplianceTag` is open, so
    /// every concrete `ComplianceTag` match carries a wildcard and is never
    /// driven to positive exhaustiveness over this list.
    pub fn lookup_variant_constructors(datatype_name: &str) -> Option<Vec<&'static str>> {
        match datatype_name {
            "ComplianceVerdict" => Some(VERDICT_CONSTRUCTORS.to_vec()),
            "Bool" => Some(BOOL_CONSTRUCTORS.to_vec()),
            "Nat" => Some(NAT_CONSTRUCTORS.to_vec()),
            "SanctionsResult" => Some(SANCTIONS_CONSTRUCTORS.to_vec()),
            "ComplianceTag" => Some(
                TAG_CONSTRUCTORS
                    .iter()
                    .copied()
                    .chain(TAG_OVERLOADED_CONSTRUCTORS.iter().copied())
                    .collect(),
            ),
            _ => None,
        }
    }

    /// Return the *primary* datatype a prelude constructor is registered and
    /// typed under.
    ///
    /// A constructor has exactly one primary datatype (the one whose
    /// `register_*` call gives the constant its type). Overloaded tag members
    /// such as `Pending` report their primary datatype here
    /// (`ComplianceVerdict`); their secondary `ComplianceTag` membership is
    /// surfaced only through [`Self::constructor_datatypes`] and
    /// [`Self::lookup_variant_constructors`]. Use this when a single, stable
    /// datatype answer is required (e.g. error-message attribution); use
    /// [`Self::constructor_datatypes`] for match-resolution membership.
    pub fn constructor_datatype(ctor_name: &str) -> Option<&'static str> {
        if VERDICT_CONSTRUCTORS.contains(&ctor_name) {
            Some("ComplianceVerdict")
        } else if BOOL_CONSTRUCTORS.contains(&ctor_name) {
            Some("Bool")
        } else if is_nat_constructor(ctor_name) {
            Some("Nat")
        } else if SANCTIONS_CONSTRUCTORS.contains(&ctor_name) {
            Some("SanctionsResult")
        } else if TAG_CONSTRUCTORS.contains(&ctor_name) {
            Some("ComplianceTag")
        } else {
            None
        }
    }

    /// Return *every* prelude datatype a constructor is an admissible member
    /// of (its primary registration plus any overload membership).
    ///
    /// This is the membership relation used to resolve the datatype of a
    /// `match` from its branch constructors: a constructor that is overloaded
    /// (e.g. `Pending`, a member of both `ComplianceVerdict` and
    /// `ComplianceTag`) reports both, so a match whose remaining arms pin a
    /// single shared datatype resolves to that datatype rather than failing
    /// as "unresolved" on a spurious cross-datatype clash. The returned
    /// `Vec` is empty for an unknown constructor.
    pub fn constructor_datatypes(ctor_name: &str) -> Vec<&'static str> {
        let mut dts = Vec::new();
        if VERDICT_CONSTRUCTORS.contains(&ctor_name) {
            dts.push("ComplianceVerdict");
        }
        if BOOL_CONSTRUCTORS.contains(&ctor_name) {
            dts.push("Bool");
        }
        if is_nat_constructor(ctor_name) {
            dts.push("Nat");
        }
        if SANCTIONS_CONSTRUCTORS.contains(&ctor_name) {
            dts.push("SanctionsResult");
        }
        if TAG_CONSTRUCTORS.contains(&ctor_name) || TAG_OVERLOADED_CONSTRUCTORS.contains(&ctor_name)
        {
            dts.push("ComplianceTag");
        }
        dts
    }
}

/// Build the structural prelude as a typechecker context with only the
/// substrate-level types and constructors needed by the Lex checker.
pub fn structural_prelude() -> Context {
    let mut ctx = Context::empty();
    let type0_term = type0();

    ctx = register_all(ctx, CORE_TYPES, &type0_term);
    ctx = register_all(ctx, VERDICT_CONSTRUCTORS, &constant("ComplianceVerdict"));
    ctx = register_all(ctx, BOOL_CONSTRUCTORS, &constant("Bool"));
    ctx = register_all(ctx, NAT_CONSTRUCTORS, &constant("Nat"));
    ctx = register_all(ctx, SANCTIONS_CONSTRUCTORS, &constant("SanctionsResult"));

    ctx = ctx.with_named_constant(
        "Some",
        arrow(constant("IncorporationContext"), constant("ComplianceTag")),
    );
    ctx = ctx.with_named_constant("None", constant("ComplianceTag"));
    ctx = ctx.with_named_constant("Nil", constant("ComplianceTag"));
    ctx = ctx.with_named_constant(
        "Cons",
        arrow(
            constant("IncorporationContext"),
            arrow(constant("ComplianceTag"), constant("ComplianceTag")),
        ),
    );

    ctx
}

/// Build the legacy fixture prelude with the historical rule-corpus symbol
/// surface. This intentionally includes jurisdiction, regulator, and
/// compliance-domain names until callers migrate to pack-local signatures.
pub fn legacy_fixture_prelude() -> Context {
    let mut ctx = structural_prelude();

    ctx = register_all(ctx, TAG_CONSTRUCTORS, &constant("ComplianceTag"));
    ctx = register_unary_accessors(ctx, NAT_ACCESSORS, "Nat");
    ctx = register_unary_accessors(ctx, BOOL_ACCESSORS, "Bool");
    ctx = register_unary_accessors(ctx, SANCTIONS_ACCESSORS, "SanctionsResult");
    ctx = register_unary_accessors(ctx, TAG_ACCESSORS, "ComplianceTag");

    // 17 C.F.R. §230.503(a)(1) + practitioner consensus on SAFE first-sale
    // date (Rule 9 of usa/regulation_d_503.lex). US_SEC_Counsel is
    // registered as a resolvable name so the typed discretion hole
    //   ? first_sale_date_for_safe : Date @ US_SEC_Counsel
    // can look it up during elaboration. A richer federal regulator
    // authority graph (acceptance / recognition semantics) is a
    // follow-up; here US_SEC_Counsel is typed as ComplianceTag so the
    // name resolves without forcing an AuthorityRef / authority-graph
    // extension in this wave.
    ctx = ctx.with_named_constant("US_SEC_Counsel", constant("ComplianceTag"));

    // ── G2 closure (2026-05-07) — authority refs and typed-discretion
    // hole markers ──────────────────────────────────────────────────
    //
    // Each MISSING-PRELUDE marker in
    // ~/kernel/modules/lex/{cayman,prospera,uk,singapore,usa/states/...}/*.lex
    // for an authority-named typed discretion hole resolves through
    // these names. Per the US_SEC_Counsel pattern, each is typed at
    // ComplianceTag for elaboration-time name resolution. A richer
    // AuthorityRef / regulator-graph extension that distinguishes
    // recognition-grade and acceptance semantics is a follow-up
    // frontier (tracked in the G2 punch list at
    // ~/kernel/docs/architecture/frontier-work/G2-MISSING-PRELUDE-CLOSURE.md).
    for authority_ref in [
        // Cayman: Department for International Tax Cooperation (DITC).
        "DITC",
        // Cayman: Cayman Islands Monetary Authority.
        "KY_CIMA",
        // BVI Financial Services Commission.
        "VG_FSC",
        // Bermuda Monetary Authority.
        "BM_BMA",
        // Jersey Financial Services Commission.
        "JE_JFSC",
        // Guernsey Financial Services Commission.
        "GG_GFSC",
        // Isle of Man Financial Services Authority.
        "IM_IOMFSA",
        // UK Financial Conduct Authority + HMRC.
        "UK_FCA",
        "HMRC",
        // Singapore Monetary Authority of Singapore + IRAS.
        "SG_MAS",
        "IRAS",
        // Hong Kong HKMA + SFC.
        "HK_HKMA",
        "HK_SFC",
        // Germany BaFin + EU EBA.
        "DE_BAFIN",
        "EU_EBA",
        // UAE Central Bank + Securities Authority + DIFC + ADGM regulators.
        "AE_CBUAE",
        "AE_SCA",
        "AE_DFSA",
        "AE_FSRA",
        // Delaware Court of Chancery — DGCL §141(a) fit-and-proper
        // determinations (modules/lex/usa/states/us-de/dgcl_corporate_governance.lex
        // Rule 9). Underscored form for the Lex name; the kernel
        // authority-graph slug remains us-de-court-of-chancery.
        "US_DE_Court_Of_Chancery",
        // Prospera ZEDE Council — authority for council-resolution
        // discretion holes (modules/lex/prospera/authority_council_approval.lex).
        "Prospera_Council",
        // ── Typed-discretion-hole markers ────────────────────────────
        // Each names a discretion hole that is presently counsel-attested
        // at runtime; the prelude resolves the name so elaboration
        // succeeds. Closure to first-class typed-discretion-hole terms
        // is tracked in the F51-LEX-COVERAGE follow-up frontier.
        "DitcPenaltyAssessment",                 // cayman/tax_neutrality.lex
        "HmrcEnquiryDiscretion",                 // uk/tax_corporation_tax.lex
        "DiscoveryAssessment",                   // uk/tax_corporation_tax.lex
        "ComptrollerDiscretion",                 // singapore/tax_treaties.lex
        "GeneralAntiAvoidanceRule",              // singapore/tax_treaties.lex
        "ArbitralMeritDetermination",            // prospera/arbitration.lex
        "CouncilResolutionIssuance",             // prospera/authority_council_approval.lex
        "USPersonDetermination",                 // prospera/investor_classification.lex
        "AccreditedInvestorVerification",        // prospera/investor_classification.lex
        "RegimeAvailabilityDetermination",       // prospera/regime_selector.lex
        "HondurasLMVDigitalAssetClassification", // prospera/fundraising_regime_classifier.lex
        "AdequateProceduresDetermination",       // uk/bribery_act_2010.lex
    ] {
        ctx = ctx.with_named_constant(authority_ref, constant("ComplianceTag"));
    }

    ctx
}

/// Build the compatibility compliance prelude.
///
/// This preserves the historical jurisdiction/regulator vocabulary for old
/// rule-corpus tests and downstream callers that still use
/// `compliance_prelude()` as a fixture surface.
pub fn compliance_prelude() -> Context {
    legacy_fixture_prelude()
}

/// Build the production compliance prelude.
///
/// Production callers should use [`production_prelude`] plus pack-local
/// signatures instead of depending on the historical fixture vocabulary.
pub fn production_prelude() -> Context {
    structural_prelude()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typecheck::{check, infer};

    // ── Nat-literal value-pattern marker (exact-count thresholds) ──────────

    #[test]
    fn nat_marker_prefix_matches_evaluator() {
        // The parser-side marker shape and the evaluator-side encoding MUST be
        // byte-identical, otherwise a `| <n> =>` pattern would never match the
        // evaluated scrutinee. `crate::evaluate::NON_ZERO_NAT_PREFIX` aliases
        // this constant, so the equality is also enforced at compile time; this
        // test documents the load-bearing invariant explicitly.
        assert_eq!(NON_ZERO_NAT_PREFIX, "__NonZeroNat:");
    }

    #[test]
    fn is_non_zero_nat_marker_recognizes_only_well_formed_markers() {
        assert!(is_non_zero_nat_marker("__NonZeroNat:1"));
        assert!(is_non_zero_nat_marker("__NonZeroNat:2"));
        assert!(is_non_zero_nat_marker("__NonZeroNat:1000"));
        // Not a marker: empty count, non-digit suffix, missing prefix, `Zero`.
        assert!(!is_non_zero_nat_marker("__NonZeroNat:"));
        assert!(!is_non_zero_nat_marker("__NonZeroNat:x"));
        assert!(!is_non_zero_nat_marker("__NonZeroNat:1a"));
        assert!(!is_non_zero_nat_marker("Zero"));
        assert!(!is_non_zero_nat_marker("Compliant"));
    }

    #[test]
    fn nat_constructor_admits_zero_and_positive_markers() {
        assert!(is_nat_constructor("Zero"));
        assert!(is_nat_constructor("__NonZeroNat:1"));
        assert!(is_nat_constructor(&encode_non_zero_nat_marker(2)));
        assert!(is_nat_constructor(&encode_non_zero_nat_marker(42)));
        assert!(!is_nat_constructor("Compliant"));
        assert!(!is_nat_constructor("True"));
    }

    #[test]
    fn nat_marker_classifies_under_nat_datatype() {
        // A positive-count marker is a value-member of `Nat` exactly as the
        // named `Zero` constructor is — this is what lets the match
        // admissibility checker resolve the scrutinee datatype to `Nat` and
        // accept the branch.
        assert_eq!(PreludeRegistry::constructor_datatype("Zero"), Some("Nat"));
        assert_eq!(
            PreludeRegistry::constructor_datatype("__NonZeroNat:3"),
            Some("Nat")
        );
        assert_eq!(
            PreludeRegistry::constructor_datatypes("__NonZeroNat:3"),
            vec!["Nat"]
        );
        assert!(is_prelude_constructor("__NonZeroNat:3"));
    }

    #[test]
    fn structural_prelude_contains_only_structural_symbols() {
        let ctx = structural_prelude();

        // 2026-05-07 (G2 closure — MISSING-PRELUDE migration): raised
        // from 18 to 20 to admit the SanctionsResult constructor
        // extensions `Match` and `PotentialMatch` lifted out of
        // modules/lex/cayman/sanctions_screening_loop.lex.
        assert_eq!(ctx.global_len(), 20);

        for name in CORE_TYPES {
            assert_eq!(ctx.lookup_named_constant(name), Some(&type0()));
        }
        for name in VERDICT_CONSTRUCTORS {
            assert_eq!(
                ctx.lookup_named_constant(name),
                Some(&constant("ComplianceVerdict"))
            );
        }
        for name in BOOL_CONSTRUCTORS {
            assert_eq!(ctx.lookup_named_constant(name), Some(&constant("Bool")));
        }
        for name in NAT_CONSTRUCTORS {
            assert_eq!(ctx.lookup_named_constant(name), Some(&constant("Nat")));
        }
        for name in SANCTIONS_CONSTRUCTORS {
            assert_eq!(
                ctx.lookup_named_constant(name),
                Some(&constant("SanctionsResult"))
            );
        }

        assert_eq!(
            ctx.lookup_named_constant("Some"),
            Some(&arrow(
                constant("IncorporationContext"),
                constant("ComplianceTag")
            ))
        );
        assert_eq!(
            ctx.lookup_named_constant("Cons"),
            Some(&arrow(
                constant("IncorporationContext"),
                arrow(constant("ComplianceTag"), constant("ComplianceTag"))
            ))
        );
    }

    #[test]
    fn structural_prelude_excludes_jurisdiction_and_regulator_symbols() {
        let ctx = structural_prelude();
        let excluded = [
            "ADGM",
            "GB",
            "HN",
            "PK",
            "SC",
            "SG",
            "VG",
            "fsra_authorization_status",
            "adgm_statutory_sanctions_screen",
            "US_SEC_Counsel",
        ];

        for name in excluded {
            assert!(
                !ctx.contains_named_constant(name),
                "structural prelude must not contain {name}"
            );
        }
    }

    #[test]
    fn legacy_fixture_prelude_preserves_old_fixture_surface() {
        let legacy = legacy_fixture_prelude();
        let compliance = compliance_prelude();

        // 2026-05-07 (G2 closure — MISSING-PRELUDE migration): raised
        // from 433 to 601 to admit the cross-jurisdictional rule
        // surface lifted out of `-- MISSING-PRELUDE: <name>` markers
        // in ~/kernel/modules/lex/{adgm,cayman,prospera,uk,singapore,
        // hong_kong,uae,eu,de,bermuda,jersey,guernsey,iom,bvi,
        // luxembourg,usa/states/...}/*.lex. See the size-pin block
        // below in `prelude_context_size_is_stable` for the per-
        // category accounting.
        assert_eq!(legacy.global_len(), 601);
        assert_eq!(compliance.global_len(), legacy.global_len());

        for name in RULE_REFERENCED_CONSTANTS
            .iter()
            .chain(RULE_REFERENCED_CONSTRUCTORS.iter())
        {
            assert!(
                legacy.contains_named_constant(name),
                "legacy fixture prelude missing old symbol: {name}"
            );
        }
    }

    #[test]
    fn prelude_covers_all_rule_symbols() {
        let ctx = legacy_fixture_prelude();

        for name in RULE_REFERENCED_CONSTANTS
            .iter()
            .chain(RULE_REFERENCED_CONSTRUCTORS.iter())
        {
            assert!(
                ctx.contains_named_constant(name),
                "missing prelude symbol: {name}"
            );
        }
    }

    #[test]
    fn prelude_contains_expected_types() {
        let ctx = compliance_prelude();

        for name in CORE_TYPES {
            assert_eq!(ctx.lookup_named_constant(name), Some(&type0()));
        }
    }

    #[test]
    fn prelude_contains_compliance_verdict_and_constructors() {
        let ctx = compliance_prelude();

        assert_eq!(
            ctx.lookup_named_constant("ComplianceVerdict"),
            Some(&type0())
        );
        assert_eq!(
            ctx.lookup_named_constant("Compliant"),
            Some(&constant("ComplianceVerdict"))
        );
        assert_eq!(
            ctx.lookup_named_constant("NonCompliant"),
            Some(&constant("ComplianceVerdict"))
        );
        assert_eq!(
            ctx.lookup_named_constant("Pending"),
            Some(&constant("ComplianceVerdict"))
        );
    }

    #[test]
    fn prelude_contains_incorporation_accessors() {
        let ctx = legacy_fixture_prelude();
        let nat_accessor = arrow(constant("IncorporationContext"), constant("Nat"));
        let tag_accessor = arrow(constant("IncorporationContext"), constant("ComplianceTag"));

        assert_eq!(
            ctx.lookup_named_constant("director_count"),
            Some(&nat_accessor)
        );
        assert_eq!(
            ctx.lookup_named_constant("registered_agent"),
            Some(&tag_accessor)
        );
        assert_eq!(
            ctx.lookup_named_constant("company_class"),
            Some(&tag_accessor)
        );
    }

    #[test]
    fn prelude_contains_sanctions_result_and_oracles() {
        let ctx = legacy_fixture_prelude();
        let oracle_ty = arrow(
            constant("IncorporationContext"),
            constant("SanctionsResult"),
        );

        assert_eq!(ctx.lookup_named_constant("SanctionsResult"), Some(&type0()));
        assert_eq!(
            ctx.lookup_named_constant("Clear"),
            Some(&constant("SanctionsResult"))
        );
        assert_eq!(
            ctx.lookup_named_constant("sanctions_check"),
            Some(&oracle_ty)
        );
        assert_eq!(
            ctx.lookup_named_constant("adgm_statutory_sanctions_screen"),
            Some(&oracle_ty)
        );
    }

    #[test]
    fn prelude_contains_bool_nat_and_their_constructors() {
        let ctx = compliance_prelude();

        assert_eq!(ctx.lookup_named_constant("Bool"), Some(&type0()));
        assert_eq!(ctx.lookup_named_constant("True"), Some(&constant("Bool")));
        assert_eq!(ctx.lookup_named_constant("False"), Some(&constant("Bool")));
        assert_eq!(ctx.lookup_named_constant("Nat"), Some(&type0()));
        assert_eq!(ctx.lookup_named_constant("Zero"), Some(&constant("Nat")));
    }

    #[test]
    fn prelude_supports_simple_constant_typechecking() {
        let ctx = compliance_prelude();
        let verdict = constant("Compliant");

        assert_eq!(
            infer(&ctx, &verdict).unwrap(),
            constant("ComplianceVerdict")
        );
        check(&ctx, &verdict, &constant("ComplianceVerdict")).unwrap();
    }

    #[test]
    fn prelude_context_size_is_stable() {
        let ctx = legacy_fixture_prelude();

        // 2026-04-24 (Phase 5.2 — USA Reg D §230.503): raised from 393
        // to 433 to admit 40 new symbols lifted for
        // modules/lex/usa/regulation_d_503.lex:
        //   +1  CORE_TYPES       (Date)
        //   +28 TAG_CONSTRUCTORS (7 ExemptionCode + 5 FormDFilingStatus +
        //                         3 FormDDeadlineStatus + 4
        //                         AccreditedVerificationStatus +
        //                         3 SolicitationStatus + 3 BadActorStatus +
        //                         3 EdgarCredentialStatus)
        //   +7  TAG_ACCESSORS    (exemption_relied_on, form_d_filing_status,
        //                         form_d_deadline_status,
        //                         accredited_investor_verification_status,
        //                         general_solicitation_status,
        //                         bad_actor_disqualification_status,
        //                         edgar_credential_status)
        //   +3  BOOL_ACCESSORS   (form_d_filed, issuer_is_covered_person,
        //                         offering_still_active)
        //   +1  with_named_constant (US_SEC_Counsel authority marker)
        // Existing overlaps NOT re-declared: `Registered` (ShareForm),
        // `Filed` (Status), `UnderReview` (Status) — the Reg D accessor
        // family sets in accessor_families() admit both the ExemptionCode/
        // FormDFilingStatus/BadActorStatus families AND the overlapping
        // ShareForm/Status families, so those existing constructors
        // continue to resolve unchanged.
        //
        // 2026-05-07 (G2 closure — MISSING-PRELUDE migration): raised
        // from 433 to 601 (+168) to admit the cross-jurisdictional rule
        // surface lifted out of `-- MISSING-PRELUDE: <name>` markers
        // in ~/kernel/modules/lex/{adgm,cayman,prospera,uk,singapore,
        // hong_kong,uae,eu,de,bermuda,jersey,guernsey,iom,bvi,
        // luxembourg,usa/states/...}/*.lex. Per-category accounting:
        //   +2  SANCTIONS_CONSTRUCTORS (Match, PotentialMatch — for
        //                               cayman/sanctions_screening_loop.lex)
        //   +9  TAG_CONSTRUCTORS · Jurisdiction (USDE, BM, JE, GG, IM,
        //                                       DE, EU, AE, BV)
        //  +22  TAG_CONSTRUCTORS · AmlCddRegime (KyCimaAmlr,
        //                          BmBmaGuidance, JeJfscHandbook,
        //                          GgGfscHandbook, ImIomfsaHandbook,
        //                          VgFscCode, UkMlr2017, UsCipMinimum,
        //                          SgMasNotice626, SgVccN01,
        //                          SgSfa04N02, HkAmloSch2,
        //                          HkHkmaGuideline, HkSfcGuideline,
        //                          DeGwG, EuFiveAmld, EuSixAmld,
        //                          EuAmlr, AeCbuaeStandards,
        //                          AeScaRegulations, AeDifcDfsa,
        //                          AeAdgmFsra)
        //  +50  TAG_CONSTRUCTORS · Status (AML/CDD ladder rungs, OFAC
        //                          SDN buckets, sanctions freshness, ES
        //                          adequacy, VASP capital/supervision/
        //                          tech-audit/travel-rule/token-
        //                          classification, Cayman PoCA STR/FIU
        //                          buckets, PEP/monitoring extensions,
        //                          Prospera FSRA/KYC ladders. `Adequate`
        //                          and `Segregated` reused from existing
        //                          JurisdictionAdequacy / Status families.)
        //   +3  TAG_CONSTRUCTORS · LicenseType (VaspLicenseCustodian,
        //                          VaspLicenseTradingPlatform,
        //                          VaspRegistrationOnly — Cayman VASP
        //                          Act 2020 license categories.)
        //   +5  NAT_ACCESSORS (aifm_local_staff_count,
        //                      aifm_conducting_officer_count,
        //                      vas_activity_classes, transfer_amount_usd,
        //                      es_activity_class_count)
        //   +7  BOOL_ACCESSORS (proof_of_address_on_file,
        //                       requires_poa_composed, path_requires_poa,
        //                       aifm_physical_office_in_lu,
        //                       holding_company_reduced_substance,
        //                       economic_substance_applicability_attestation,
        //                       simplified_due_diligence_eligible)
        //  +37  TAG_ACCESSORS (aml_cdd_jurisdiction, recordkeeping_status,
        //                      mlro_appointment_status, aml_audit_status,
        //                      aml_program_status, ofac_sdn_screening_status,
        //                      screening_freshness_status, vasp_license_category,
        //                      segregation_status, prudential_va_module_status,
        //                      es_filing_status, ciga_status,
        //                      adequate_employees_and_premises_status,
        //                      adequate_opex_status,
        //                      holding_company_reduced_substance_status,
        //                      ditc_enrolment_status, crs_filing_status,
        //                      cbcr_filing_status, self_certification_status,
        //                      tax_exemption_undertaking_status,
        //                      ct_filing_status, vat_registration_status,
        //                      cit_filing_status, gst_registration_status,
        //                      fiu_report_status, vasp_supervision_status,
        //                      vasp_capital_adequacy, technology_audit_status,
        //                      travel_rule_status, token_classification_status,
        //                      selected_regime_status,
        //                      reciprocity_attestation_status,
        //                      council_approval_receipt_status,
        //                      kyc_status, aifm_portfolio_manager_location,
        //                      aifm_risk_manager_location,
        //                      beneficiary_vasp_jurisdiction)
        //  +33  with_named_constant (G2 authority refs DITC, KY_CIMA,
        //                            VG_FSC, BM_BMA, JE_JFSC, GG_GFSC,
        //                            IM_IOMFSA, UK_FCA, HMRC, SG_MAS,
        //                            IRAS, HK_HKMA, HK_SFC, DE_BAFIN,
        //                            EU_EBA, AE_CBUAE, AE_SCA, AE_DFSA,
        //                            AE_FSRA, US_DE_Court_Of_Chancery,
        //                            Prospera_Council; typed-discretion-
        //                            hole markers DitcPenaltyAssessment,
        //                            HmrcEnquiryDiscretion,
        //                            DiscoveryAssessment,
        //                            ComptrollerDiscretion,
        //                            GeneralAntiAvoidanceRule,
        //                            ArbitralMeritDetermination,
        //                            CouncilResolutionIssuance,
        //                            USPersonDetermination,
        //                            AccreditedInvestorVerification,
        //                            RegimeAvailabilityDetermination,
        //                            HondurasLMVDigitalAssetClassification,
        //                            AdequateProceduresDetermination)
        //  Subtotal: 2+9+22+50+3+5+7+37+33 = 168.
        assert_eq!(ctx.global_len(), 601);
    }

    // ── Constructor family tests ────────────────────────────────────

    #[test]
    fn every_tag_constructor_has_a_family() {
        for name in TAG_CONSTRUCTORS {
            assert!(
                constructor_family(name).is_some(),
                "TAG_CONSTRUCTOR {name} has no constructor family assignment"
            );
        }
    }

    #[test]
    fn every_tag_accessor_has_families() {
        for name in TAG_ACCESSORS {
            assert!(
                accessor_families(name).is_some(),
                "TAG_ACCESSOR {name} has no accessor family assignment"
            );
        }
    }

    #[test]
    fn non_tag_constructors_return_none() {
        // Verdict, Bool, Nat, Sanctions constructors are not TAG_CONSTRUCTORS
        assert_eq!(constructor_family("Compliant"), None);
        assert_eq!(constructor_family("True"), None);
        assert_eq!(constructor_family("Zero"), None);
        assert_eq!(constructor_family("Clear"), None);
        assert_eq!(constructor_family("Nonexistent"), None);
    }

    #[test]
    fn validate_audit_status_against_audit_complete_is_valid() {
        assert!(validate_match_family("audit_status", "AuditComplete"));
        assert!(validate_match_family("audit_status", "AuditDue"));
        assert!(validate_match_family("audit_status", "AuditOverdue"));
        assert!(validate_match_family("audit_status", "AuditExempt"));
    }

    #[test]
    fn validate_audit_status_against_adgm_is_invalid() {
        assert!(!validate_match_family("audit_status", "ADGM"));
    }

    #[test]
    fn validate_audit_status_against_jurisdiction_constructors_invalid() {
        for j in &["ADGM", "GB", "HK", "SC", "PK", "SG", "KY", "VG", "LU", "HN"] {
            assert!(
                !validate_match_family("audit_status", j),
                "audit_status should reject jurisdiction constructor {j}"
            );
        }
    }

    #[test]
    fn validate_entity_type_against_entity_constructors_valid() {
        assert!(validate_match_family("entity_type", "IBC"));
        assert!(validate_match_family("entity_type", "PublicCompany"));
        assert!(validate_match_family("entity_type", "ExemptedCompany"));
    }

    #[test]
    fn validate_entity_type_against_status_is_invalid() {
        assert!(!validate_match_family("entity_type", "AmlCompliant"));
        assert!(!validate_match_family("entity_type", "Filed"));
    }

    #[test]
    fn validate_office_country_against_jurisdictions_valid() {
        assert!(validate_match_family("office_country", "ADGM"));
        assert!(validate_match_family("office_country", "GB"));
        assert!(validate_match_family("office_country", "PK"));
    }

    #[test]
    fn validate_office_country_against_status_invalid() {
        assert!(!validate_match_family("office_country", "AuditComplete"));
        assert!(!validate_match_family("office_country", "Active"));
    }

    #[test]
    fn validate_risk_rating_against_risk_levels_valid() {
        assert!(validate_match_family("customer_risk_rating", "HighRisk"));
        assert!(validate_match_family("customer_risk_rating", "MediumRisk"));
        assert!(validate_match_family("customer_risk_rating", "LowRisk"));
    }

    #[test]
    fn validate_risk_rating_against_jurisdiction_invalid() {
        assert!(!validate_match_family("customer_risk_rating", "ADGM"));
    }

    #[test]
    fn validate_share_form_against_share_constructors_valid() {
        assert!(validate_match_family("share_form", "Bearer"));
        assert!(validate_match_family("share_form", "Registered"));
    }

    #[test]
    fn validate_share_form_against_entity_type_invalid() {
        assert!(!validate_match_family("share_form", "IBC"));
    }

    #[test]
    fn validate_license_accessor_accepts_both_license_and_status() {
        // License accessors accept both LicenseType and Status families
        assert!(validate_match_family(
            "fca_authorization_status",
            "FcaAuthorized"
        ));
        assert!(validate_match_family(
            "fca_authorization_status",
            "FcaApplied"
        ));
        assert!(validate_match_family("fca_authorization_status", "Revoked"));
        assert!(validate_match_family(
            "fca_authorization_status",
            "Suspended"
        ));
    }

    #[test]
    fn validate_license_accessor_rejects_jurisdiction() {
        assert!(!validate_match_family("fca_authorization_status", "ADGM"));
        assert!(!validate_match_family("fca_authorization_status", "GB"));
    }

    #[test]
    fn validate_name_suffix_valid() {
        assert!(validate_match_family("name_suffix", "Ltd"));
        assert!(validate_match_family("name_suffix", "Limited"));
        assert!(validate_match_family("name_suffix", "BC"));
        assert!(validate_match_family("name_suffix", "SA"));
        assert!(validate_match_family("name_suffix", "SARL"));
    }

    #[test]
    fn validate_name_suffix_rejects_status() {
        assert!(!validate_match_family("name_suffix", "Active"));
    }

    #[test]
    fn validate_frequency_accessor_valid() {
        assert!(validate_match_family("nav_frequency_status", "Daily"));
        assert!(validate_match_family("nav_frequency_status", "Weekly"));
        assert!(validate_match_family("nav_frequency_status", "Monthly"));
        assert!(validate_match_family("nav_frequency_status", "Quarterly"));
    }

    #[test]
    fn validate_frequency_accessor_rejects_entity_type() {
        assert!(!validate_match_family("nav_frequency_status", "IBC"));
    }

    #[test]
    fn validate_unknown_accessor_conservative_accept() {
        assert!(validate_match_family("unknown_accessor", "ADGM"));
        assert!(validate_match_family("unknown_accessor", "AuditComplete"));
    }

    #[test]
    fn validate_unknown_constructor_conservative_accept() {
        assert!(validate_match_family("audit_status", "UnknownCtor"));
    }

    #[test]
    fn validate_jurisdiction_adequacy_valid() {
        assert!(validate_match_family(
            "transfer_jurisdiction_adequacy",
            "AdequateJurisdiction"
        ));
        assert!(validate_match_family(
            "transfer_jurisdiction_adequacy",
            "InadequateJurisdiction"
        ));
        assert!(validate_match_family(
            "transfer_jurisdiction_adequacy",
            "Adequate"
        ));
    }

    #[test]
    fn validate_jurisdiction_adequacy_rejects_jurisdiction() {
        assert!(!validate_match_family(
            "transfer_jurisdiction_adequacy",
            "ADGM"
        ));
    }

    #[test]
    fn constructor_family_coverage_matches_tag_constructors() {
        // Verify that the set of constructors handled in constructor_family()
        // exactly matches TAG_CONSTRUCTORS (no missing, no extras).
        let mut family_count = 0;
        for name in TAG_CONSTRUCTORS {
            if constructor_family(name).is_some() {
                family_count += 1;
            }
        }
        assert_eq!(
            family_count,
            TAG_CONSTRUCTORS.len(),
            "some TAG_CONSTRUCTORS are missing from constructor_family()"
        );
    }

    // ── USA Reg D §230.503 extension tests (Phase 5.2) ──────────────

    /// Every symbol lifted into the prelude for
    /// `modules/lex/usa/regulation_d_503.lex` resolves via the prelude
    /// context lookup. This is the file-level coverage gate for the Reg D
    /// wave: if a symbol is enumerated in regulation_d_503's PENDING-PRELUDE
    /// block but missing from prelude.rs, this test fails.
    #[test]
    fn reg_d_prelude_extensions_are_resolvable() {
        let ctx = legacy_fixture_prelude();

        // Core types
        let reg_d_types: &[&str] = &["Date"];

        // Authority marker
        let reg_d_authorities: &[&str] = &["US_SEC_Counsel"];

        // 7 TAG_ACCESSORS
        let reg_d_tag_accessors: &[&str] = &[
            "accredited_investor_verification_status",
            "bad_actor_disqualification_status",
            "edgar_credential_status",
            "exemption_relied_on",
            "form_d_deadline_status",
            "form_d_filing_status",
            "general_solicitation_status",
        ];

        // 3 BOOL_ACCESSORS
        let reg_d_bool_accessors: &[&str] = &[
            "form_d_filed",
            "issuer_is_covered_person",
            "offering_still_active",
        ];

        // 28 new TAG_CONSTRUCTORS (grouped by family)
        let reg_d_tag_constructors: &[&str] = &[
            // ExemptionCode (7 new; `Registered` reused from ShareForm)
            "RegA",
            "RegCF",
            "RegS",
            "Rule504",
            "Rule506b",
            "Rule506c",
            "Section4a2",
            // FormDFilingStatus (5 new; `Filed` reused from Status)
            "Drafted",
            "FiledLate",
            "NotDue",
            "ReadyForCounsel",
            "Superseded",
            // FormDDeadlineStatus (3)
            "NoFirstSale",
            "PastDeadline",
            "Within15Days",
            // AccreditedVerificationStatus (4)
            "NotRequired",
            "VerificationComplete",
            "VerificationFailed",
            "VerificationPending",
            // SolicitationStatus (3)
            "NoSolicitation",
            "PermittedSolicitation506c",
            "ProhibitedSolicitation506b",
            // BadActorStatus (3 new; `UnderReview` reused from Status)
            "Disqualified",
            "NoDisqualification",
            "Waived",
            // EdgarCredentialStatus (3)
            "CounselFilingPath",
            "CredentialsAbsent",
            "CredentialsProvisioned",
        ];

        for name in reg_d_types
            .iter()
            .chain(reg_d_authorities.iter())
            .chain(reg_d_tag_accessors.iter())
            .chain(reg_d_bool_accessors.iter())
            .chain(reg_d_tag_constructors.iter())
        {
            assert!(
                ctx.contains_named_constant(name),
                "Reg D §230.503 prelude extension missing symbol: {name}"
            );
        }

        // Pin the delta count so a future accidental removal of any
        // one symbol is caught by arithmetic too, not just membership.
        let total_new = reg_d_types.len()
            + reg_d_authorities.len()
            + reg_d_tag_accessors.len()
            + reg_d_bool_accessors.len()
            + reg_d_tag_constructors.len();
        assert_eq!(total_new, 40, "expected 40 new Reg D prelude symbols");
    }

    /// `Date` is registered at universe level 0 like the other CORE_TYPES.
    /// Pinned here so a future migration that demotes `Date` to a lower
    /// level (or moves it off the prelude) is caught immediately.
    #[test]
    fn reg_d_date_type_is_registered_at_type_0() {
        let ctx = legacy_fixture_prelude();
        assert_eq!(ctx.lookup_named_constant("Date"), Some(&type0()));
    }

    /// The ExemptionCode family's `Registered` arm reuses the existing
    /// ShareForm `Registered` constructor. This test pins the policy:
    /// `exemption_relied_on` must admit ShareForm members (for the
    /// Rule 1 `| Registered => Compliant` arm) AND the new
    /// ExemptionCode members. Family coverage is verified via
    /// `validate_match_family` which consults both family sets.
    #[test]
    fn reg_d_exemption_relied_on_admits_both_exemption_code_and_shareform() {
        // ExemptionCode members resolve.
        assert!(validate_match_family("exemption_relied_on", "Rule506b"));
        assert!(validate_match_family("exemption_relied_on", "Rule506c"));
        assert!(validate_match_family("exemption_relied_on", "Rule504"));
        assert!(validate_match_family("exemption_relied_on", "Section4a2"));
        assert!(validate_match_family("exemption_relied_on", "RegS"));
        assert!(validate_match_family("exemption_relied_on", "RegCF"));
        assert!(validate_match_family("exemption_relied_on", "RegA"));
        // ShareForm `Registered` (existing) admits via the overlap.
        assert!(validate_match_family("exemption_relied_on", "Registered"));
        // Status members should NOT admit (defence against accidentally
        // widening the accessor).
        assert!(!validate_match_family("exemption_relied_on", "Active"));
        assert!(!validate_match_family(
            "exemption_relied_on",
            "AmlCompliant"
        ));
    }

    /// `form_d_filing_status` accepts both the new FormDFilingStatus
    /// family AND the Status family (so the existing `Filed`
    /// constructor — which is a canonical Status member — resolves for
    /// the Rule 2 `| Filed => Compliant` arm).
    #[test]
    fn reg_d_form_d_filing_status_admits_both_families() {
        // FormDFilingStatus members
        assert!(validate_match_family("form_d_filing_status", "NotDue"));
        assert!(validate_match_family(
            "form_d_filing_status",
            "ReadyForCounsel"
        ));
        assert!(validate_match_family("form_d_filing_status", "Drafted"));
        assert!(validate_match_family("form_d_filing_status", "FiledLate"));
        assert!(validate_match_family("form_d_filing_status", "Superseded"));
        // Status `Filed` admits via the overlap.
        assert!(validate_match_family("form_d_filing_status", "Filed"));
        // Jurisdiction / unrelated family rejected.
        assert!(!validate_match_family("form_d_filing_status", "ADGM"));
        assert!(!validate_match_family("form_d_filing_status", "IBC"));
    }

    /// `bad_actor_disqualification_status` accepts the new BadActorStatus
    /// family AND Status (for the existing `UnderReview` constructor used
    /// in the Rule 3 `| UnderReview => Pending` arm).
    #[test]
    fn reg_d_bad_actor_status_admits_both_families() {
        // BadActorStatus members
        assert!(validate_match_family(
            "bad_actor_disqualification_status",
            "NoDisqualification"
        ));
        assert!(validate_match_family(
            "bad_actor_disqualification_status",
            "Disqualified"
        ));
        assert!(validate_match_family(
            "bad_actor_disqualification_status",
            "Waived"
        ));
        // Status `UnderReview` admits via the overlap.
        assert!(validate_match_family(
            "bad_actor_disqualification_status",
            "UnderReview"
        ));
        // Unrelated family rejected.
        assert!(!validate_match_family(
            "bad_actor_disqualification_status",
            "ADGM"
        ));
    }

    /// Pure-family accessors reject cross-family constructors. This is
    /// the type-system-above-flat-ComplianceTag discipline applied to
    /// the Reg D additions.
    #[test]
    fn reg_d_pure_family_accessors_reject_cross_family() {
        // form_d_deadline_status is FormDDeadlineStatus only.
        assert!(validate_match_family(
            "form_d_deadline_status",
            "Within15Days"
        ));
        assert!(!validate_match_family("form_d_deadline_status", "Filed"));
        assert!(!validate_match_family("form_d_deadline_status", "ADGM"));

        // accredited_investor_verification_status is
        // AccreditedVerificationStatus only.
        assert!(validate_match_family(
            "accredited_investor_verification_status",
            "VerificationComplete"
        ));
        assert!(!validate_match_family(
            "accredited_investor_verification_status",
            "Active"
        ));

        // general_solicitation_status is SolicitationStatus only.
        assert!(validate_match_family(
            "general_solicitation_status",
            "NoSolicitation"
        ));
        assert!(!validate_match_family(
            "general_solicitation_status",
            "Filed"
        ));

        // edgar_credential_status is EdgarCredentialStatus only.
        assert!(validate_match_family(
            "edgar_credential_status",
            "CredentialsProvisioned"
        ));
        assert!(!validate_match_family("edgar_credential_status", "Filed"));
    }

    /// Every Reg D constructor registered in TAG_CONSTRUCTORS has a
    /// family assignment in constructor_family(). This is the
    /// Reg-D-specific instance of the global invariant enforced by
    /// `constructor_family_coverage_matches_tag_constructors`.
    #[test]
    fn reg_d_every_new_constructor_has_a_family() {
        for name in &[
            "RegA",
            "RegCF",
            "RegS",
            "Rule504",
            "Rule506b",
            "Rule506c",
            "Section4a2",
            "Drafted",
            "FiledLate",
            "NotDue",
            "ReadyForCounsel",
            "Superseded",
            "NoFirstSale",
            "PastDeadline",
            "Within15Days",
            "NotRequired",
            "VerificationComplete",
            "VerificationFailed",
            "VerificationPending",
            "NoSolicitation",
            "PermittedSolicitation506c",
            "ProhibitedSolicitation506b",
            "Disqualified",
            "NoDisqualification",
            "Waived",
            "CounselFilingPath",
            "CredentialsAbsent",
            "CredentialsProvisioned",
        ] {
            assert!(
                constructor_family(name).is_some(),
                "Reg D constructor {name} has no family assignment"
            );
        }
    }

    // ── G2 closure (2026-05-07) — MISSING-PRELUDE migration tests ────

    /// Every symbol lifted into the prelude for the
    /// `~/kernel/modules/lex/{adgm,cayman,prospera,uk,singapore,...}/*.lex`
    /// MISSING-PRELUDE markers resolves via the prelude context lookup.
    /// File-level coverage gate for the G2 closure: if any G2 symbol
    /// regresses out of the prelude, this test fails.
    #[test]
    fn g2_prelude_extensions_are_resolvable() {
        let ctx = legacy_fixture_prelude();

        // 9 new Jurisdiction codes (USDE Delaware + 8 harbor markers).
        let g2_jurisdictions: &[&str] = &["USDE", "BM", "JE", "GG", "IM", "DE", "EU", "AE", "BV"];

        // 22 AmlCddRegime constructors (per-jurisdiction AML/CDD rule-sets).
        let g2_aml_cdd_regimes: &[&str] = &[
            "KyCimaAmlr",
            "BmBmaGuidance",
            "JeJfscHandbook",
            "GgGfscHandbook",
            "ImIomfsaHandbook",
            "VgFscCode",
            "UkMlr2017",
            "UsCipMinimum",
            "SgMasNotice626",
            "SgVccN01",
            "SgSfa04N02",
            "HkAmloSch2",
            "HkHkmaGuideline",
            "HkSfcGuideline",
            "DeGwG",
            "EuFiveAmld",
            "EuSixAmld",
            "EuAmlr",
            "AeCbuaeStandards",
            "AeScaRegulations",
            "AeDifcDfsa",
            "AeAdgmFsra",
        ];

        // Status / LicenseType ladder rungs lifted out of MISSING-PRELUDE
        // markers (52 across AML/CDD, sanctions, ES adequacy, VASP, KYC).
        let g2_status_extensions: &[&str] = &[
            "Appointed",
            "NotAppointed",
            "AuditCurrent",
            "Breached",
            "NoMatchReportingNotRequired",
            "MatchReportedToFiu",
            "MatchPendingReport",
            "MatchUnreported",
            "OfacClear",
            "OfacMatch",
            "OfacPotentialMatch",
            "OfacNotApplicable",
            "FreshWithin24h",
            "ExpiredBeyond24h",
            "Inadequate",
            "ReducedSubstanceMet",
            "ReducedSubstanceNotMet",
            "CigaPerformedLocally",
            "CigaOutsourcedExternally",
            "CigaNotPerformed",
            "TravelRuleImplemented",
            "TravelRuleMissing",
            "TravelRulePartial",
            "TechAuditPassed",
            "TechAuditFailed",
            "TechAuditPending",
            "ProgramApproved",
            "ProgramRejected",
            "AssessmentPending",
            "ClassificationFiled",
            "ClassificationMissing",
            "ClassificationDisputed",
            "NotSegregated",
            "AllPrincipalsClear",
            "AnyPrincipalFailed",
            "NoPepIdentified",
            "PepIdentifiedEddCurrent",
            "Current",
            "Lapsed",
            "CapitalMet",
            "CapitalShortfall",
            "SupervisionCurrent",
            "SupervisionInProgress",
            "SupervisionOverdue",
            "FsraAuthorized",
            "FsraSubmitted",
            "FsraRejected",
            "KycApproved",
            "KycPending",
            "KycFailed",
            "VaspLicenseCustodian",
            "VaspLicenseTradingPlatform",
            "VaspRegistrationOnly",
        ];

        // 2 SanctionsResult extensions lifted from
        // cayman/sanctions_screening_loop.lex.
        let g2_sanctions_extensions: &[&str] = &["Match", "PotentialMatch"];

        // 5 NAT_ACCESSORS.
        let g2_nat_accessors: &[&str] = &[
            "aifm_local_staff_count",
            "aifm_conducting_officer_count",
            "vas_activity_classes",
            "transfer_amount_usd",
            "es_activity_class_count",
        ];

        // 7 BOOL_ACCESSORS (composed PoA + path PoA + AIFMD substance +
        // ES applicability + simplified-DD eligibility).
        let g2_bool_accessors: &[&str] = &[
            "proof_of_address_on_file",
            "requires_poa_composed",
            "path_requires_poa",
            "aifm_physical_office_in_lu",
            "holding_company_reduced_substance",
            "economic_substance_applicability_attestation",
            "simplified_due_diligence_eligible",
        ];

        // 37 TAG_ACCESSORS (per-jurisdiction ladder accessors).
        let g2_tag_accessors: &[&str] = &[
            "aml_cdd_jurisdiction",
            "recordkeeping_status",
            "mlro_appointment_status",
            "aml_audit_status",
            "ofac_sdn_screening_status",
            "screening_freshness_status",
            "vasp_license_category",
            "segregation_status",
            "prudential_va_module_status",
            "es_filing_status",
            "ciga_status",
            "adequate_employees_and_premises_status",
            "adequate_opex_status",
            "holding_company_reduced_substance_status",
            "ditc_enrolment_status",
            "crs_filing_status",
            "cbcr_filing_status",
            "self_certification_status",
            "tax_exemption_undertaking_status",
            "ct_filing_status",
            "vat_registration_status",
            "cit_filing_status",
            "gst_registration_status",
            "fiu_report_status",
            "vasp_supervision_status",
            "vasp_capital_adequacy",
            "technology_audit_status",
            "travel_rule_status",
            "token_classification_status",
            "aml_program_status",
            "selected_regime_status",
            "reciprocity_attestation_status",
            "council_approval_receipt_status",
            "kyc_status",
            "aifm_portfolio_manager_location",
            "aifm_risk_manager_location",
            "beneficiary_vasp_jurisdiction",
        ];

        // 21 authority refs + 12 typed-discretion-hole markers.
        let g2_authority_refs: &[&str] = &[
            "DITC",
            "KY_CIMA",
            "VG_FSC",
            "BM_BMA",
            "JE_JFSC",
            "GG_GFSC",
            "IM_IOMFSA",
            "UK_FCA",
            "HMRC",
            "SG_MAS",
            "IRAS",
            "HK_HKMA",
            "HK_SFC",
            "DE_BAFIN",
            "EU_EBA",
            "AE_CBUAE",
            "AE_SCA",
            "AE_DFSA",
            "AE_FSRA",
            "US_DE_Court_Of_Chancery",
            "Prospera_Council",
            "DitcPenaltyAssessment",
            "HmrcEnquiryDiscretion",
            "DiscoveryAssessment",
            "ComptrollerDiscretion",
            "GeneralAntiAvoidanceRule",
            "ArbitralMeritDetermination",
            "CouncilResolutionIssuance",
            "USPersonDetermination",
            "AccreditedInvestorVerification",
            "RegimeAvailabilityDetermination",
            "HondurasLMVDigitalAssetClassification",
            "AdequateProceduresDetermination",
        ];

        for name in g2_jurisdictions
            .iter()
            .chain(g2_aml_cdd_regimes.iter())
            .chain(g2_status_extensions.iter())
            .chain(g2_sanctions_extensions.iter())
            .chain(g2_nat_accessors.iter())
            .chain(g2_bool_accessors.iter())
            .chain(g2_tag_accessors.iter())
            .chain(g2_authority_refs.iter())
        {
            assert!(
                ctx.contains_named_constant(name),
                "G2 prelude extension missing symbol: {name}"
            );
        }

        // Pin counts so a future accidental removal of any symbol is
        // caught by arithmetic in addition to membership.
        assert_eq!(g2_jurisdictions.len(), 9);
        assert_eq!(g2_aml_cdd_regimes.len(), 22);
        assert_eq!(g2_status_extensions.len(), 53);
        assert_eq!(g2_sanctions_extensions.len(), 2);
        assert_eq!(g2_nat_accessors.len(), 5);
        assert_eq!(g2_bool_accessors.len(), 7);
        assert_eq!(g2_tag_accessors.len(), 37);
        assert_eq!(g2_authority_refs.len(), 33);
    }

    /// G2 jurisdiction additions resolve through `office_country` /
    /// `registered_office_country` accessors. Pins the policy so the
    /// Step-3 us-de DGCL Rule 12 (`registered_office_country` against
    /// `USDE`) typechecks once the kernel side migrates.
    #[test]
    fn g2_office_country_admits_new_jurisdictions() {
        for j in &["USDE", "BM", "JE", "GG", "IM", "DE", "EU", "AE", "BV"] {
            assert!(
                validate_match_family("registered_office_country", j),
                "registered_office_country must admit G2 jurisdiction {j}"
            );
            assert!(
                validate_match_family("office_country", j),
                "office_country must admit G2 jurisdiction {j}"
            );
        }
    }

    /// `aml_cdd_jurisdiction` accessor admits the new AmlCddRegime
    /// constructors and rejects unrelated families. Pins the policy
    /// so `match ctx.aml_cdd_jurisdiction return Bool with | KyCimaAmlr
    /// => True | _ => True` typechecks across all sixteen Step-4 PoA
    /// programs.
    #[test]
    fn g2_aml_cdd_jurisdiction_admits_aml_cdd_regime_only() {
        // AmlCddRegime members admit.
        for ctor in &[
            "KyCimaAmlr",
            "BmBmaGuidance",
            "JeJfscHandbook",
            "GgGfscHandbook",
            "ImIomfsaHandbook",
            "VgFscCode",
            "UkMlr2017",
            "UsCipMinimum",
            "SgMasNotice626",
            "SgVccN01",
            "SgSfa04N02",
            "HkAmloSch2",
            "HkHkmaGuideline",
            "HkSfcGuideline",
            "DeGwG",
            "EuFiveAmld",
            "EuSixAmld",
            "EuAmlr",
            "AeCbuaeStandards",
            "AeScaRegulations",
            "AeDifcDfsa",
            "AeAdgmFsra",
        ] {
            assert!(
                validate_match_family("aml_cdd_jurisdiction", ctor),
                "aml_cdd_jurisdiction must admit AmlCddRegime constructor {ctor}"
            );
        }
        // Unrelated families rejected.
        assert!(!validate_match_family("aml_cdd_jurisdiction", "ADGM"));
        assert!(!validate_match_family("aml_cdd_jurisdiction", "Active"));
        assert!(!validate_match_family("aml_cdd_jurisdiction", "Filed"));
    }

    /// Cayman ES adequacy accessors admit both JurisdictionAdequacy
    /// (`Adequate` / `Inadequate`) and Status families. Pins the
    /// policy so modules/lex/cayman/economic_substance.lex Rule 4 + 5
    /// typecheck without re-authoring.
    #[test]
    fn g2_es_adequacy_admits_jurisdictionadequacy_and_status() {
        for accessor in &[
            "adequate_employees_and_premises_status",
            "adequate_opex_status",
        ] {
            assert!(validate_match_family(accessor, "Adequate"));
            assert!(validate_match_family(accessor, "Inadequate"));
            // Status family pass-through verdicts.
            assert!(validate_match_family(accessor, "Pending"));
        }
        // Unrelated rejected.
        assert!(!validate_match_family("adequate_opex_status", "ADGM"));
    }

    /// VASP license-category accessor admits both LicenseType (the new
    /// VaspLicense* constructors) and Status families (the existing
    /// licensing-status ladder rungs Active / Suspended / Revoked). Pins
    /// the policy so cayman/vasp_act.lex Rule 5 typechecks.
    #[test]
    fn g2_vasp_license_category_admits_licensetype_and_status() {
        for ctor in &[
            "VaspLicenseCustodian",
            "VaspLicenseTradingPlatform",
            "VaspRegistrationOnly",
        ] {
            assert!(
                validate_match_family("vasp_license_category", ctor),
                "vasp_license_category must admit {ctor}"
            );
        }
        // Status rungs admit (existing LicenseType-Status overlap pattern).
        assert!(validate_match_family("vasp_license_category", "Suspended"));
        assert!(validate_match_family("vasp_license_category", "Revoked"));
        // Unrelated rejected.
        assert!(!validate_match_family("vasp_license_category", "ADGM"));
        assert!(!validate_match_family("vasp_license_category", "IBC"));
    }

    /// AIFMD Article 18 manager-location accessors admit Jurisdiction
    /// only — the modules/lex/luxembourg/aifmd_aif_substance.lex
    /// rules scrutinise them as `Jurisdiction` returning Bool.
    #[test]
    fn g2_aifm_location_admits_jurisdiction_only() {
        for accessor in &[
            "aifm_portfolio_manager_location",
            "aifm_risk_manager_location",
        ] {
            assert!(validate_match_family(accessor, "LU"));
            assert!(validate_match_family(accessor, "GB"));
            assert!(!validate_match_family(accessor, "Active"));
            assert!(!validate_match_family(accessor, "Filed"));
        }
    }

    /// Every G2 AmlCddRegime constructor has a family assignment in
    /// `constructor_family()`. The G2-specific instance of the global
    /// invariant enforced by
    /// `constructor_family_coverage_matches_tag_constructors`.
    #[test]
    fn g2_every_aml_cdd_regime_constructor_has_a_family() {
        for name in &[
            "KyCimaAmlr",
            "BmBmaGuidance",
            "JeJfscHandbook",
            "GgGfscHandbook",
            "ImIomfsaHandbook",
            "VgFscCode",
            "UkMlr2017",
            "UsCipMinimum",
            "SgMasNotice626",
            "SgVccN01",
            "SgSfa04N02",
            "HkAmloSch2",
            "HkHkmaGuideline",
            "HkSfcGuideline",
            "DeGwG",
            "EuFiveAmld",
            "EuSixAmld",
            "EuAmlr",
            "AeCbuaeStandards",
            "AeScaRegulations",
            "AeDifcDfsa",
            "AeAdgmFsra",
        ] {
            assert_eq!(
                constructor_family(name),
                Some(ConstructorFamily::AmlCddRegime),
                "AmlCddRegime constructor {name} not assigned to AmlCddRegime family"
            );
        }
    }

    /// Sanctions-result extensions resolve as SanctionsResult-typed
    /// (not ComplianceTag). Pins the policy so
    /// modules/lex/cayman/sanctions_screening_loop.lex Rule 1
    /// (`match ctx.sanctions_check return ComplianceVerdict with
    /// | Clear => Compliant | Match => NonCompliant
    /// | PotentialMatch => Pending`) typechecks against the existing
    /// `sanctions_check` accessor of type
    /// `IncorporationContext → SanctionsResult`.
    #[test]
    fn g2_sanctions_extensions_typed_as_sanctions_result() {
        let ctx = legacy_fixture_prelude();
        for name in &["Match", "PotentialMatch"] {
            assert_eq!(
                ctx.lookup_named_constant(name),
                Some(&constant("SanctionsResult")),
                "G2 SanctionsResult constructor {name} typed incorrectly"
            );
        }
        // Existing `Clear` continues to resolve.
        assert_eq!(
            ctx.lookup_named_constant("Clear"),
            Some(&constant("SanctionsResult"))
        );
    }
}
