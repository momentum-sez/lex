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
];

const VERDICT_CONSTRUCTORS: &[&str] = &["Compliant", "NonCompliant", "Pending"];
const BOOL_CONSTRUCTORS: &[&str] = &["True", "False"];
const NAT_CONSTRUCTORS: &[&str] = &["Zero"];
const SANCTIONS_CONSTRUCTORS: &[&str] = &["Clear"];

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
];

const NAT_ACCESSORS: &[&str] = &[
    "director_count",
    "natural_person_director_count",
    "shareholder_count",
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
    "fsa_administrator_exemption",
    "fsra_authorization_required",
    "high_risk_jurisdiction_counterparty",
    "holds_client_assets",
    "incorporator_identified",
    "insider_trading_flag",
    "local_resident_director",
    "market_manipulation_flag",
    "minimum_subscription_met",
    "operating_in_adgm",
    "owners_identified",
    "parent_entity_kyc_compliant",
    "pep_or_associate",
    "processes_personal_data",
    "processes_sensitive_data",
    "public_company_authorized_capital_satisfied",
    "regulated_activity_exemption",
    "relevant_activity",
    "transfers_data_cross_border",
];

const SANCTIONS_ACCESSORS: &[&str] = &["adgm_statutory_sanctions_screen", "sanctions_check"];

const TAG_ACCESSORS: &[&str] = &[
    "accounting_records_retention_status",
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
    "employment_agreement_status",
    "employment_standards_status",
    "entity_type",
    "fca_authorization_status",
    "financial_promotion_status",
    "fit_and_proper_status",
    "fsra_authorization_status",
    "fsra_permission_status",
    "fsc_license_status",
    "fund_administrator_status",
    "fund_auditor_status",
    "fund_class",
    "fund_license_status",
    "kyc_aml_status",
    "listing_venue_status",
    "memorandum_filing_status",
    "minimum_capital_status",
    "name_suffix",
    "nav_frequency_status",
    "notarization_status",
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
    "secp_registration_status",
    "securities_dealer_license_status",
    "sez_status",
    "sfc_licence_status",
    "share_form",
    "sifc_approval_status",
    "significant_controllers_register_status",
    "str_filing_status",
    "str_filing_to_crf_status",
    "systems_controls_status",
    "tax_registration_status",
    "transfer_jurisdiction_adequacy",
    "vasp_license_status",
    "wire_transfer_compliance_status",
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
}

/// Look up the constructor family for a TAG_CONSTRUCTOR name.
///
/// Returns `None` for names that are not TAG_CONSTRUCTORS (including
/// constructors of other prelude types like `Compliant`, `True`, `Clear`).
pub fn constructor_family(name: &str) -> Option<ConstructorFamily> {
    use ConstructorFamily::*;
    match name {
        // ── Jurisdiction ────────────────────────────────────────────
        "ADGM" | "GB" | "HK" | "HN" | "KY" | "LU" | "PK" | "SC" | "SG" | "VG" => {
            Some(Jurisdiction)
        }

        // ── Entity type ─────────────────────────────────────────────
        "IBC" | "ExemptedCompany" | "PublicCompany" | "ProtectedCell" => Some(EntityType),

        // ── Risk level ──────────────────────────────────────────────
        "HighRisk" | "MediumRisk" | "LowRisk" => Some(RiskLevel),

        // ── License / authorization type ────────────────────────────
        "FcaApplied" | "FcaAuthorized" | "FullLicense" | "SpecialLicense"
        | "InPrincipleApproval" | "LicensedExchange" | "UnlicensedExchange"
        | "SfcType1DealingSecurities" | "SfcType4AdvisingSecurities"
        | "SfcType6CorporateFinance" | "SfcType9AssetManagement"
        | "CmsCorporateFinanceAdvice" | "CmsCreditRating" | "CmsCustodialServices"
        | "CmsDealingCapitalMarkets" | "CmsFundManagement" => Some(LicenseType),

        // ── Regulatory category ─────────────────────────────────────
        "Category1" | "Category2" | "Category3A" | "Category3B" | "Category3C"
        | "Category4" => Some(RegulatoryCategory),

        // ── Frequency ───────────────────────────────────────────────
        "Daily" | "Weekly" | "Monthly" | "Quarterly" => Some(Frequency),

        // ── Share form ──────────────────────────────────────────────
        "Bearer" | "Registered" => Some(ShareForm),

        // ── Offering type ───────────────────────────────────────────
        "PublicOffering" | "ExemptLimitedOfferees" | "ExemptMinimumSubscription"
        | "ExemptProfessionalInvestor" | "ExemptSmallOffer" | "NoExemption"
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
        "AtLeast7Years" | "LessThan7Years" | "Within14Days" | "Within30Days"
        | "WithinFilingDeadline" | "WithinRestrictionPeriod"
        | "WithinOneMonthOfAnniversary" => Some(TimePeriod),

        // ── Status (the large cross-cutting family) ─────────────────
        "Active" | "AgreementInPlace" | "AgreementPending" | "AllApproved"
        | "AmlCompliant" | "AmlFailed" | "AmlRemediationRequired" | "Applied"
        | "ApprovalPending" | "ArbitrationAvailable" | "ArbitrationNotAvailable"
        | "AgmDispensed" | "AgmDue" | "AgmHeld" | "AgmOverdue"
        | "AuditComplete" | "AuditDue" | "AuditExempt" | "AuditOverdue"
        | "AuditRequired" | "BelowThreshold" | "BreachNotified"
        | "BreachNotNotified" | "CapitalAdequate" | "CapitalInsufficient"
        | "CapitalPending" | "CddComplete" | "CddExpired" | "CddIncomplete"
        | "ChangeOverdue" | "ChangePendingWithin15Days" | "CharterNotRegistered"
        | "CharterPending" | "CharterRegistered" | "CnicNotVerified"
        | "CnicPending" | "CnicVerified" | "CobsCompliant" | "CobsUnderReview"
        | "ConfirmationStatementFiled" | "ConfirmationStatementOverdue"
        | "ConsentNotObtained" | "ConsentObtained"
        | "CorrespondentDdComplete" | "CorrespondentDdPending"
        | "DisclosureComplete" | "DisclosureIncomplete" | "DisclosureUnderReview"
        | "DpCompliant" | "DpNonCompliant" | "DpRemediationPending"
        | "DueSoon" | "EddComplete" | "EddIncomplete" | "EddRequired"
        | "EmploymentAgreementFiled" | "EmploymentAgreementMissing"
        | "EmploymentStandardsMet" | "EmploymentStandardsNotMet"
        | "Exempt" | "Filed" | "FitAndProperFailed" | "FitAndProperSatisfied"
        | "FitAndProperUnderReview" | "Granted"
        | "HighRiskEddComplete" | "HighRiskEddPending" | "HighRiskProhibited"
        | "ImpactAssessmentComplete" | "ImpactAssessmentRequired"
        | "LateNotice" | "MonitoringActive" | "MonitoringLapsed"
        | "NoTransferMechanism" | "NotApplicable" | "NotFiled" | "NotListed"
        | "NotRegistered" | "NotRestricted" | "NotSatisfied"
        | "NotarizedFiled" | "NotarizedMissing" | "NotarizedPending"
        | "OriginatorInfoComplete" | "OriginatorInfoMissing"
        | "Overdue" | "Paid"
        | "PepClear" | "PepIdentified" | "PepIdentifiedEddComplete"
        | "PepIdentifiedEddFailed" | "PepIdentifiedEddPending" | "PepNotIdentified"
        | "ProfessionalObligationMet" | "ProfessionalObligationNotMet"
        | "PromotionApproved" | "PromotionUnapproved"
        | "PscChangeOverdue" | "PscRegisterCurrent" | "PscRegisterMissing"
        | "RbeCompliant" | "RbeNonCompliant" | "RbePending"
        | "RcsNotRegistered" | "RcsPending" | "RcsRegistered"
        | "RecordsCurrent" | "RecordsExpired"
        | "RegisterCurrent" | "RegisterMissing"
        | "RepatriationApproved" | "RepatriationDenied" | "RepatriationPending"
        | "Restricted" | "RestrictionPeriodExpired"
        | "RetentionCompliant" | "RetentionNonCompliant"
        | "Revoked" | "Satisfied"
        | "SarFiled" | "SarNotFiled" | "SarPending"
        | "SecpNotRegistered" | "SecpPending" | "SecpRegistered"
        | "Segregated" | "SegregationPending"
        | "SezApproved" | "SezNotApproved" | "SezPending"
        | "ShellBankDetected"
        | "SifcApproved" | "SifcNotApproved" | "SifcPending"
        | "StrFiledWithFiu" | "StrFiledWithNca" | "StrNotRequired"
        | "StrPendingFiling" | "Suspended"
        | "TaxExempt" | "TaxNotRegistered" | "TaxRegistered"
        | "TransferMechanismInPlace" | "UnderReview" => Some(Status),

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
        "fca_authorization_status" | "fsra_authorization_status"
        | "fsra_permission_status" | "fsc_license_status"
        | "csp_license_status" | "fund_license_status"
        | "vasp_license_status" | "securities_dealer_license_status"
        | "sfc_licence_status" | "cms_licence_status"
        | "cima_registration_status" | "listing_venue_status" => {
            Some(&[LicenseType, Status])
        }

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
        "accounting_records_retention_status" | "aml_record_keeping_status"
        | "data_retention_status" => Some(&[Status, TimePeriod]),

        // ── Registration status accessors (status only) ─────────────
        "acra_registration_status" | "cr_registration_status"
        | "dp_registration_status" | "rcs_registration_status"
        | "secp_registration_status" | "tax_registration_status" => Some(&[Status]),

        // ── Pure status accessors (the large group) ─────────────────
        "agm_status" | "aml_compliance_officer_status"
        | "annual_accounts_filing_status" | "annual_license_fee_status"
        | "annual_return_filing_status" | "approved_individuals_status"
        | "approved_persons_status" | "audit_status"
        | "beneficial_owners" | "beneficial_ownership_register_status"
        | "breach_notification_status" | "capital_adequacy_status"
        | "cdd_status" | "charter_registration_status"
        | "client_money_status" | "cnic_verification_status"
        | "company_secretary" | "conduct_of_business_status"
        | "confirmation_statement_filing_status" | "confirmation_statement_status"
        | "correspondent_banking_status"
        | "cross_border_transfer_status" | "custodian_status"
        | "data_processor_agreement_status" | "data_protection_status"
        | "data_subject_consent_status"
        | "disclosure_completeness_status" | "dispute_resolution_status"
        | "dpia_status" | "economic_substance_status"
        | "edd_status" | "employment_agreement_status"
        | "employment_standards_status"
        | "financial_promotion_status" | "fit_and_proper_status"
        | "fund_administrator_status" | "fund_auditor_status"
        | "kyc_aml_status"
        | "memorandum_filing_status" | "minimum_capital_status"
        | "notarization_status" | "ongoing_monitoring_status"
        | "pep_screening_status" | "professional_obligation_status"
        | "prospectus_filing_status" | "psc_register_status"
        | "rbe_status" | "registered_agent"
        | "registered_agent_change_notice_status"
        | "repatriation_status" | "resale_restriction_status"
        | "sar_status" | "sez_status"
        | "sifc_approval_status"
        | "significant_controllers_register_status"
        | "str_filing_status" | "str_filing_to_crf_status"
        | "systems_controls_status"
        | "wire_transfer_compliance_status" => Some(&[Status]),

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
    "IncorporationContext",
    "NonCompliant",
    "Pending",
    "SanctionsResult",
    "accounting_records_retention_status",
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
    "employment_agreement_status",
    "employment_standards_status",
    "entity_type",
    "fca_authorization_status",
    "financial_promotion_status",
    "fit_and_proper_status",
    "fsa_administrator_exemption",
    "fsra_authorization_required",
    "fsra_authorization_status",
    "fsra_permission_status",
    "fsc_license_status",
    "fund_administrator_status",
    "fund_auditor_status",
    "fund_class",
    "fund_license_status",
    "high_risk_jurisdiction_counterparty",
    "holds_client_assets",
    "incorporator_identified",
    "insider_trading_flag",
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
    "offering_exemption_status",
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
    "resale_restriction_status",
    "sanctions_check",
    "sar_status",
    "secp_registration_status",
    "securities_dealer_license_status",
    "sez_status",
    "sfc_licence_status",
    "share_form",
    "shareholder_count",
    "sifc_approval_status",
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
    "Filed",
    "FitAndProperFailed",
    "FitAndProperSatisfied",
    "FitAndProperUnderReview",
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
        || NAT_CONSTRUCTORS.contains(&name)
        || SANCTIONS_CONSTRUCTORS.contains(&name)
        || TAG_CONSTRUCTORS.contains(&name)
}

/// Returns `true` if `name` is one of the core prelude types
/// (`ComplianceVerdict`, `ComplianceTag`, `Bool`, `Nat`, `SanctionsResult`,
/// `IncorporationContext`).
pub fn is_prelude_type(name: &str) -> bool {
    CORE_TYPES.contains(&name)
}

/// Registry mapping prelude datatypes to their variant constructors.
///
/// Used by the admissibility checker to verify that every constructor in a
/// `Match` expression belongs to the scrutinee's datatype and that the set
/// of constructors covers the datatype (either exhaustively or via a
/// wildcard branch).
pub struct PreludeRegistry;

impl PreludeRegistry {
    /// Return the full constructor list for a named prelude datatype, or
    /// `None` if `datatype_name` is not a known prelude type.
    ///
    /// `ComplianceTag` is finite but very large (hundreds of TAG_CONSTRUCTORS);
    /// it is returned in full so exhaustive-coverage checks can decide
    /// whether a `Match` covers the entire tag set or requires a wildcard.
    pub fn lookup_variant_constructors(datatype_name: &str) -> Option<Vec<&'static str>> {
        match datatype_name {
            "ComplianceVerdict" => Some(VERDICT_CONSTRUCTORS.to_vec()),
            "Bool" => Some(BOOL_CONSTRUCTORS.to_vec()),
            "Nat" => Some(NAT_CONSTRUCTORS.to_vec()),
            "SanctionsResult" => Some(SANCTIONS_CONSTRUCTORS.to_vec()),
            "ComplianceTag" => Some(TAG_CONSTRUCTORS.to_vec()),
            _ => None,
        }
    }

    /// Given a prelude constructor name, return the datatype it belongs to
    /// (e.g. `"Compliant" -> Some("ComplianceVerdict")`). Returns `None` for
    /// names that are not prelude constructors.
    pub fn constructor_datatype(ctor_name: &str) -> Option<&'static str> {
        if VERDICT_CONSTRUCTORS.contains(&ctor_name) {
            Some("ComplianceVerdict")
        } else if BOOL_CONSTRUCTORS.contains(&ctor_name) {
            Some("Bool")
        } else if NAT_CONSTRUCTORS.contains(&ctor_name) {
            Some("Nat")
        } else if SANCTIONS_CONSTRUCTORS.contains(&ctor_name) {
            Some("SanctionsResult")
        } else if TAG_CONSTRUCTORS.contains(&ctor_name) {
            Some("ComplianceTag")
        } else {
            None
        }
    }
}

/// Build the compliance prelude as a typechecker context with a global
/// constant signature.
pub fn compliance_prelude() -> Context {
    let mut ctx = Context::empty();
    let type0_term = type0();

    ctx = register_all(ctx, CORE_TYPES, &type0_term);
    ctx = register_all(ctx, VERDICT_CONSTRUCTORS, &constant("ComplianceVerdict"));
    ctx = register_all(ctx, BOOL_CONSTRUCTORS, &constant("Bool"));
    ctx = register_all(ctx, NAT_CONSTRUCTORS, &constant("Nat"));
    ctx = register_all(ctx, SANCTIONS_CONSTRUCTORS, &constant("SanctionsResult"));
    ctx = register_all(ctx, TAG_CONSTRUCTORS, &constant("ComplianceTag"));

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

    ctx = register_unary_accessors(ctx, NAT_ACCESSORS, "Nat");
    ctx = register_unary_accessors(ctx, BOOL_ACCESSORS, "Bool");
    ctx = register_unary_accessors(ctx, SANCTIONS_ACCESSORS, "SanctionsResult");
    ctx = register_unary_accessors(ctx, TAG_ACCESSORS, "ComplianceTag");

    ctx
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typecheck::{check, infer};

    #[test]
    fn prelude_covers_all_rule_symbols() {
        let ctx = compliance_prelude();

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
        let ctx = compliance_prelude();
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
        let ctx = compliance_prelude();
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
        let ctx = compliance_prelude();

        assert_eq!(ctx.global_len(), 363);
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
        assert!(validate_match_family("fca_authorization_status", "FcaAuthorized"));
        assert!(validate_match_family("fca_authorization_status", "FcaApplied"));
        assert!(validate_match_family("fca_authorization_status", "Revoked"));
        assert!(validate_match_family("fca_authorization_status", "Suspended"));
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
}
