//! # Compliance Domains — Single Source of Truth
//!
//! Defines the [`ComplianceDomain`] enum with all 23 variants. The Rust
//! compiler enforces exhaustive `match` — adding a new domain forces every
//! handler in the entire codebase to address it.
//!
//! ## Canonical Wire Format
//!
//! Each variant serializes to a lowercase `snake_case` string (`"aml"`,
//! `"data_privacy"`, `"anti_bribery"`, …). The same strings are accepted by
//! [`FromStr`] and produced by [`std::fmt::Display`]. This enum is byte-
//! compatible with the kernel tree's `mez_core::ComplianceDomain`.

use serde::{Deserialize, Serialize};
use std::fmt;
use std::str::FromStr;

/// A compliance domain representing a regulatory category that can be
/// evaluated by the Compliance Tensor.
///
/// All 23 domains are included. Every `match` on this enum must be
/// exhaustive — the compiler enforces that no domain is accidentally
/// ignored.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ComplianceDomain {
    /// Anti-money laundering (transaction monitoring, suspicious activity).
    Aml,
    /// Know Your Customer (identity verification, due diligence).
    Kyc,
    /// Sanctions screening (OFAC, UN, EU lists).
    Sanctions,
    /// Tax compliance (withholding, reporting, filing).
    Tax,
    /// Securities regulation (issuance, trading, disclosure).
    Securities,
    /// Corporate governance (formation, dissolution, beneficial ownership).
    Corporate,
    /// Custody requirements (asset safekeeping, segregation).
    Custody,
    /// Data privacy (GDPR, PDPA, cross-border data transfer).
    DataPrivacy,
    /// Licensing (business license validity, professional certifications).
    Licensing,
    /// Banking regulation (reserve requirements, capital adequacy).
    Banking,
    /// Payment services (PSP licensing, payment instrument rules).
    Payments,
    /// Clearing and settlement (CCP rules, netting, finality).
    Clearing,
    /// Settlement finality (delivery-versus-payment, settlement cycles).
    Settlement,
    /// Digital asset regulation (token classification, exchange licensing).
    DigitalAssets,
    /// Employment law (labor contracts, social security, withholding).
    Employment,
    /// Immigration (work permits, visa sponsorship, residency).
    Immigration,
    /// Intellectual property (patent, trademark, trade secret).
    Ip,
    /// Consumer protection (disclosure, dispute resolution, warranties).
    ConsumerProtection,
    /// Arbitration (dispute resolution frameworks, enforcement).
    Arbitration,
    /// Trade regulation (import/export controls, customs, tariffs).
    Trade,
    /// Insurance regulation (Solvency II, NAIC, Lloyd's, reinsurance).
    Insurance,
    /// Anti-bribery and corruption (FCPA, UK Bribery Act, UNCAC).
    AntiBribery,
    /// Sharia compliance (Islamic finance: riba, gharar, maysir, asset
    /// backing, SSB certification).
    Sharia,
}

impl ComplianceDomain {
    /// Number of compliance domains.
    pub const COUNT: usize = 23;

    /// Return all compliance domains as a slice.
    pub fn all() -> &'static [ComplianceDomain] {
        &[
            Self::Aml,
            Self::Kyc,
            Self::Sanctions,
            Self::Tax,
            Self::Securities,
            Self::Corporate,
            Self::Custody,
            Self::DataPrivacy,
            Self::Licensing,
            Self::Banking,
            Self::Payments,
            Self::Clearing,
            Self::Settlement,
            Self::DigitalAssets,
            Self::Employment,
            Self::Immigration,
            Self::Ip,
            Self::ConsumerProtection,
            Self::Arbitration,
            Self::Trade,
            Self::Insurance,
            Self::AntiBribery,
            Self::Sharia,
        ]
    }

    /// Return the `snake_case` string representation of this domain.
    ///
    /// Matches the serde serialization format and the inverse of [`FromStr`].
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Aml => "aml",
            Self::Kyc => "kyc",
            Self::Sanctions => "sanctions",
            Self::Tax => "tax",
            Self::Securities => "securities",
            Self::Corporate => "corporate",
            Self::Custody => "custody",
            Self::DataPrivacy => "data_privacy",
            Self::Licensing => "licensing",
            Self::Banking => "banking",
            Self::Payments => "payments",
            Self::Clearing => "clearing",
            Self::Settlement => "settlement",
            Self::DigitalAssets => "digital_assets",
            Self::Employment => "employment",
            Self::Immigration => "immigration",
            Self::Ip => "ip",
            Self::ConsumerProtection => "consumer_protection",
            Self::Arbitration => "arbitration",
            Self::Trade => "trade",
            Self::Insurance => "insurance",
            Self::AntiBribery => "anti_bribery",
            Self::Sharia => "sharia",
        }
    }
}

impl fmt::Display for ComplianceDomain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl FromStr for ComplianceDomain {
    type Err = String;

    /// Parse a compliance domain from its snake_case string representation.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "aml" => Ok(Self::Aml),
            "kyc" => Ok(Self::Kyc),
            "sanctions" => Ok(Self::Sanctions),
            "tax" => Ok(Self::Tax),
            "securities" => Ok(Self::Securities),
            "corporate" => Ok(Self::Corporate),
            "custody" => Ok(Self::Custody),
            "data_privacy" => Ok(Self::DataPrivacy),
            "licensing" => Ok(Self::Licensing),
            "banking" => Ok(Self::Banking),
            "payments" => Ok(Self::Payments),
            "clearing" => Ok(Self::Clearing),
            "settlement" => Ok(Self::Settlement),
            "digital_assets" => Ok(Self::DigitalAssets),
            "employment" => Ok(Self::Employment),
            "immigration" => Ok(Self::Immigration),
            "ip" => Ok(Self::Ip),
            "consumer_protection" => Ok(Self::ConsumerProtection),
            "arbitration" => Ok(Self::Arbitration),
            "trade" => Ok(Self::Trade),
            "insurance" => Ok(Self::Insurance),
            "anti_bribery" => Ok(Self::AntiBribery),
            "sharia" => Ok(Self::Sharia),
            other => Err(format!("unknown compliance domain: \"{other}\"")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_returns_23_domains() {
        assert_eq!(ComplianceDomain::all().len(), ComplianceDomain::COUNT);
        assert_eq!(ComplianceDomain::all().len(), 23);
    }

    #[test]
    fn all_domains_are_unique() {
        let domains = ComplianceDomain::all();
        let unique: std::collections::HashSet<_> = domains.iter().collect();
        assert_eq!(unique.len(), domains.len());
    }

    #[test]
    fn display_roundtrip_via_from_str() {
        for domain in ComplianceDomain::all() {
            let s = domain.to_string();
            let parsed: ComplianceDomain = s.parse().unwrap();
            assert_eq!(*domain, parsed);
        }
    }

    #[test]
    fn from_str_rejects_unknown() {
        assert!("unknown_domain".parse::<ComplianceDomain>().is_err());
        assert!("".parse::<ComplianceDomain>().is_err());
        assert!("AML".parse::<ComplianceDomain>().is_err()); // case-sensitive
    }

    #[test]
    fn serde_roundtrip() {
        for domain in ComplianceDomain::all() {
            let json = serde_json::to_string(domain).unwrap();
            let deserialized: ComplianceDomain = serde_json::from_str(&json).unwrap();
            assert_eq!(*domain, deserialized);
        }
    }

    #[test]
    fn as_str_matches_serde_wire_format() {
        for domain in ComplianceDomain::all() {
            let as_str = domain.as_str();
            let serde_json_value = serde_json::to_value(domain).unwrap();
            assert_eq!(serde_json_value.as_str().unwrap(), as_str);
        }
    }

    #[test]
    fn as_str_is_lowercase_snake_case() {
        for domain in ComplianceDomain::all() {
            let s = domain.as_str();
            assert!(
                s.chars().all(|c| c.is_ascii_lowercase() || c == '_'),
                "{s} is not lowercase snake_case"
            );
        }
    }

    #[test]
    fn specific_variants_round_trip() {
        assert_eq!("aml".parse::<ComplianceDomain>().unwrap(), ComplianceDomain::Aml);
        assert_eq!(
            "data_privacy".parse::<ComplianceDomain>().unwrap(),
            ComplianceDomain::DataPrivacy
        );
        assert_eq!(
            "anti_bribery".parse::<ComplianceDomain>().unwrap(),
            ComplianceDomain::AntiBribery
        );
        assert_eq!(
            "sharia".parse::<ComplianceDomain>().unwrap(),
            ComplianceDomain::Sharia
        );
    }

    #[test]
    fn domain_count_invariant() {
        // If this count changes, every match must be re-audited for exhaustiveness.
        assert_eq!(ComplianceDomain::all().len(), 23);
    }
}
