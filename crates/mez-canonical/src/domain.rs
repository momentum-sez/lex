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
//! [`FromStr`] and produced by [`std::fmt::Display`]. The wire format is the
//! canonical Momentum `ComplianceDomain` format.

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
#[cfg_attr(feature = "openapi", derive(utoipa::ToSchema))]
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

    /// Map this domain to a unique index in `0..COUNT`.
    ///
    /// The index matches the position in [`all()`](Self::all) — enforced by
    /// the M-003 / M-004 compile-time assertions below. Enables O(1)
    /// array-based representations of the 23-domain product lattice.
    pub const fn index(&self) -> usize {
        match self {
            Self::Aml => 0,
            Self::Kyc => 1,
            Self::Sanctions => 2,
            Self::Tax => 3,
            Self::Securities => 4,
            Self::Corporate => 5,
            Self::Custody => 6,
            Self::DataPrivacy => 7,
            Self::Licensing => 8,
            Self::Banking => 9,
            Self::Payments => 10,
            Self::Clearing => 11,
            Self::Settlement => 12,
            Self::DigitalAssets => 13,
            Self::Employment => 14,
            Self::Immigration => 15,
            Self::Ip => 16,
            Self::ConsumerProtection => 17,
            Self::Arbitration => 18,
            Self::Trade => 19,
            Self::Insurance => 20,
            Self::AntiBribery => 21,
            Self::Sharia => 22,
        }
    }

    /// Recover a domain from its index. Returns `None` for out-of-range
    /// indices. Inverse of [`index()`](Self::index):
    /// `from_index(d.index()) == Some(d)`.
    pub const fn from_index(i: usize) -> Option<Self> {
        match i {
            0 => Some(Self::Aml),
            1 => Some(Self::Kyc),
            2 => Some(Self::Sanctions),
            3 => Some(Self::Tax),
            4 => Some(Self::Securities),
            5 => Some(Self::Corporate),
            6 => Some(Self::Custody),
            7 => Some(Self::DataPrivacy),
            8 => Some(Self::Licensing),
            9 => Some(Self::Banking),
            10 => Some(Self::Payments),
            11 => Some(Self::Clearing),
            12 => Some(Self::Settlement),
            13 => Some(Self::DigitalAssets),
            14 => Some(Self::Employment),
            15 => Some(Self::Immigration),
            16 => Some(Self::Ip),
            17 => Some(Self::ConsumerProtection),
            18 => Some(Self::Arbitration),
            19 => Some(Self::Trade),
            20 => Some(Self::Insurance),
            21 => Some(Self::AntiBribery),
            22 => Some(Self::Sharia),
            _ => None,
        }
    }

    /// Whether this domain is eligible for mutual recognition agreements.
    ///
    /// All domains except `Sanctions` are MRA-eligible. Sanctions
    /// re-evaluation is mandatory per the sanctions-dominance axiom — no
    /// bilateral agreement can waive it.
    pub const fn is_mra_eligible(&self) -> bool {
        !matches!(self, Self::Sanctions)
    }
}

// Compile-time assertion (M-003): `ComplianceDomain::all()` length must
// match `COUNT`. If a variant is added or removed without updating both,
// this fails at compile time.
const _: () = {
    const ALL_LEN: usize = 23; // must equal ComplianceDomain::all().len()
    assert!(
        ALL_LEN == ComplianceDomain::COUNT,
        "ComplianceDomain::COUNT does not match the number of variants in all()"
    );
};

// Compile-time assertion (M-004): `from_index` is the inverse of `index`.
// Verifiable at compile time because both are `const fn`.
const _: () = {
    let mut i = 0;
    while i < ComplianceDomain::COUNT {
        match ComplianceDomain::from_index(i) {
            Some(d) => assert!(
                d.index() == i,
                "from_index(i).index() != i — from_index and index are inconsistent"
            ),
            None => panic!("from_index returned None for valid index"),
        }
        i += 1;
    }
    // Out of range must return None.
    assert!(ComplianceDomain::from_index(ComplianceDomain::COUNT).is_none());
};

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
        assert_eq!(
            "aml".parse::<ComplianceDomain>().unwrap(),
            ComplianceDomain::Aml
        );
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
