//! lex-cli - Command-line Lex fiber authoring.
//!
//! Implemented:
//! - `lex check <file.lex>` - lex, parse, and admissibility-check a fiber.
//! - `lex parse <file.lex>` - parse and print the AST (pretty or JSON).
//! - `lex elaborate <file.lex>` - surface → core elaboration.
//! - `lex sign <file.lex> --key <key>` - content-address a fiber and attach a
//!   keyed authenticator, producing a self-contained signed bundle.
//! - `lex verify <file.lex.signed>` - recompute the digest and re-check the
//!   authenticator on a signed bundle.
//!
//! Not yet implemented (return a clear error, never a fake success):
//! - `lex check-principles <file>` - the principle-DAG acyclicity check needs a
//!   surface syntax for principle-priority edges that the parser does not yet
//!   produce. See the `CheckPrinciples` arm.
//!
//! Authentication mechanism. `sign`/`verify` operate over the SHA-256 content
//! digest of the canonical source. The authenticator is a keyed HMAC-SHA256
//! over that digest, computed with the key file's bytes as the HMAC key, using
//! only the SHA-256 primitive `lex-core` already depends on. This is a
//! **symmetric** authenticator: it proves integrity and authenticity to a
//! holder of the same key. It is **not** an Ed25519 public-key signature, so
//! it does not provide air-gapped *public* verifiability where the verifier
//! holds only a public key. Public-key signing is a follow-on (see the `Sign`
//! arm) that requires adding a signature dependency to the workspace.
//!
//! Run with no arguments to see a brief orientation and a pointer to the
//! end-to-end `hello-lex` example.

use std::fs;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const ORIENTATION: &str = concat!(
    "lex - a logic for jurisdictional rules.\n",
    "\n",
    "Lex expresses legal rules as typed programs. Defeasibility, temporal\n",
    "stratification, authority-relative interpretation, and typed discretion\n",
    "holes are primitives of the calculus.\n",
    "\n",
    "Run the end-to-end example (builds a rule, type-checks, extracts\n",
    "obligations, discharges them, issues a signed certificate, and shows a\n",
    "typed discretion hole):\n",
    "\n",
    "    cargo run --example hello-lex -p lex-core\n",
    "\n",
    "Read the 5-minute walk-through at docs/getting-started.md.\n",
    "Read the canonical paper at https://research.momentum.inc/papers/lex.\n",
    "\n",
    "Subcommands:\n",
    "    lex check <file.lex>            Lex, parse, and admissibility-check a fiber\n",
    "    lex parse <file.lex>            Parse and print the AST (pretty | json)\n",
    "    lex elaborate <file.lex>        Surface → core elaboration\n",
    "    lex sign <file.lex> --key <k>   Content-address + keyed-HMAC a fiber bundle\n",
    "    lex verify <file.lex.signed>    Recheck a signed fiber bundle's digest + HMAC\n",
    "    lex check-principles <file>    (not yet implemented)\n",
    "\n",
    "Pass --help after any subcommand for its flags.\n",
);

#[derive(Parser)]
#[command(name = "lex")]
#[command(about = "Lex: A Logic for Jurisdictional Rules - CLI")]
#[command(version)]
#[command(long_about = ORIENTATION)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    /// Type-check a Lex fiber file.
    Check {
        /// Path to the .lex file.
        file: String,
        /// Print verbose diagnostics.
        #[arg(long)]
        verbose: bool,
    },
    /// Parse a Lex file and print the AST.
    Parse {
        /// Path to the .lex file.
        file: String,
        /// Output format: json or pretty.
        #[arg(long, default_value = "pretty")]
        format: String,
    },
    /// Elaborate surface Lex to core Lex.
    Elaborate {
        /// Path to the .lex file.
        file: String,
        /// Output the core Lex to a file.
        #[arg(long)]
        output: Option<String>,
    },
    /// Sign a fiber for air-gapped submission.
    Sign {
        /// Path to the .lex file to sign.
        file: String,
        /// Path to the signing key (Ed25519 secret key file).
        #[arg(long)]
        key: String,
        /// Output path for the signed bundle.
        #[arg(long)]
        output: Option<String>,
    },
    /// Verify a signed fiber bundle.
    Verify {
        /// Path to the signed fiber bundle.
        file: String,
    },
    /// Check the principle conflict DAG for acyclicity.
    CheckPrinciples {
        /// Path to the jurisdiction's principle priority file.
        file: String,
    },
}

/// Bundle format emitted by `lex sign` and consumed by `lex verify`.
///
/// Self-contained: it carries the original source so the verifier can
/// recompute the content digest and the authenticator without the original
/// `.lex` file. `format_version` lets the format evolve (e.g. a future
/// Ed25519-signed bundle) without silently misreading old bundles.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct SignedFiber {
    /// Bundle format version.
    format_version: u32,
    /// The original Lex source text.
    source: String,
    /// Lowercase hex SHA-256 of `source` (content address).
    content_digest: String,
    /// Authenticator scheme identifier. Currently `"hmac-sha256"`.
    scheme: String,
    /// Lowercase hex HMAC-SHA256 over `content_digest`, keyed by the key file.
    authenticator: String,
}

const BUNDLE_FORMAT_VERSION: u32 = 1;
const BUNDLE_SCHEME: &str = "hmac-sha256";

/// Errors surfaced by the CLI. Every command that cannot complete returns one
/// of these — none of them is a fake-success path.
#[derive(Debug)]
enum CliError {
    /// A file could not be read or written.
    Io { path: String, source: std::io::Error },
    /// Lexing failed.
    Lex(String),
    /// Parsing failed.
    Parse(String),
    /// Admissibility checking failed.
    TypeCheck(String),
    /// Elaboration failed.
    Elaborate(String),
    /// (De)serialization of a signed bundle failed.
    Bundle(String),
    /// A signed bundle was tampered with (digest or authenticator mismatch).
    VerificationFailed(String),
    /// The command is recognized but not yet implemented. Distinct from a
    /// silent stub: it is an error, surfaced loudly, never a success.
    NotImplemented(String),
}

impl std::fmt::Display for CliError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CliError::Io { path, source } => write!(f, "i/o error on `{path}`: {source}"),
            CliError::Lex(msg) => write!(f, "lex error: {msg}"),
            CliError::Parse(msg) => write!(f, "parse error: {msg}"),
            CliError::TypeCheck(msg) => write!(f, "admissibility error: {msg}"),
            CliError::Elaborate(msg) => write!(f, "elaboration error: {msg}"),
            CliError::Bundle(msg) => write!(f, "signed-bundle error: {msg}"),
            CliError::VerificationFailed(msg) => write!(f, "verification failed: {msg}"),
            CliError::NotImplemented(msg) => write!(f, "not implemented: {msg}"),
        }
    }
}

impl std::error::Error for CliError {}

fn read_source(path: &str) -> Result<String, CliError> {
    fs::read_to_string(path).map_err(|source| CliError::Io {
        path: path.to_string(),
        source,
    })
}

/// Lex + parse a source string into a Core Lex `Term`.
fn parse_source(source: &str) -> Result<lex_core::ast::Term, CliError> {
    let tokens = lex_core::lexer::lex(source).map_err(|e| CliError::Lex(e.to_string()))?;
    lex_core::parser::parse(&tokens).map_err(|e| CliError::Parse(e.to_string()))
}

/// Lowercase hex SHA-256 of a byte slice.
fn sha256_hex(data: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(data);
    let digest = hasher.finalize();
    let mut out = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write as _;
        let _ = write!(out, "{byte:02x}");
    }
    out
}

/// HMAC-SHA256(key, message) as defined by RFC 2104, built on the `sha2`
/// primitive (no extra dependency). Block size for SHA-256 is 64 bytes.
fn hmac_sha256(key: &[u8], message: &[u8]) -> [u8; 32] {
    const BLOCK: usize = 64;

    // Keys longer than the block size are first hashed.
    let mut key_block = [0u8; BLOCK];
    if key.len() > BLOCK {
        let mut hasher = Sha256::new();
        hasher.update(key);
        let hashed = hasher.finalize();
        key_block[..32].copy_from_slice(&hashed);
    } else {
        key_block[..key.len()].copy_from_slice(key);
    }

    let mut ipad = [0x36u8; BLOCK];
    let mut opad = [0x5cu8; BLOCK];
    for i in 0..BLOCK {
        ipad[i] ^= key_block[i];
        opad[i] ^= key_block[i];
    }

    let mut inner = Sha256::new();
    inner.update(ipad);
    inner.update(message);
    let inner_digest = inner.finalize();

    let mut outer = Sha256::new();
    outer.update(opad);
    outer.update(inner_digest);
    let outer_digest = outer.finalize();

    let mut out = [0u8; 32];
    out.copy_from_slice(&outer_digest);
    out
}

/// Constant-time equality over two byte slices. Avoids leaking how many
/// leading bytes of a forged authenticator matched.
fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}

/// Decode a lowercase/uppercase hex string into bytes.
fn hex_decode(hex: &str) -> Result<Vec<u8>, CliError> {
    if !hex.len().is_multiple_of(2) {
        return Err(CliError::Bundle(
            "hex authenticator has odd length".to_string(),
        ));
    }
    let mut out = Vec::with_capacity(hex.len() / 2);
    let bytes = hex.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let hi = (bytes[i] as char)
            .to_digit(16)
            .ok_or_else(|| CliError::Bundle("non-hex character in authenticator".to_string()))?;
        let lo = (bytes[i + 1] as char)
            .to_digit(16)
            .ok_or_else(|| CliError::Bundle("non-hex character in authenticator".to_string()))?;
        out.push(((hi << 4) | lo) as u8);
        i += 2;
    }
    Ok(out)
}

fn cmd_check(file: &str, verbose: bool) -> Result<(), CliError> {
    let source = read_source(file)?;
    let term = parse_source(&source)?;
    if verbose {
        println!("Parsed AST:\n{}", lex_core::pretty::pretty_print(&term));
    }
    lex_core::typecheck::check_admissibility(&term)
        .map_err(|e| CliError::TypeCheck(e.to_string()))?;
    println!("OK: {file} is admissible.");
    Ok(())
}

fn cmd_parse(file: &str, format: &str) -> Result<(), CliError> {
    let source = read_source(file)?;
    let term = parse_source(&source)?;
    match format {
        "json" => {
            let json = serde_json::to_string_pretty(&term)
                .map_err(|e| CliError::Bundle(format!("AST serialization failed: {e}")))?;
            println!("{json}");
        }
        "pretty" => println!("{}", lex_core::pretty::pretty_print(&term)),
        other => {
            return Err(CliError::Parse(format!(
                "unknown --format `{other}` (expected `pretty` or `json`)"
            )));
        }
    }
    Ok(())
}

fn cmd_elaborate(file: &str, output: Option<&str>) -> Result<(), CliError> {
    let source = read_source(file)?;
    let term = parse_source(&source)?;
    let prelude = lex_core::prelude::compliance_prelude();
    let core = lex_core::elaborate::elaborate(&term, &prelude)
        .map_err(|e| CliError::Elaborate(e.to_string()))?;
    let rendered = lex_core::pretty::pretty_print(&core);
    match output {
        Some(out) => {
            fs::write(out, &rendered).map_err(|source| CliError::Io {
                path: out.to_string(),
                source,
            })?;
            println!("Elaborated core written to {out}.");
        }
        None => println!("{rendered}"),
    }
    Ok(())
}

fn cmd_sign(file: &str, key: &str, output: Option<&str>) -> Result<(), CliError> {
    let source = read_source(file)?;
    // A signed fiber must be a well-formed, admissible fiber; refuse to sign
    // something that does not even parse, so a bundle never certifies garbage.
    let term = parse_source(&source)?;
    lex_core::typecheck::check_admissibility(&term)
        .map_err(|e| CliError::TypeCheck(e.to_string()))?;

    let key_bytes = fs::read(key).map_err(|source| CliError::Io {
        path: key.to_string(),
        source,
    })?;
    if key_bytes.is_empty() {
        return Err(CliError::Bundle("key file is empty".to_string()));
    }

    let content_digest = sha256_hex(source.as_bytes());
    let authenticator = sha256_hex_of_bytes(&hmac_sha256(&key_bytes, content_digest.as_bytes()));

    let bundle = SignedFiber {
        format_version: BUNDLE_FORMAT_VERSION,
        source,
        content_digest,
        scheme: BUNDLE_SCHEME.to_string(),
        authenticator,
    };

    let serialized = serde_json::to_string_pretty(&bundle)
        .map_err(|e| CliError::Bundle(format!("bundle serialization failed: {e}")))?;

    let out_path = output
        .map(|o| o.to_string())
        .unwrap_or_else(|| format!("{file}.signed"));
    fs::write(&out_path, &serialized).map_err(|source| CliError::Io {
        path: out_path.clone(),
        source,
    })?;
    println!("Signed bundle written to {out_path}.");
    println!("  content digest: {}", bundle.content_digest);
    println!("  scheme        : {}", bundle.scheme);
    Ok(())
}

fn cmd_verify(file: &str) -> Result<(), CliError> {
    let raw = read_source(file)?;
    let bundle: SignedFiber = serde_json::from_str(&raw)
        .map_err(|e| CliError::Bundle(format!("could not parse signed bundle: {e}")))?;

    if bundle.format_version != BUNDLE_FORMAT_VERSION {
        return Err(CliError::Bundle(format!(
            "unsupported bundle format_version {} (this build understands {})",
            bundle.format_version, BUNDLE_FORMAT_VERSION
        )));
    }
    if bundle.scheme != BUNDLE_SCHEME {
        return Err(CliError::Bundle(format!(
            "unsupported authenticator scheme `{}` (this build understands `{}`)",
            bundle.scheme, BUNDLE_SCHEME
        )));
    }

    // 1. Recompute the content digest from the embedded source and confirm it
    //    matches the digest the bundle claims. Catches source tampering.
    let recomputed_digest = sha256_hex(bundle.source.as_bytes());
    if !constant_time_eq(
        recomputed_digest.as_bytes(),
        bundle.content_digest.as_bytes(),
    ) {
        return Err(CliError::VerificationFailed(format!(
            "content digest mismatch: bundle claims {}, source hashes to {}",
            bundle.content_digest, recomputed_digest
        )));
    }

    // 2. Recompute the HMAC over the digest with the verifier's key and
    //    constant-time-compare against the bundle's authenticator.
    let prompt = "verification requires the same key used to sign; \
                  pass it via the LEX_VERIFY_KEY environment variable \
                  (path to the key file)";
    let key_path = std::env::var("LEX_VERIFY_KEY")
        .map_err(|_| CliError::VerificationFailed(prompt.to_string()))?;
    let key_bytes = fs::read(&key_path).map_err(|source| CliError::Io {
        path: key_path.clone(),
        source,
    })?;
    let expected = hmac_sha256(&key_bytes, bundle.content_digest.as_bytes());
    let presented = hex_decode(&bundle.authenticator)?;
    if !constant_time_eq(&expected, &presented) {
        return Err(CliError::VerificationFailed(
            "authenticator mismatch (wrong key or tampered bundle)".to_string(),
        ));
    }

    // 3. The signed source must still be an admissible fiber.
    let term = parse_source(&bundle.source)?;
    lex_core::typecheck::check_admissibility(&term)
        .map_err(|e| CliError::TypeCheck(e.to_string()))?;

    println!("OK: {file} verified.");
    println!("  content digest: {}", bundle.content_digest);
    println!("  scheme        : {}", bundle.scheme);
    Ok(())
}

/// Hex-encode a 32-byte digest (helper for the HMAC output).
fn sha256_hex_of_bytes(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for byte in bytes {
        use std::fmt::Write as _;
        let _ = write!(out, "{byte:02x}");
    }
    out
}

fn run(command: Commands) -> Result<(), CliError> {
    match command {
        Commands::Check { file, verbose } => cmd_check(&file, verbose),
        Commands::Parse { file, format } => cmd_parse(&file, &format),
        Commands::Elaborate { file, output } => cmd_elaborate(&file, output.as_deref()),
        Commands::Sign { file, key, output } => cmd_sign(&file, &key, output.as_deref()),
        Commands::Verify { file } => cmd_verify(&file),
        Commands::CheckPrinciples { file } => Err(CliError::NotImplemented(format!(
            "`lex check-principles {file}`: the parser does not yet emit \
             principle-priority edges, so the acyclicity check \
             (lex_core::principles::check_acyclicity) has no input. This \
             command is a recognized follow-on, not a supported operation."
        ))),
    }
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    let command = match cli.command {
        Some(c) => c,
        None => {
            print!("{ORIENTATION}");
            return ExitCode::SUCCESS;
        }
    };

    match run(command) {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("error: {err}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hmac_sha256_matches_rfc4231_test_case_2() {
        // RFC 4231 Test Case 2: key = "Jefe", data = "what do ya want for
        // nothing?", expected HMAC-SHA256 is a published fixed vector. This
        // pins the hand-rolled HMAC construction to the standard.
        let mac = hmac_sha256(b"Jefe", b"what do ya want for nothing?");
        let expected =
            "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843";
        assert_eq!(sha256_hex_of_bytes(&mac), expected);
    }

    #[test]
    fn hmac_sha256_long_key_is_hashed_first() {
        // Key longer than the 64-byte block must be SHA-256'd first (RFC 2104).
        // We only assert determinism + that it differs from the short-key MAC,
        // which is enough to exercise the long-key branch.
        let long_key = vec![0xaau8; 131];
        let mac1 = hmac_sha256(&long_key, b"message");
        let mac2 = hmac_sha256(&long_key, b"message");
        assert_eq!(mac1, mac2, "HMAC must be deterministic");
        let short = hmac_sha256(b"aa", b"message");
        assert_ne!(mac1, short, "different keys must yield different MACs");
    }

    #[test]
    fn sha256_hex_is_64_lowercase_hex_chars() {
        let hex = sha256_hex(b"hello");
        assert_eq!(hex.len(), 64);
        assert!(hex.chars().all(|c| c.is_ascii_hexdigit() && !c.is_uppercase()));
        // Known SHA-256("hello").
        assert_eq!(
            hex,
            "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824"
        );
    }

    #[test]
    fn constant_time_eq_behaves_like_eq() {
        assert!(constant_time_eq(b"abc", b"abc"));
        assert!(!constant_time_eq(b"abc", b"abd"));
        assert!(!constant_time_eq(b"abc", b"ab"));
        assert!(constant_time_eq(b"", b""));
    }

    #[test]
    fn hex_decode_roundtrips_hmac_output() {
        let mac = hmac_sha256(b"k", b"m");
        let hex = sha256_hex_of_bytes(&mac);
        let decoded = hex_decode(&hex).expect("valid hex must decode");
        assert_eq!(decoded, mac.to_vec());
    }

    #[test]
    fn hex_decode_rejects_odd_length_and_non_hex() {
        assert!(hex_decode("abc").is_err());
        assert!(hex_decode("zz").is_err());
    }

    #[test]
    fn sign_then_verify_roundtrips_with_matching_key() {
        let dir = std::env::temp_dir();
        let stamp = format!(
            "{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        );
        let lex_path = dir.join(format!("lex_cli_test_src_{stamp}.lex"));
        let key_path = dir.join(format!("lex_cli_test_key_{stamp}.bin"));
        let bundle_path = dir.join(format!("lex_cli_test_bundle_{stamp}.signed"));

        // A minimal admissible fiber written in the surface syntax the parser
        // accepts (`lambda (binder : T) . body`). The bound variable body and
        // constant domain are both structurally admissible.
        let source = "lambda (ctx : T) . ctx";
        fs::write(&lex_path, source).unwrap();
        fs::write(&key_path, b"super-secret-key-material").unwrap();

        // Confirm the source parses + is admissible (guards the fixture).
        let term = parse_source(source).expect("fixture should parse");
        lex_core::typecheck::check_admissibility(&term).expect("fixture should be admissible");

        cmd_sign(
            lex_path.to_str().unwrap(),
            key_path.to_str().unwrap(),
            Some(bundle_path.to_str().unwrap()),
        )
        .expect("sign should succeed");

        // Verify needs the key via env var.
        std::env::set_var("LEX_VERIFY_KEY", &key_path);
        let ok = cmd_verify(bundle_path.to_str().unwrap());
        std::env::remove_var("LEX_VERIFY_KEY");
        ok.expect("verify with matching key should succeed");

        let _ = fs::remove_file(&lex_path);
        let _ = fs::remove_file(&key_path);
        let _ = fs::remove_file(&bundle_path);
    }

    #[test]
    fn verify_rejects_tampered_source() {
        let dir = std::env::temp_dir();
        let stamp = format!(
            "{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        );
        let key_path = dir.join(format!("lex_cli_tamper_key_{stamp}.bin"));
        let bundle_path = dir.join(format!("lex_cli_tamper_bundle_{stamp}.signed"));
        fs::write(&key_path, b"key-bytes").unwrap();

        // Hand-build a bundle whose claimed digest does not match its source.
        let bundle = SignedFiber {
            format_version: BUNDLE_FORMAT_VERSION,
            source: "lambda (ctx : T) . ctx".to_string(),
            content_digest: "00".repeat(32), // wrong digest
            scheme: BUNDLE_SCHEME.to_string(),
            authenticator: "ab".repeat(32),
        };
        fs::write(&bundle_path, serde_json::to_string(&bundle).unwrap()).unwrap();

        std::env::set_var("LEX_VERIFY_KEY", &key_path);
        let result = cmd_verify(bundle_path.to_str().unwrap());
        std::env::remove_var("LEX_VERIFY_KEY");

        assert!(
            matches!(result, Err(CliError::VerificationFailed(_))),
            "tampered source must fail verification, got {result:?}"
        );

        let _ = fs::remove_file(&key_path);
        let _ = fs::remove_file(&bundle_path);
    }

    #[test]
    fn verify_rejects_wrong_key() {
        let dir = std::env::temp_dir();
        let stamp = format!(
            "{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        );
        let lex_path = dir.join(format!("lex_cli_wrongkey_src_{stamp}.lex"));
        let sign_key = dir.join(format!("lex_cli_wrongkey_sign_{stamp}.bin"));
        let wrong_key = dir.join(format!("lex_cli_wrongkey_wrong_{stamp}.bin"));
        let bundle_path = dir.join(format!("lex_cli_wrongkey_bundle_{stamp}.signed"));

        fs::write(&lex_path, "lambda (ctx : T) . ctx").unwrap();
        fs::write(&sign_key, b"the-real-key").unwrap();
        fs::write(&wrong_key, b"a-different-key").unwrap();

        cmd_sign(
            lex_path.to_str().unwrap(),
            sign_key.to_str().unwrap(),
            Some(bundle_path.to_str().unwrap()),
        )
        .expect("sign should succeed");

        std::env::set_var("LEX_VERIFY_KEY", &wrong_key);
        let result = cmd_verify(bundle_path.to_str().unwrap());
        std::env::remove_var("LEX_VERIFY_KEY");

        assert!(
            matches!(result, Err(CliError::VerificationFailed(_))),
            "wrong key must fail verification, got {result:?}"
        );

        let _ = fs::remove_file(&lex_path);
        let _ = fs::remove_file(&sign_key);
        let _ = fs::remove_file(&wrong_key);
        let _ = fs::remove_file(&bundle_path);
    }

    #[test]
    fn check_principles_reports_not_implemented_not_fake_success() {
        let result = run(Commands::CheckPrinciples {
            file: "anything.lex".to_string(),
        });
        assert!(
            matches!(result, Err(CliError::NotImplemented(_))),
            "check-principles must return NotImplemented, got {result:?}"
        );
    }

    #[test]
    fn check_rejects_unparseable_source() {
        let dir = std::env::temp_dir();
        let stamp = format!(
            "{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        );
        let bad = dir.join(format!("lex_cli_bad_{stamp}.lex"));
        fs::write(&bad, "this is not (((valid lex").unwrap();
        let result = cmd_check(bad.to_str().unwrap(), false);
        assert!(
            matches!(result, Err(CliError::Lex(_)) | Err(CliError::Parse(_))),
            "garbage must fail check, got {result:?}"
        );
        let _ = fs::remove_file(&bad);
    }
}
