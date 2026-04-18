//! lex-cli — Command-line Lex fiber authoring for air-gapped environments.
//!
//! Supports:
//! - `lex check <file.lex>` — type-check a fiber
//! - `lex parse <file.lex>` — parse and pretty-print the AST
//! - `lex elaborate <file.lex>` — surface → core elaboration
//! - `lex sign <file.lex> --key <key>` — sign a fiber for air-gapped submission
//! - `lex verify <file.lex.signed>` — verify a signed fiber
//!
//! Air-gapped workflow: author on offline machine, `lex sign` with hardware key,
//! transfer signed fiber via USB, submit to kernel.
//!
//! Run with no arguments to see a brief orientation and a pointer to the
//! end-to-end `hello-lex` example.

use clap::{Parser, Subcommand};

const ORIENTATION: &str = concat!(
    "lex — a logic for jurisdictional rules.\n",
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
    "    lex check <file.lex>            Type-check a Lex fiber\n",
    "    lex parse <file.lex>            Parse and pretty-print the AST\n",
    "    lex elaborate <file.lex>        Surface → core elaboration\n",
    "    lex sign <file.lex> --key <k>   Sign a fiber for air-gapped submission\n",
    "    lex verify <file.lex.signed>    Verify a signed fiber\n",
    "    lex check-principles <file>    Check principle priority DAG acyclicity\n",
    "\n",
    "Pass --help after any subcommand for its flags.\n",
);

#[derive(Parser)]
#[command(name = "lex")]
#[command(about = "Lex: A Logic for Jurisdictional Rules — CLI")]
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

fn main() {
    let cli = Cli::parse();

    let command = match cli.command {
        Some(c) => c,
        None => {
            print!("{ORIENTATION}");
            return;
        }
    };

    match command {
        Commands::Check { file, verbose } => {
            println!("Type-checking: {file}");
            if verbose {
                println!("  (verbose mode)");
            }
            // TODO: Read file, parse, type-check using lex-core
            println!("  [not yet implemented — lex-core integration pending]");
        }
        Commands::Parse { file, format } => {
            println!("Parsing: {file} (format: {format})");
            // TODO: Read file, parse, output AST
            println!("  [not yet implemented]");
        }
        Commands::Elaborate { file, output } => {
            println!("Elaborating: {file}");
            if let Some(out) = output {
                println!("  Output: {out}");
            }
            // TODO: surface → core elaboration
            println!("  [not yet implemented]");
        }
        Commands::Sign { file, key, output } => {
            println!("Signing: {file} with key: {key}");
            if let Some(out) = output {
                println!("  Output: {out}");
            }
            // TODO: Read file, compute content hash, sign with Ed25519
            println!("  [not yet implemented — air-gapped signing pending]");
        }
        Commands::Verify { file } => {
            println!("Verifying: {file}");
            // TODO: Read signed bundle, verify signature
            println!("  [not yet implemented]");
        }
        Commands::CheckPrinciples { file } => {
            println!("Checking principle DAG: {file}");
            // TODO: Read principle priority edges, run check_acyclicity
            println!("  [not yet implemented]");
        }
    }
}
