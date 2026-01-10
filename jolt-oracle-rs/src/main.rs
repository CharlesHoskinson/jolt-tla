//! Jolt Oracle CLI.
//!
//! Command-line interface matching the Lean oracle for drop-in replacement.

use clap::{Parser, Subcommand};
use std::process::ExitCode;

#[derive(Parser)]
#[command(name = "oracle")]
#[command(about = "Jolt Oracle - Rust implementation", long_about = None)]
#[command(version)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    /// Show version information
    Version,

    /// Export metadata JSON (for verification against Lean)
    ExportMetadata,

    // TODO: Add more commands in later phases
    // Digest { path: String },
    // Verify { path: String },
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    match cli.command {
        Some(Commands::Version) => {
            println!("Jolt Oracle v0.1.0");
            println!("Rust implementation");
            ExitCode::SUCCESS
        }
        Some(Commands::ExportMetadata) => {
            // TODO: Export metadata for comparison with Lean
            println!("{{\"status\": \"not_implemented\"}}");
            ExitCode::SUCCESS
        }
        None => {
            println!("Jolt Oracle v0.1.0");
            println!("Use --help for usage information");
            ExitCode::SUCCESS
        }
    }
}
