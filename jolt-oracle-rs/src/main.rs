//! Jolt Oracle CLI.
//!
//! Command-line interface matching the Lean oracle for drop-in replacement.

use clap::{Parser, Subcommand};
use jolt_oracle::state::{Bytes32, VMStateV1};
use jolt_oracle::{compute_state_digest, ErrorCode, Fr};
use serde::{Deserialize, Serialize};
use std::fs;
use std::io::{self, Read};
use std::path::PathBuf;
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

    /// Compute state digest from JSON input
    Digest {
        /// Path to JSON file (use - for stdin)
        #[arg(default_value = "-")]
        path: String,
    },

    /// Verify state digest matches expected value
    Verify {
        /// Path to JSON file (use - for stdin)
        #[arg(default_value = "-")]
        path: String,
    },

    /// Generate test vector from input file
    Generate {
        /// Vector type (state_digest)
        vector_type: String,
        /// Path to input JSON file
        path: String,
        /// Optional output file path
        #[arg(short, long)]
        output: Option<String>,
    },
}

/// Input format for the digest command.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct DigestInput {
    /// Program hash (32-byte hex string)
    program_hash: Bytes32,
    /// VM state
    state: VMStateV1,
}

/// Input format for the verify command.
#[derive(Debug, Deserialize)]
struct VerifyInput {
    /// Program hash (32-byte hex string)
    program_hash: Bytes32,
    /// VM state
    state: VMStateV1,
    /// Expected digest (decimal string)
    expected_digest: String,
}

/// Output format for successful digest computation.
#[derive(Debug, Serialize)]
struct DigestOutput {
    /// Status indicator
    ok: DigestOk,
}

#[derive(Debug, Serialize)]
struct DigestOk {
    /// Computed digest as decimal string
    digest: String,
}

/// Output format for successful verification.
#[derive(Debug, Serialize)]
struct VerifyOutput {
    /// Status indicator
    ok: VerifyOk,
}

#[derive(Debug, Serialize)]
struct VerifyOk {
    /// Whether the digest matched
    valid: bool,
    /// Computed digest as decimal string
    computed_digest: String,
    /// Expected digest as decimal string
    expected_digest: String,
}

/// Output format for errors.
#[derive(Debug, Serialize)]
struct ErrorOutput {
    /// Error details
    err: ErrorDetails,
}

#[derive(Debug, Serialize)]
struct ErrorDetails {
    /// Numeric error code
    code: u32,
    /// Error name
    name: String,
    /// Human-readable message
    message: String,
}

/// Output format for the generate command.
#[derive(Debug, Serialize)]
struct GenerateOutput {
    /// List of test vectors
    vectors: Vec<TestVector>,
}

/// A single test vector.
#[derive(Debug, Serialize)]
struct TestVector {
    /// Name of the test (derived from filename)
    name: String,
    /// Type of vector (e.g., "state_digest")
    #[serde(rename = "type")]
    vector_type: String,
    /// Input data
    input: DigestInput,
    /// Expected result (decimal string for digests)
    expected: String,
}

/// Error output for generate command.
#[derive(Debug, Serialize)]
struct GenerateErrorOutput {
    /// Status indicator
    status: String,
    /// Error code
    error: String,
    /// Error message
    message: String,
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
        Some(Commands::Digest { path }) => run_digest(&path),
        Some(Commands::Verify { path }) => run_verify(&path),
        Some(Commands::Generate {
            vector_type,
            path,
            output,
        }) => run_generate(&vector_type, &path, output.as_deref()),
        None => {
            println!("Jolt Oracle v0.1.0");
            println!("Use --help for usage information");
            ExitCode::SUCCESS
        }
    }
}

fn run_digest(path: &str) -> ExitCode {
    // Read input
    let input_json = match read_input(path) {
        Ok(s) => s,
        Err(e) => {
            output_error(
                ErrorCode::E100_InvalidJSON,
                &format!("Failed to read input: {}", e),
            );
            return ExitCode::FAILURE;
        }
    };

    // Parse input JSON
    let input: DigestInput = match serde_json::from_str(&input_json) {
        Ok(i) => i,
        Err(e) => {
            output_error(ErrorCode::E100_InvalidJSON, &format!("Invalid JSON: {}", e));
            return ExitCode::FAILURE;
        }
    };

    // Compute digest
    match compute_state_digest(&input.program_hash, &input.state) {
        Ok(digest) => {
            let output = DigestOutput {
                ok: DigestOk {
                    digest: digest.to_string(),
                },
            };
            match serde_json::to_string(&output) {
                Ok(json) => {
                    println!("{}", json);
                    ExitCode::SUCCESS
                }
                Err(_) => {
                    output_error(ErrorCode::E100_InvalidJSON, "Failed to serialize output");
                    ExitCode::FAILURE
                }
            }
        }
        Err(e) => {
            output_error(e.clone(), &e.to_string());
            ExitCode::FAILURE
        }
    }
}

fn run_verify(path: &str) -> ExitCode {
    // Read input
    let input_json = match read_input(path) {
        Ok(s) => s,
        Err(e) => {
            output_error(
                ErrorCode::E100_InvalidJSON,
                &format!("Failed to read input: {}", e),
            );
            return ExitCode::FAILURE;
        }
    };

    // Parse input JSON
    let input: VerifyInput = match serde_json::from_str(&input_json) {
        Ok(i) => i,
        Err(e) => {
            output_error(ErrorCode::E100_InvalidJSON, &format!("Invalid JSON: {}", e));
            return ExitCode::FAILURE;
        }
    };

    // Compute digest
    let computed_digest = match compute_state_digest(&input.program_hash, &input.state) {
        Ok(digest) => digest,
        Err(e) => {
            output_error(e.clone(), &e.to_string());
            return ExitCode::FAILURE;
        }
    };

    // Parse expected digest
    let expected_digest = match parse_decimal_fr(&input.expected_digest) {
        Ok(d) => d,
        Err(e) => {
            output_error(e.clone(), &format!("Invalid expected_digest: {}", e));
            return ExitCode::FAILURE;
        }
    };

    // Compare digests
    let valid = computed_digest == expected_digest;

    let output = VerifyOutput {
        ok: VerifyOk {
            valid,
            computed_digest: computed_digest.to_string(),
            expected_digest: expected_digest.to_string(),
        },
    };

    match serde_json::to_string(&output) {
        Ok(json) => {
            println!("{}", json);
            if valid {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            }
        }
        Err(_) => {
            output_error(ErrorCode::E100_InvalidJSON, "Failed to serialize output");
            ExitCode::FAILURE
        }
    }
}

/// Parse a decimal string into an Fr element.
fn parse_decimal_fr(s: &str) -> Result<Fr, ErrorCode> {
    // Parse decimal string to bytes
    let s = s.trim();
    if s.is_empty() {
        return Err(ErrorCode::E100_InvalidJSON);
    }

    // Convert decimal string to little-endian bytes
    let bytes = decimal_to_le_bytes(s)?;

    // Create Fr from bytes
    let mut arr = [0u8; 32];
    let len = bytes.len().min(32);
    arr[..len].copy_from_slice(&bytes[..len]);

    Fr::from_bytes_le(&arr)
}

/// Convert a decimal string to little-endian bytes (up to 32 bytes).
fn decimal_to_le_bytes(s: &str) -> Result<Vec<u8>, ErrorCode> {
    // Validate input is all digits
    if !s.chars().all(|c| c.is_ascii_digit()) {
        return Err(ErrorCode::E100_InvalidJSON);
    }

    // Handle zero case
    if s == "0" {
        return Ok(vec![0u8; 32]);
    }

    // Convert decimal to big integer using repeated multiplication
    let mut result = vec![0u8; 32];

    for ch in s.chars() {
        let digit = (ch as u8) - b'0';

        // Multiply result by 10
        let mut carry: u16 = 0;
        for byte in result.iter_mut() {
            let product = (*byte as u16) * 10 + carry;
            *byte = (product & 0xFF) as u8;
            carry = product >> 8;
        }

        // Add digit
        let mut add_carry: u16 = digit as u16;
        for byte in result.iter_mut() {
            let sum = (*byte as u16) + add_carry;
            *byte = (sum & 0xFF) as u8;
            add_carry = sum >> 8;
            if add_carry == 0 {
                break;
            }
        }
    }

    Ok(result)
}

fn read_input(path: &str) -> io::Result<String> {
    if path == "-" {
        let mut buffer = String::new();
        io::stdin().read_to_string(&mut buffer)?;
        Ok(buffer)
    } else {
        let path = PathBuf::from(path);
        fs::read_to_string(path)
    }
}

fn output_error(code: ErrorCode, message: &str) {
    let output = ErrorOutput {
        err: ErrorDetails {
            code: code.code(),
            name: code.name().to_string(),
            message: message.to_string(),
        },
    };
    if let Ok(json) = serde_json::to_string(&output) {
        println!("{}", json);
    } else {
        eprintln!("Error: {}", message);
    }
}

fn run_generate(vector_type: &str, path: &str, output_path: Option<&str>) -> ExitCode {
    // Validate vector type
    if vector_type != "state_digest" {
        let err = GenerateErrorOutput {
            status: "ERROR".to_string(),
            error: "E106_UnexpectedType".to_string(),
            message: format!(
                "Unknown vector type: {}. Supported: state_digest",
                vector_type
            ),
        };
        if let Ok(json) = serde_json::to_string(&err) {
            println!("{}", json);
        }
        return ExitCode::FAILURE;
    }

    // Read input file
    let input_json = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            let err = GenerateErrorOutput {
                status: "ERROR".to_string(),
                error: "E900_FileNotFound".to_string(),
                message: format!("Cannot read file: {}: {}", path, e),
            };
            if let Ok(json) = serde_json::to_string(&err) {
                println!("{}", json);
            }
            return ExitCode::FAILURE;
        }
    };

    // Parse input JSON
    let input: DigestInput = match serde_json::from_str(&input_json) {
        Ok(i) => i,
        Err(e) => {
            let err = GenerateErrorOutput {
                status: "ERROR".to_string(),
                error: "E100_InvalidJSON".to_string(),
                message: format!("Invalid JSON: {}", e),
            };
            if let Ok(json) = serde_json::to_string(&err) {
                println!("{}", json);
            }
            return ExitCode::FAILURE;
        }
    };

    // Compute digest
    let digest = match compute_state_digest(&input.program_hash, &input.state) {
        Ok(d) => d,
        Err(e) => {
            let err = GenerateErrorOutput {
                status: "ERROR".to_string(),
                error: e.name().to_string(),
                message: e.to_string(),
            };
            if let Ok(json) = serde_json::to_string(&err) {
                println!("{}", json);
            }
            return ExitCode::FAILURE;
        }
    };

    // Extract base name from file path
    let name = extract_base_name(path);

    // Build test vector output
    let vector = TestVector {
        name,
        vector_type: "state_digest".to_string(),
        input,
        expected: digest.to_string(),
    };

    let output = GenerateOutput {
        vectors: vec![vector],
    };

    let json = match serde_json::to_string(&output) {
        Ok(j) => j,
        Err(_) => {
            let err = GenerateErrorOutput {
                status: "ERROR".to_string(),
                error: "E100_InvalidJSON".to_string(),
                message: "Failed to serialize output".to_string(),
            };
            if let Ok(json) = serde_json::to_string(&err) {
                println!("{}", json);
            }
            return ExitCode::FAILURE;
        }
    };

    // Write to file or stdout
    match output_path {
        Some(out_path) => match fs::write(out_path, format!("{}\n", json)) {
            Ok(_) => {
                println!("Generated test vector written to: {}", out_path);
                ExitCode::SUCCESS
            }
            Err(e) => {
                eprintln!("Error: Cannot write to file: {}: {}", out_path, e);
                ExitCode::FAILURE
            }
        },
        None => {
            println!("{}", json);
            ExitCode::SUCCESS
        }
    }
}

/// Extract the base name (without extension) from a file path.
fn extract_base_name(path: &str) -> String {
    // Handle both forward and backslashes
    let path = path.replace('\\', "/");
    let file_name = path.rsplit('/').next().unwrap_or(&path);

    // Remove extension
    if let Some(dot_pos) = file_name.rfind('.') {
        file_name[..dot_pos].to_string()
    } else {
        file_name.to_string()
    }
}
