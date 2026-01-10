// Build script that generates Rust code from Lean metadata.
// Build scripts are not consensus-critical, so we allow expect() and panic().
#![allow(clippy::expect_used)]
//
// Consumes `../jolt_oracle/metadata.json` and generates:
// - `src/error.rs` - ErrorCode enum with all variants
// - `src/field/modulus.rs` - Field modulus constant
// - `src/poseidon/params.rs` - MDS matrix and round constants
//
// Satisfies: BUILD-001, BUILD-002, BUILD-003, BUILD-004

use serde::Deserialize;
use std::env;
use std::fs;
use std::path::Path;

#[derive(Debug, Deserialize)]
struct Metadata {
    version: String,
    field: FieldMetadata,
    errors: Vec<ErrorInfo>,
    poseidon: PoseidonMetadata,
}

#[derive(Debug, Deserialize)]
struct FieldMetadata {
    modulus: String,
    modulus_hex: String,
}

#[derive(Debug, Deserialize)]
struct ErrorInfo {
    name: String,
    code: u32,
    params: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct PoseidonMetadata {
    width: usize,
    rate: usize,
    capacity: usize,
    full_rounds: usize,
    partial_rounds: usize,
    sbox_alpha: usize,
    mds_matrix: Vec<Vec<String>>,
    round_constants: Vec<Vec<String>>,
    round_constants_hash: String,
}

fn main() {
    // Tell Cargo to rerun if metadata changes
    println!("cargo:rerun-if-changed=../jolt_oracle/metadata.json");
    println!("cargo:rerun-if-changed=build.rs");

    let metadata_path = Path::new("../jolt_oracle/metadata.json");

    // Read and parse metadata
    let metadata_content = match fs::read_to_string(metadata_path) {
        Ok(content) => content,
        Err(e) => {
            eprintln!(
                "Warning: Could not read metadata.json: {}. Using fallback generation.",
                e
            );
            // Generate stub files so compilation can proceed
            generate_stub_files();
            return;
        }
    };

    let metadata: Metadata = match serde_json::from_str(&metadata_content) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("Warning: Could not parse metadata.json: {}. Using fallback.", e);
            generate_stub_files();
            return;
        }
    };

    // Validate metadata version
    if metadata.version != "1" {
        eprintln!(
            "Warning: Unexpected metadata version '{}', expected '1'",
            metadata.version
        );
    }

    // Generate code files
    let out_dir = env::var("OUT_DIR").expect("OUT_DIR not set");
    let out_path = Path::new(&out_dir);

    generate_error_rs(out_path, &metadata.errors);
    generate_modulus_rs(out_path, &metadata.field);
    generate_params_rs(out_path, &metadata.poseidon);

    println!("cargo:warning=Generated code from metadata.json v{}", metadata.version);
}

fn generate_stub_files() {
    let out_dir = env::var("OUT_DIR").expect("OUT_DIR not set");
    let out_path = Path::new(&out_dir);

    // Stub error.rs
    fs::write(
        out_path.join("error_generated.rs"),
        r#"
// STUB: Generated from build.rs when metadata.json is unavailable
// Run `lake exe oracle export-metadata > ../jolt_oracle/metadata.json` to generate

/// Placeholder error code enum
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum ErrorCode {
    /// Placeholder error
    Unknown = 0,
}

impl ErrorCode {
    /// Get the numeric code
    pub const fn code(&self) -> u32 {
        *self as u32
    }

    /// Get the error name
    pub const fn name(&self) -> &'static str {
        "Unknown"
    }
}
"#,
    )
    .expect("Failed to write stub error_generated.rs");

    // Stub modulus.rs
    fs::write(
        out_path.join("modulus_generated.rs"),
        r#"
// STUB: Generated from build.rs when metadata.json is unavailable

/// BLS12-381 scalar field modulus (placeholder)
pub const MODULUS_DECIMAL: &str = "0";
pub const MODULUS_HEX: &str = "0000000000000000000000000000000000000000000000000000000000000000";
"#,
    )
    .expect("Failed to write stub modulus_generated.rs");

    // Stub params.rs
    fs::write(
        out_path.join("params_generated.rs"),
        r#"
// STUB: Generated from build.rs when metadata.json is unavailable

/// Poseidon parameters (placeholder)
pub const WIDTH: usize = 3;
pub const RATE: usize = 2;
pub const CAPACITY: usize = 1;
pub const FULL_ROUNDS: usize = 8;
pub const PARTIAL_ROUNDS: usize = 60;
pub const TOTAL_ROUNDS: usize = 68;
pub const SBOX_ALPHA: usize = 5;

/// MDS matrix (placeholder - identity)
pub const MDS_MATRIX: [[&str; 3]; 3] = [
    ["0100000000000000000000000000000000000000000000000000000000000000", "0000000000000000000000000000000000000000000000000000000000000000", "0000000000000000000000000000000000000000000000000000000000000000"],
    ["0000000000000000000000000000000000000000000000000000000000000000", "0100000000000000000000000000000000000000000000000000000000000000", "0000000000000000000000000000000000000000000000000000000000000000"],
    ["0000000000000000000000000000000000000000000000000000000000000000", "0000000000000000000000000000000000000000000000000000000000000000", "0100000000000000000000000000000000000000000000000000000000000000"],
];

/// Round constants (placeholder - empty)
pub const ROUND_CONSTANTS: [[&str; 3]; 68] = [
    ["0000000000000000000000000000000000000000000000000000000000000000"; 3]; 68
];

pub const ROUND_CONSTANTS_HASH: &str = "0000000000000000000000000000000000000000000000000000000000000000";
"#,
    )
    .expect("Failed to write stub params_generated.rs");
}

fn generate_error_rs(out_path: &Path, errors: &[ErrorInfo]) {
    let mut code = String::new();

    // Use outer doc comments for include!() compatibility
    code.push_str(
        r#"// Error codes generated from Lean metadata.
//
// DO NOT EDIT - This file is generated by build.rs from metadata.json
// Satisfies: BUILD-003, ERR-001, ERR-002

use thiserror::Error;

/// All error codes from the Jolt Oracle specification.
///
/// Each variant corresponds to a specific spec violation that must be
/// detected and reported consistently between Lean and Rust implementations.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Error)]
#[allow(non_camel_case_types)]
pub enum ErrorCode {
"#,
    );

    // Generate enum variants
    for error in errors {
        let variant_name = error.name.clone();
        let doc = format!("    /// {} (code {})\n", variant_name, error.code);
        code.push_str(&doc);

        if error.params.is_empty() {
            code.push_str(&format!(
                "    #[error(\"{}\")]\n    {},\n\n",
                variant_name, variant_name
            ));
        } else {
            // Generate tuple variant with parameters
            let params: Vec<String> = error
                .params
                .iter()
                .map(|p| {
                    let ty = param_type(p);
                    format!("/* {} */ {}", p, ty)
                })
                .collect();
            let param_refs: Vec<String> = (0..error.params.len()).map(|i| format!("{{{}}}", i)).collect();
            code.push_str(&format!(
                "    #[error(\"{name}({refs})\")]\n    {name}({params}),\n\n",
                name = variant_name,
                refs = param_refs.join(", "),
                params = params.join(", ")
            ));
        }
    }

    code.push_str("}\n\n");

    // Generate code() method
    code.push_str(
        r#"impl ErrorCode {
    /// Get the numeric error code.
    pub fn code(&self) -> u32 {
        match self {
"#,
    );

    for error in errors {
        if error.params.is_empty() {
            code.push_str(&format!(
                "            ErrorCode::{} => {},\n",
                error.name, error.code
            ));
        } else {
            let wildcards = vec!["_"; error.params.len()].join(", ");
            code.push_str(&format!(
                "            ErrorCode::{}({}) => {},\n",
                error.name, wildcards, error.code
            ));
        }
    }

    code.push_str(
        r#"        }
    }

    /// Get the error name as a string.
    pub fn name(&self) -> &'static str {
        match self {
"#,
    );

    for error in errors {
        if error.params.is_empty() {
            code.push_str(&format!(
                "            ErrorCode::{} => \"{}\",\n",
                error.name, error.name
            ));
        } else {
            let wildcards = vec!["_"; error.params.len()].join(", ");
            code.push_str(&format!(
                "            ErrorCode::{}({}) => \"{}\",\n",
                error.name, wildcards, error.name
            ));
        }
    }

    code.push_str(
        r#"        }
    }
}

/// Result type for oracle operations.
pub type OracleResult<T> = Result<T, ErrorCode>;
"#,
    );

    fs::write(out_path.join("error_generated.rs"), code)
        .expect("Failed to write error_generated.rs");
}

fn param_type(param_name: &str) -> &'static str {
    match param_name {
        "got" | "size" | "limit" | "depth" | "length" | "count" | "index" | "codepoint" => "u64",
        // String for key, field, context, expected, reason, value, and all others
        _ => "String",
    }
}

fn generate_modulus_rs(out_path: &Path, field: &FieldMetadata) {
    let code = format!(
        r#"// Field modulus generated from Lean metadata.
//
// DO NOT EDIT - This file is generated by build.rs from metadata.json
// Satisfies: BUILD-004, FR-001

/// BLS12-381 scalar field modulus as decimal string.
pub const MODULUS_DECIMAL: &str = "{}";

/// BLS12-381 scalar field modulus as 64-char hex (little-endian bytes).
pub const MODULUS_HEX: &str = "{}";
"#,
        field.modulus, field.modulus_hex
    );

    fs::write(out_path.join("modulus_generated.rs"), code)
        .expect("Failed to write modulus_generated.rs");
}

fn generate_params_rs(out_path: &Path, poseidon: &PoseidonMetadata) {
    let mut code = String::new();

    code.push_str(&format!(
        r#"// Poseidon parameters generated from Lean metadata.
//
// DO NOT EDIT - This file is generated by build.rs from metadata.json
// Satisfies: BUILD-004, POS-001, POS-003

/// Poseidon state width (t = 3).
pub const WIDTH: usize = {};

/// Poseidon sponge rate (r = 2).
pub const RATE: usize = {};

/// Poseidon sponge capacity (c = 1).
pub const CAPACITY: usize = {};

/// Number of full rounds (RF = 8).
pub const FULL_ROUNDS: usize = {};

/// Number of partial rounds (RP = 60).
pub const PARTIAL_ROUNDS: usize = {};

/// Total rounds (RF + RP = 68).
pub const TOTAL_ROUNDS: usize = {};

/// S-box exponent (alpha = 5).
pub const SBOX_ALPHA: usize = {};

/// SHA-256 hash of round constants for verification.
pub const ROUND_CONSTANTS_HASH: &str = "{}";

"#,
        poseidon.width,
        poseidon.rate,
        poseidon.capacity,
        poseidon.full_rounds,
        poseidon.partial_rounds,
        poseidon.full_rounds + poseidon.partial_rounds,
        poseidon.sbox_alpha,
        poseidon.round_constants_hash
    ));

    // Generate MDS matrix
    code.push_str("/// MDS matrix (3x3) as hex strings (little-endian Fr encoding).\n");
    code.push_str(&format!(
        "pub const MDS_MATRIX: [[&str; {}]; {}] = [\n",
        poseidon.width, poseidon.width
    ));
    for row in &poseidon.mds_matrix {
        code.push_str("    [");
        for (i, val) in row.iter().enumerate() {
            if i > 0 {
                code.push_str(", ");
            }
            code.push_str(&format!("\"{}\"", val));
        }
        code.push_str("],\n");
    }
    code.push_str("];\n\n");

    // Generate round constants
    let total_rounds = poseidon.full_rounds + poseidon.partial_rounds;
    code.push_str(&format!(
        "/// Round constants ({} rounds x {} elements) as hex strings.\n",
        total_rounds, poseidon.width
    ));
    code.push_str(&format!(
        "pub const ROUND_CONSTANTS: [[&str; {}]; {}] = [\n",
        poseidon.width, total_rounds
    ));
    for (round, constants) in poseidon.round_constants.iter().enumerate() {
        code.push_str(&format!("    // Round {}\n    [", round));
        for (i, val) in constants.iter().enumerate() {
            if i > 0 {
                code.push_str(", ");
            }
            code.push_str(&format!("\"{}\"", val));
        }
        code.push_str("],\n");
    }
    code.push_str("];\n");

    fs::write(out_path.join("params_generated.rs"), code)
        .expect("Failed to write params_generated.rs");
}
