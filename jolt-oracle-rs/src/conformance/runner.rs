//! Oracle runner implementations for differential testing.

use super::{ConformanceError, ConformanceResult};
use crate::field::Fr;
use crate::state::{compute_state_digest, Bytes32, VMStateV1};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Result from an oracle computation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OracleOutput {
    /// Successful computation with decimal string result.
    Ok(String),
    /// Error with code name.
    Err(String),
}

impl OracleOutput {
    /// Check if this is an Ok result.
    pub fn is_ok(&self) -> bool {
        matches!(self, Self::Ok(_))
    }

    /// Check if this is an Err result.
    pub fn is_err(&self) -> bool {
        matches!(self, Self::Err(_))
    }

    /// Get the value as a string (either ok value or error name).
    pub fn as_string(&self) -> &str {
        match self {
            Self::Ok(s) => s,
            Self::Err(s) => s,
        }
    }
}

/// Trait for oracle runners that can compute state digests.
pub trait OracleRunner {
    /// Compute state digest and return result as a string.
    fn compute_digest(
        &self,
        program_hash: &Bytes32,
        state: &VMStateV1,
    ) -> ConformanceResult<OracleOutput>;

    /// Get the runner name for reporting.
    fn name(&self) -> &str;
}

/// Rust implementation runner.
pub struct RustDigestRunner;

impl RustDigestRunner {
    /// Create a new Rust runner.
    pub fn new() -> Self {
        Self
    }
}

impl Default for RustDigestRunner {
    fn default() -> Self {
        Self::new()
    }
}

impl OracleRunner for RustDigestRunner {
    fn compute_digest(
        &self,
        program_hash: &Bytes32,
        state: &VMStateV1,
    ) -> ConformanceResult<OracleOutput> {
        match compute_state_digest(program_hash, state) {
            Ok(digest) => {
                let decimal = fr_to_decimal(&digest);
                Ok(OracleOutput::Ok(decimal))
            }
            Err(e) => {
                // Extract error name from debug representation
                let error_name = format!("{:?}", e);
                // Get just the variant name (before any parentheses)
                let name = error_name
                    .split('(')
                    .next()
                    .unwrap_or(&error_name)
                    .to_string();
                Ok(OracleOutput::Err(name))
            }
        }
    }

    fn name(&self) -> &str {
        "Rust"
    }
}

/// Lean oracle subprocess runner.
pub struct LeanDigestRunner {
    /// Path to the jolt_oracle directory.
    project_path: PathBuf,
    /// Path to the oracle executable.
    oracle_path: PathBuf,
}

impl LeanDigestRunner {
    /// Create a new Lean runner.
    ///
    /// # Arguments
    /// * `project_path` - Path to the jolt_oracle directory
    pub fn new<P: AsRef<Path>>(project_path: P) -> ConformanceResult<Self> {
        let project_path = project_path.as_ref().to_path_buf();

        // Determine oracle executable path
        let oracle_path = if cfg!(windows) {
            project_path.join(".lake/build/bin/oracle.exe")
        } else {
            project_path.join(".lake/build/bin/oracle")
        };

        if !oracle_path.exists() {
            return Err(ConformanceError::LeanNotAvailable(format!(
                "Oracle not found at {:?}. Run 'lake build' in jolt_oracle first.",
                oracle_path
            )));
        }

        Ok(Self {
            project_path,
            oracle_path,
        })
    }

    /// Check if the Lean oracle is available.
    pub fn is_available(&self) -> bool {
        self.oracle_path.exists()
    }

    /// Create a temporary JSON file for the digest input.
    fn create_input_file(
        &self,
        program_hash: &Bytes32,
        state: &VMStateV1,
    ) -> ConformanceResult<tempfile::NamedTempFile> {
        let mut file = tempfile::NamedTempFile::with_suffix(".json")
            .map_err(|e| ConformanceError::IoError(e.to_string()))?;

        let json = format_state_json(program_hash, state);
        file.write_all(json.as_bytes())
            .map_err(|e| ConformanceError::IoError(e.to_string()))?;
        file.flush()
            .map_err(|e| ConformanceError::IoError(e.to_string()))?;

        Ok(file)
    }

    /// Parse the JSON output from the Lean oracle.
    fn parse_output(
        &self,
        stdout: &str,
        stderr: &str,
        success: bool,
    ) -> ConformanceResult<OracleOutput> {
        // Check for error in stderr or stdout
        if !success || stdout.contains("\"error\"") || stdout.contains("\"status\": \"INVALID\"") {
            // Extract error code from JSON (handles both "error":"..." and "error": "...")
            if let Some(code) = extract_json_string(stdout, "\"error\":") {
                return Ok(OracleOutput::Err(code));
            }
            if let Some(code) = extract_json_string(stderr, "\"error\":") {
                return Ok(OracleOutput::Err(code));
            }
            // Fall back to stderr content
            if !stderr.is_empty() {
                return Ok(OracleOutput::Err(stderr.trim().to_string()));
            }
            return Err(ConformanceError::LeanOutputParseError(
                "Unknown error format".to_string(),
            ));
        }

        // Extract digest from JSON output (handles both "digest":"..." and "digest": "...")
        if let Some(digest) = extract_json_string(stdout, "\"digest\":") {
            return Ok(OracleOutput::Ok(digest));
        }

        Err(ConformanceError::LeanOutputParseError(format!(
            "Could not parse digest from: {}",
            stdout
        )))
    }
}

impl OracleRunner for LeanDigestRunner {
    fn compute_digest(
        &self,
        program_hash: &Bytes32,
        state: &VMStateV1,
    ) -> ConformanceResult<OracleOutput> {
        // Create temporary input file
        let input_file = self.create_input_file(program_hash, state)?;

        // Run the oracle
        let output = Command::new(&self.oracle_path)
            .args(["digest", "--format=json"])
            .arg(input_file.path())
            .current_dir(&self.project_path)
            .output()
            .map_err(|e| ConformanceError::LeanExecutionFailed(e.to_string()))?;

        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();

        self.parse_output(&stdout, &stderr, output.status.success())
    }

    fn name(&self) -> &str {
        "Lean"
    }
}

/// Format VMStateV1 as JSON for the Lean oracle.
fn format_state_json(program_hash: &Bytes32, state: &VMStateV1) -> String {
    let regs_json: Vec<String> = state.regs.iter().map(|r| r.to_string()).collect();

    let config_tags_json: Vec<String> = state
        .config_tags
        .iter()
        .map(|tag| {
            format!(
                "{{\"name\":\"0x{}\",\"value\":\"0x{}\"}}",
                hex::encode(&tag.name),
                hex::encode(&tag.value)
            )
        })
        .collect();

    format!(
        r#"{{"program_hash":"0x{}","state":{{"pc":{},"regs":[{}],"step_counter":{},"rw_mem_root":"0x{}","io_root":"0x{}","halted":{},"exit_code":{},"config_tags":[{}]}}}}"#,
        program_hash.to_hex(),
        state.pc,
        regs_json.join(","),
        state.step_counter,
        state.rw_mem_root.to_hex(),
        state.io_root.to_hex(),
        state.halted,
        state.exit_code,
        config_tags_json.join(",")
    )
}

/// Extract a string value from JSON after a key.
fn extract_json_string(s: &str, key_prefix: &str) -> Option<String> {
    let start = s.find(key_prefix)? + key_prefix.len();
    let remaining = &s[start..];
    // Skip optional whitespace after the colon
    let remaining = remaining.trim_start();
    // Must start with a quote
    if !remaining.starts_with('"') {
        return None;
    }
    let remaining = &remaining[1..]; // skip opening quote
    let end = remaining.find('"')?;
    Some(remaining[..end].to_string())
}

/// Convert Fr to decimal string.
fn fr_to_decimal(fr: &Fr) -> String {
    // Convert Fr bytes (little-endian) to big integer
    let bytes = fr.to_bytes_le();
    let mut result = vec![0u8];

    for &byte in bytes.iter().rev() {
        // Multiply result by 256 and add byte
        let mut carry = byte as u16;
        for digit in result.iter_mut() {
            let val = (*digit as u16) * 256 + carry;
            *digit = (val % 10) as u8;
            carry = val / 10;
        }
        while carry > 0 {
            result.push((carry % 10) as u8);
            carry /= 10;
        }
    }

    // Convert digits to string (reverse order)
    if result.iter().all(|&d| d == 0) {
        "0".to_string()
    } else {
        result
            .iter()
            .rev()
            .skip_while(|&&d| d == 0)
            .map(|&d| (b'0' + d) as char)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rust_runner_basic() {
        let runner = RustDigestRunner::new();
        let program_hash = Bytes32::zero();
        let state = VMStateV1::default();

        let result = runner.compute_digest(&program_hash, &state);
        assert!(result.is_ok());

        let output = result.unwrap();
        assert!(output.is_ok());
    }

    #[test]
    fn test_rust_runner_invalid_state() {
        let runner = RustDigestRunner::new();
        let program_hash = Bytes32::zero();
        let mut state = VMStateV1::default();
        state.regs[0] = 1; // Invalid: x0 must be 0

        let result = runner.compute_digest(&program_hash, &state);
        assert!(result.is_ok());

        let output = result.unwrap();
        assert!(output.is_err());
        assert!(output.as_string().contains("E407"));
    }

    #[test]
    fn test_format_state_json() {
        let program_hash = Bytes32::zero();
        let state = VMStateV1::default();

        let json = format_state_json(&program_hash, &state);

        assert!(json.contains("\"program_hash\":\"0x"));
        assert!(json.contains("\"pc\":0"));
        assert!(json.contains("\"regs\":["));
        assert!(json.contains("\"step_counter\":0"));
        assert!(json.contains("\"halted\":0"));
    }

    #[test]
    fn test_extract_json_string() {
        // Without space after colon
        let json = r#"{"digest":"12345"}"#;
        let result = extract_json_string(json, "\"digest\":");
        assert_eq!(result, Some("12345".to_string()));

        // With space after colon (Lean style)
        let json_with_space = r#"{"digest": "12345"}"#;
        let result = extract_json_string(json_with_space, "\"digest\":");
        assert_eq!(result, Some("12345".to_string()));

        // Error without space
        let error_json = r#"{"error":"E404_InvalidHalted"}"#;
        let result = extract_json_string(error_json, "\"error\":");
        assert_eq!(result, Some("E404_InvalidHalted".to_string()));

        // Error with space (Lean style)
        let error_json_space = r#"{"error": "E404_InvalidHalted"}"#;
        let result = extract_json_string(error_json_space, "\"error\":");
        assert_eq!(result, Some("E404_InvalidHalted".to_string()));
    }
}
