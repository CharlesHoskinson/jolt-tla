//! Reproduction bundle for debugging conformance mismatches.

use super::runner::OracleOutput;
use std::path::Path;

/// A bundle of information for reproducing a conformance mismatch.
#[derive(Debug)]
pub struct ReproBundle {
    /// Test name that failed.
    pub test_name: String,
    /// Operation that was being tested (e.g., "state_digest").
    pub operation: String,
    /// Program hash (formatted for display).
    pub program_hash: String,
    /// State (formatted for display).
    pub state: String,
    /// Rust output.
    pub rust_output: OracleOutput,
    /// Lean output.
    pub lean_output: OracleOutput,
}

impl ReproBundle {
    /// Create a new repro bundle.
    pub fn new(
        test_name: String,
        operation: String,
        program_hash: String,
        state: String,
        rust_output: OracleOutput,
        lean_output: OracleOutput,
    ) -> Self {
        Self {
            test_name,
            operation,
            program_hash,
            state,
            rust_output,
            lean_output,
        }
    }

    /// Format as a human-readable report.
    pub fn to_report(&self) -> String {
        format!(
            r#"=== Conformance Mismatch Report ===
Test: {}
Operation: {}
Program Hash: {}
State: {}

Rust Output: {:?}
Lean Output: {:?}

To reproduce:
  1. Run Rust: cargo test {} -- --nocapture
  2. Run Lean: lake exe oracle {} <input.json>
"#,
            self.test_name,
            self.operation,
            self.program_hash,
            self.state,
            self.rust_output,
            self.lean_output,
            self.test_name,
            self.operation,
        )
    }

    /// Save the repro bundle to a file.
    pub fn save<P: AsRef<Path>>(&self, path: P) -> std::io::Result<()> {
        std::fs::write(path, self.to_report())
    }

    /// Format as JSON for machine parsing.
    pub fn to_json(&self) -> String {
        format!(
            r#"{{"test_name":"{}","operation":"{}","program_hash":"{}","rust_output":"{}","lean_output":"{}"}}"#,
            escape_json(&self.test_name),
            escape_json(&self.operation),
            escape_json(&self.program_hash),
            escape_json(self.rust_output.as_string()),
            escape_json(self.lean_output.as_string()),
        )
    }
}

/// Escape a string for JSON output.
fn escape_json(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_repro_bundle_report() {
        let bundle = ReproBundle::new(
            "test_basic".to_string(),
            "state_digest".to_string(),
            "0x00...00".to_string(),
            "VMStateV1 { pc: 0, ... }".to_string(),
            OracleOutput::Ok("12345".to_string()),
            OracleOutput::Ok("67890".to_string()),
        );

        let report = bundle.to_report();
        assert!(report.contains("test_basic"));
        assert!(report.contains("state_digest"));
        assert!(report.contains("Rust Output"));
        assert!(report.contains("Lean Output"));
    }

    #[test]
    fn test_repro_bundle_json() {
        let bundle = ReproBundle::new(
            "test".to_string(),
            "digest".to_string(),
            "hash".to_string(),
            "state".to_string(),
            OracleOutput::Ok("123".to_string()),
            OracleOutput::Err("E404".to_string()),
        );

        let json = bundle.to_json();
        assert!(json.contains("\"test_name\":\"test\""));
        assert!(json.contains("\"rust_output\":\"123\""));
        assert!(json.contains("\"lean_output\":\"E404\""));
    }
}
