//! LeanRunner - Subprocess backend for differential testing.
//!
//! Invokes the Lean oracle via subprocess and parses its output for
//! comparison with the Rust implementation.
//!
//! # Usage
//!
//! ```ignore
//! let runner = LeanRunner::new("../jolt_oracle")?;
//! let result = runner.poseidon_hash(&[Fr::ONE, Fr::from_u64(2)])?;
//! ```

use crate::error::{ErrorCode, OracleResult};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// Result from the Lean oracle.
#[derive(Debug)]
pub enum LeanResult {
    /// Successful computation with hex output
    Ok(String),
    /// Error with code and name
    Err {
        /// Numeric error code
        code: u32,
        /// Error name string
        name: String,
    },
}

/// Runner that invokes the Lean oracle via subprocess.
pub struct LeanRunner {
    /// Path to the jolt_oracle directory
    project_path: PathBuf,
    /// Path to the oracle executable
    oracle_path: PathBuf,
}

impl LeanRunner {
    /// Create a new LeanRunner.
    ///
    /// # Arguments
    /// * `project_path` - Path to the jolt_oracle directory
    pub fn new<P: AsRef<Path>>(project_path: P) -> OracleResult<Self> {
        let project_path = project_path.as_ref().to_path_buf();

        // Determine oracle executable path
        // On Unix: .lake/build/bin/oracle
        // On Windows: .lake/build/bin/oracle.exe
        let oracle_path = if cfg!(windows) {
            project_path.join(".lake/build/bin/oracle.exe")
        } else {
            project_path.join(".lake/build/bin/oracle")
        };

        Ok(Self {
            project_path,
            oracle_path,
        })
    }

    /// Check if the Lean oracle is available.
    pub fn is_available(&self) -> bool {
        self.oracle_path.exists()
    }

    /// Run the oracle with given arguments.
    fn run_oracle(&self, args: &[&str]) -> OracleResult<Output> {
        let output = Command::new(&self.oracle_path)
            .args(args)
            .current_dir(&self.project_path)
            .output()
            .map_err(|_| ErrorCode::E100_InvalidJSON)?;

        Ok(output)
    }

    /// Export metadata from the Lean oracle.
    pub fn export_metadata(&self) -> OracleResult<String> {
        let output = self.run_oracle(&["export-metadata"])?;

        if !output.status.success() {
            return Err(ErrorCode::E100_InvalidJSON);
        }

        String::from_utf8(output.stdout)
            .map_err(|_| ErrorCode::E105_InvalidUTF8)
    }

    /// Generate corpus from the Lean oracle.
    pub fn generate_corpus(&self) -> OracleResult<String> {
        let output = self.run_oracle(&["generate-corpus"])?;

        if !output.status.success() {
            return Err(ErrorCode::E100_InvalidJSON);
        }

        String::from_utf8(output.stdout)
            .map_err(|_| ErrorCode::E105_InvalidUTF8)
    }

    /// Parse a result from JSON output.
    pub fn parse_result(json: &str) -> OracleResult<LeanResult> {
        // Simple parsing - in production, use serde_json
        if json.contains("\"ok\"") {
            // Extract the value after "ok"
            if let Some(start) = json.find("\"hash\":\"") {
                let start = start + 8;
                if let Some(end) = json[start..].find('"') {
                    return Ok(LeanResult::Ok(json[start..start + end].to_string()));
                }
            }
            if let Some(start) = json.find("\"result\":\"") {
                let start = start + 10;
                if let Some(end) = json[start..].find('"') {
                    return Ok(LeanResult::Ok(json[start..start + end].to_string()));
                }
            }
            if let Some(start) = json.find("\"decimal\":\"") {
                let start = start + 11;
                if let Some(end) = json[start..].find('"') {
                    return Ok(LeanResult::Ok(json[start..start + end].to_string()));
                }
            }
            Ok(LeanResult::Ok(String::new()))
        } else if json.contains("\"err\"") {
            // Extract error code and name
            let code = extract_number(json, "\"code\":");
            let name = extract_string(json, "\"name\":\"");
            Ok(LeanResult::Err {
                code: code.unwrap_or(0),
                name: name.unwrap_or_else(|| "Unknown".to_string()),
            })
        } else {
            Err(ErrorCode::E100_InvalidJSON)
        }
    }
}

fn extract_number(s: &str, prefix: &str) -> Option<u32> {
    let start = s.find(prefix)? + prefix.len();
    let end = s[start..].find(|c: char| !c.is_ascii_digit())?;
    s[start..start + end].parse().ok()
}

fn extract_string(s: &str, prefix: &str) -> Option<String> {
    let start = s.find(prefix)? + prefix.len();
    let end = s[start..].find('"')?;
    Some(s[start..start + end].to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_ok_result() {
        let json = r#"{"ok":{"hash":"abc123"}}"#;
        match LeanRunner::parse_result(json) {
            Ok(LeanResult::Ok(val)) => assert_eq!(val, "abc123"),
            _ => panic!("Expected Ok result"),
        }
    }

    #[test]
    fn test_parse_err_result() {
        let json = r#"{"err":{"code":300,"name":"E300_NonCanonicalFr"}}"#;
        match LeanRunner::parse_result(json) {
            Ok(LeanResult::Err { code, name }) => {
                assert_eq!(code, 300);
                assert_eq!(name, "E300_NonCanonicalFr");
            }
            _ => panic!("Expected Err result"),
        }
    }
}
