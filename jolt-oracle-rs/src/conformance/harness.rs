//! Differential test harness for comparing Rust and Lean implementations.

use super::repro::ReproBundle;
use super::runner::{LeanDigestRunner, OracleOutput, OracleRunner, RustDigestRunner};
use super::{ConformanceError, ConformanceResult};
use crate::state::{Bytes32, VMStateV1};
use std::path::Path;

/// Result of a differential test.
#[derive(Debug)]
pub enum DiffResult {
    /// Both implementations produced the same output.
    Match {
        /// The matching output value.
        value: String,
    },
    /// Implementations produced different outputs.
    Mismatch {
        /// Rust output.
        rust: OracleOutput,
        /// Lean output.
        lean: OracleOutput,
        /// Repro bundle for debugging.
        repro: ReproBundle,
    },
    /// Lean oracle is not available.
    LeanUnavailable,
}

impl DiffResult {
    /// Check if the result is a match.
    pub fn is_match(&self) -> bool {
        matches!(self, Self::Match { .. })
    }

    /// Check if the result is a mismatch.
    pub fn is_mismatch(&self) -> bool {
        matches!(self, Self::Mismatch { .. })
    }
}

/// Differential test harness for comparing implementations.
pub struct DiffTestHarness {
    /// Rust implementation runner.
    rust_runner: RustDigestRunner,
    /// Lean implementation runner (optional).
    lean_runner: Option<LeanDigestRunner>,
}

impl DiffTestHarness {
    /// Create a new test harness.
    ///
    /// # Arguments
    /// * `lean_project_path` - Path to the jolt_oracle directory (optional)
    pub fn new<P: AsRef<Path>>(lean_project_path: Option<P>) -> Self {
        let lean_runner = lean_project_path.and_then(|p| LeanDigestRunner::new(p).ok());

        Self {
            rust_runner: RustDigestRunner::new(),
            lean_runner,
        }
    }

    /// Create a harness with only the Rust runner (for unit testing).
    pub fn rust_only() -> Self {
        Self {
            rust_runner: RustDigestRunner::new(),
            lean_runner: None,
        }
    }

    /// Check if the Lean runner is available.
    pub fn has_lean(&self) -> bool {
        self.lean_runner.is_some()
    }

    /// Compare state digest computation between Rust and Lean.
    pub fn compare_digest(
        &self,
        test_name: &str,
        program_hash: &Bytes32,
        state: &VMStateV1,
    ) -> ConformanceResult<DiffResult> {
        // Run Rust implementation
        let rust_output = self.rust_runner.compute_digest(program_hash, state)?;

        // If Lean is not available, return LeanUnavailable
        let lean_runner = match &self.lean_runner {
            Some(r) => r,
            None => return Ok(DiffResult::LeanUnavailable),
        };

        // Run Lean implementation
        let lean_output = lean_runner.compute_digest(program_hash, state)?;

        // Compare outputs
        if rust_output == lean_output {
            Ok(DiffResult::Match {
                value: rust_output.as_string().to_string(),
            })
        } else {
            // Create repro bundle
            let repro = ReproBundle::new(
                test_name.to_string(),
                "state_digest".to_string(),
                format!("{:?}", program_hash),
                format!("{:?}", state),
                rust_output.clone(),
                lean_output.clone(),
            );

            Ok(DiffResult::Mismatch {
                rust: rust_output,
                lean: lean_output,
                repro,
            })
        }
    }

    /// Run Rust implementation only (for testing without Lean).
    pub fn run_rust_digest(
        &self,
        program_hash: &Bytes32,
        state: &VMStateV1,
    ) -> ConformanceResult<OracleOutput> {
        self.rust_runner.compute_digest(program_hash, state)
    }

    /// Run a batch of differential tests.
    pub fn run_batch<'a>(
        &self,
        tests: impl Iterator<Item = (&'a str, &'a Bytes32, &'a VMStateV1)>,
    ) -> BatchResult {
        let mut results = BatchResult::new();

        for (name, program_hash, state) in tests {
            match self.compare_digest(name, program_hash, state) {
                Ok(DiffResult::Match { value }) => {
                    results.record_pass(name, &value);
                }
                Ok(DiffResult::Mismatch { rust, lean, repro }) => {
                    results.record_fail(name, rust, lean, repro);
                }
                Ok(DiffResult::LeanUnavailable) => {
                    results.record_skip(name, "Lean oracle not available");
                }
                Err(e) => {
                    results.record_error(name, e);
                }
            }
        }

        results
    }
}

/// Results from running a batch of differential tests.
#[derive(Debug)]
pub struct BatchResult {
    /// Number of tests that passed.
    pub passed: usize,
    /// Number of tests that failed.
    pub failed: usize,
    /// Number of tests that were skipped.
    pub skipped: usize,
    /// Number of tests that errored.
    pub errors: usize,
    /// Details of failures.
    pub failures: Vec<FailureDetail>,
    /// Details of errors.
    pub error_details: Vec<ErrorDetail>,
}

/// Details about a test failure.
#[derive(Debug)]
pub struct FailureDetail {
    /// Test name.
    pub name: String,
    /// Rust output.
    pub rust: OracleOutput,
    /// Lean output.
    pub lean: OracleOutput,
    /// Repro bundle.
    pub repro: ReproBundle,
}

/// Details about a test error.
#[derive(Debug)]
pub struct ErrorDetail {
    /// Test name.
    pub name: String,
    /// Error that occurred.
    pub error: ConformanceError,
}

impl BatchResult {
    /// Create a new empty batch result.
    pub fn new() -> Self {
        Self {
            passed: 0,
            failed: 0,
            skipped: 0,
            errors: 0,
            failures: Vec::new(),
            error_details: Vec::new(),
        }
    }

    /// Record a passing test.
    pub fn record_pass(&mut self, _name: &str, _value: &str) {
        self.passed += 1;
    }

    /// Record a failing test.
    pub fn record_fail(
        &mut self,
        name: &str,
        rust: OracleOutput,
        lean: OracleOutput,
        repro: ReproBundle,
    ) {
        self.failed += 1;
        self.failures.push(FailureDetail {
            name: name.to_string(),
            rust,
            lean,
            repro,
        });
    }

    /// Record a skipped test.
    pub fn record_skip(&mut self, _name: &str, _reason: &str) {
        self.skipped += 1;
    }

    /// Record a test error.
    pub fn record_error(&mut self, name: &str, error: ConformanceError) {
        self.errors += 1;
        self.error_details.push(ErrorDetail {
            name: name.to_string(),
            error,
        });
    }

    /// Check if all tests passed.
    pub fn all_passed(&self) -> bool {
        self.failed == 0 && self.errors == 0
    }

    /// Get total number of tests run.
    pub fn total(&self) -> usize {
        self.passed + self.failed + self.skipped + self.errors
    }

    /// Format a summary string.
    pub fn summary(&self) -> String {
        format!(
            "{} passed, {} failed, {} skipped, {} errors (total: {})",
            self.passed,
            self.failed,
            self.skipped,
            self.errors,
            self.total()
        )
    }
}

impl Default for BatchResult {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rust_only_harness() {
        let harness = DiffTestHarness::rust_only();
        assert!(!harness.has_lean());

        let program_hash = Bytes32::zero();
        let state = VMStateV1::default();

        let result = harness.compare_digest("test", &program_hash, &state);
        assert!(result.is_ok());
        assert!(matches!(result.unwrap(), DiffResult::LeanUnavailable));
    }

    #[test]
    fn test_rust_digest_execution() {
        let harness = DiffTestHarness::rust_only();
        let program_hash = Bytes32::zero();
        let state = VMStateV1::default();

        let result = harness.run_rust_digest(&program_hash, &state);
        assert!(result.is_ok());

        let output = result.unwrap();
        assert!(output.is_ok());

        // Verify the expected digest from golden vectors
        let expected =
            "24421670062301725635551677633693836338234896090794496795972501815695727753187";
        assert_eq!(output.as_string(), expected);
    }

    #[test]
    fn test_batch_result() {
        let mut result = BatchResult::new();

        result.record_pass("test1", "value1");
        result.record_pass("test2", "value2");
        result.record_skip("test3", "reason");

        assert_eq!(result.passed, 2);
        assert_eq!(result.skipped, 1);
        assert_eq!(result.total(), 3);
        assert!(result.all_passed());
    }
}
