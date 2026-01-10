//! Corpus-based conformance testing.
//!
//! This module loads test vectors from corpus.json and runs them
//! against the Rust implementation to verify conformance with the Lean oracle.
//!
//! # Requirements
//!
//! - CONF-001: Load and parse corpus.json
//! - CONF-002: Execute all test vectors
//! - CONF-003: Compare expected vs actual results
//! - CONF-004: Report pass/fail with details

use crate::error::ErrorCode;
use crate::field::Fr;
use crate::json::parse as parse_json;
use crate::poseidon::{hash, permute};
use serde::Deserialize;
use std::fs;
use std::path::Path;

/// Corpus manifest with metadata.
#[derive(Debug, Deserialize)]
pub struct CorpusManifest {
    /// Format version of the corpus file.
    pub format_version: String,
    /// Lean version used to generate the corpus.
    pub lean_version: String,
    /// Oracle version from metadata.
    pub oracle_version: String,
    /// BLS12-381 modulus in decimal.
    pub modulus_decimal: String,
    /// BLS12-381 modulus in hex.
    pub modulus_hex: String,
    /// SHA-256 hash of round constants.
    pub round_constants_hash: String,
    /// Corpus version.
    pub version: String,
}

/// A corpus containing test vectors.
#[derive(Debug, Deserialize)]
pub struct Corpus {
    /// Corpus metadata.
    pub manifest: CorpusManifest,
    /// List of test vectors.
    pub vectors: Vec<TestVector>,
}

/// A single test vector.
#[derive(Debug, Deserialize)]
pub struct TestVector {
    /// Unique identifier for the test.
    pub id: String,
    /// Operation to test (e.g., "fr_canonical", "poseidon_hash").
    pub op: String,
    /// Input parameters for the operation.
    pub input: serde_json::Value,
    /// Expected result (success or error).
    pub expected: serde_json::Value,
}

/// Result of running a single test vector.
#[derive(Debug)]
pub enum TestResult {
    /// Test passed.
    Pass,
    /// Test failed with mismatch.
    Fail {
        /// Expected result from the corpus.
        expected: String,
        /// Actual result from the Rust implementation.
        actual: String,
    },
    /// Test was skipped (operation not implemented).
    Skip {
        /// Reason for skipping.
        reason: String,
    },
    /// Test errored during execution.
    Error {
        /// Error message.
        message: String,
    },
}

impl TestResult {
    /// Returns true if this is a passing result.
    pub fn is_pass(&self) -> bool {
        matches!(self, Self::Pass)
    }

    /// Returns true if this is a failing result.
    pub fn is_fail(&self) -> bool {
        matches!(self, Self::Fail { .. })
    }
}

/// Results from running the corpus.
#[derive(Debug, Default)]
pub struct CorpusResults {
    /// Number of tests that passed.
    pub passed: usize,
    /// Number of tests that failed.
    pub failed: usize,
    /// Number of tests that were skipped.
    pub skipped: usize,
    /// Number of tests that errored.
    pub errors: usize,
    /// Detailed results for each test.
    pub details: Vec<(String, TestResult)>,
}

impl CorpusResults {
    /// Create a new empty results container.
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a test result.
    pub fn record(&mut self, id: &str, result: TestResult) {
        match &result {
            TestResult::Pass => self.passed += 1,
            TestResult::Fail { .. } => self.failed += 1,
            TestResult::Skip { .. } => self.skipped += 1,
            TestResult::Error { .. } => self.errors += 1,
        }
        self.details.push((id.to_string(), result));
    }

    /// Get total number of tests run.
    pub fn total(&self) -> usize {
        self.passed + self.failed + self.skipped + self.errors
    }

    /// Returns true if all tests passed (no failures or errors).
    pub fn all_passed(&self) -> bool {
        self.failed == 0 && self.errors == 0
    }

    /// Get a summary string of the results.
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

    /// Get failures only.
    pub fn failures(&self) -> Vec<&(String, TestResult)> {
        self.details
            .iter()
            .filter(|(_, r)| matches!(r, TestResult::Fail { .. }))
            .collect()
    }

    /// Get errors only.
    pub fn error_details(&self) -> Vec<&(String, TestResult)> {
        self.details
            .iter()
            .filter(|(_, r)| matches!(r, TestResult::Error { .. }))
            .collect()
    }
}

/// Corpus runner that executes test vectors.
pub struct CorpusRunner {
    corpus: Corpus,
}

impl CorpusRunner {
    /// Load corpus from a file path.
    pub fn load<P: AsRef<Path>>(path: P) -> Result<Self, String> {
        let content = fs::read_to_string(path.as_ref())
            .map_err(|e| format!("Failed to read corpus file: {}", e))?;

        let corpus: Corpus = serde_json::from_str(&content)
            .map_err(|e| format!("Failed to parse corpus JSON: {}", e))?;

        Ok(Self { corpus })
    }

    /// Get the corpus manifest.
    pub fn manifest(&self) -> &CorpusManifest {
        &self.corpus.manifest
    }

    /// Get the number of test vectors.
    pub fn vector_count(&self) -> usize {
        self.corpus.vectors.len()
    }

    /// Run all test vectors and return results.
    pub fn run_all(&self) -> CorpusResults {
        let mut results = CorpusResults::new();

        for vector in &self.corpus.vectors {
            let result = self.run_vector(vector);
            results.record(&vector.id, result);
        }

        results
    }

    /// Run a single test vector.
    fn run_vector(&self, vector: &TestVector) -> TestResult {
        match vector.op.as_str() {
            "fr_canonical" => self.run_fr_canonical(vector),
            "fr_add" => self.run_fr_add(vector),
            "fr_mul" => self.run_fr_mul(vector),
            "poseidon_params" => self.run_poseidon_params(vector),
            "poseidon_hash" => self.run_poseidon_hash(vector),
            "poseidon_permute_trace" => self.run_poseidon_permute_trace(vector),
            "compute_state_digest" => self.run_compute_state_digest(vector),
            "parse_json" => self.run_parse_json(vector),
            "parse_hex" => self.run_parse_hex(vector),
            _ => TestResult::Skip {
                reason: format!("Unknown operation: {}", vector.op),
            },
        }
    }

    /// Run fr_canonical test.
    fn run_fr_canonical(&self, vector: &TestVector) -> TestResult {
        let hex = match vector.input.get("hex").and_then(|v| v.as_str()) {
            Some(h) => h,
            None => {
                return TestResult::Error {
                    message: "Missing 'hex' in input".to_string(),
                }
            }
        };

        // Parse hex to bytes
        let bytes = match hex::decode(hex) {
            Ok(b) => b,
            Err(e) => {
                return TestResult::Error {
                    message: format!("Invalid hex: {}", e),
                }
            }
        };

        // Try to create Fr from bytes
        let result = if bytes.len() == 32 {
            let mut arr = [0u8; 32];
            arr.copy_from_slice(&bytes);
            Fr::from_bytes_le(&arr)
        } else {
            Err(ErrorCode::E104_WrongLength(
                "32".to_string(),
                bytes.len() as u64,
            ))
        };

        // Check expected
        if let Some(ok) = vector.expected.get("ok") {
            // Expected success
            match result {
                Ok(fr) => {
                    let expected_decimal = ok.get("decimal").and_then(|v| v.as_str()).unwrap_or("");
                    let actual_decimal = fr_to_decimal(&fr);
                    if actual_decimal == expected_decimal {
                        TestResult::Pass
                    } else {
                        TestResult::Fail {
                            expected: expected_decimal.to_string(),
                            actual: actual_decimal,
                        }
                    }
                }
                Err(e) => TestResult::Fail {
                    expected: format!("ok: {:?}", ok),
                    actual: format!("err: {:?}", e),
                },
            }
        } else if let Some(err) = vector.expected.get("err") {
            // Expected error
            match result {
                Ok(fr) => TestResult::Fail {
                    expected: format!("err: {:?}", err),
                    actual: format!("ok: {}", fr_to_decimal(&fr)),
                },
                Err(e) => {
                    let expected_code =
                        err.get("code").and_then(|v| v.as_u64()).unwrap_or(0) as u32;
                    let actual_code = e.code();
                    if actual_code == expected_code {
                        TestResult::Pass
                    } else {
                        TestResult::Fail {
                            expected: format!("E{}", expected_code),
                            actual: format!("E{}", actual_code),
                        }
                    }
                }
            }
        } else {
            TestResult::Error {
                message: "Invalid expected format".to_string(),
            }
        }
    }

    /// Run fr_add test.
    fn run_fr_add(&self, vector: &TestVector) -> TestResult {
        let a_hex = match vector.input.get("a").and_then(|v| v.as_str()) {
            Some(h) => h,
            None => {
                return TestResult::Error {
                    message: "Missing 'a' in input".to_string(),
                }
            }
        };
        let b_hex = match vector.input.get("b").and_then(|v| v.as_str()) {
            Some(h) => h,
            None => {
                return TestResult::Error {
                    message: "Missing 'b' in input".to_string(),
                }
            }
        };

        let a = match parse_fr_hex(a_hex) {
            Ok(fr) => fr,
            Err(e) => return TestResult::Error { message: e },
        };
        let b = match parse_fr_hex(b_hex) {
            Ok(fr) => fr,
            Err(e) => return TestResult::Error { message: e },
        };

        let result = a + b;
        let result_hex = hex::encode(result.to_bytes_le());

        if let Some(ok) = vector.expected.get("ok") {
            let expected_hex = ok
                .get("result")
                .and_then(|v| v.as_str())
                .unwrap_or("")
                .to_lowercase();
            if result_hex == expected_hex {
                TestResult::Pass
            } else {
                TestResult::Fail {
                    expected: expected_hex,
                    actual: result_hex,
                }
            }
        } else {
            TestResult::Error {
                message: "Expected 'ok' result for fr_add".to_string(),
            }
        }
    }

    /// Run fr_mul test.
    fn run_fr_mul(&self, vector: &TestVector) -> TestResult {
        let a_hex = match vector.input.get("a").and_then(|v| v.as_str()) {
            Some(h) => h,
            None => {
                return TestResult::Error {
                    message: "Missing 'a' in input".to_string(),
                }
            }
        };
        let b_hex = match vector.input.get("b").and_then(|v| v.as_str()) {
            Some(h) => h,
            None => {
                return TestResult::Error {
                    message: "Missing 'b' in input".to_string(),
                }
            }
        };

        let a = match parse_fr_hex(a_hex) {
            Ok(fr) => fr,
            Err(e) => return TestResult::Error { message: e },
        };
        let b = match parse_fr_hex(b_hex) {
            Ok(fr) => fr,
            Err(e) => return TestResult::Error { message: e },
        };

        let result = a * b;
        let result_hex = hex::encode(result.to_bytes_le());

        if let Some(ok) = vector.expected.get("ok") {
            let expected_hex = ok
                .get("result")
                .and_then(|v| v.as_str())
                .unwrap_or("")
                .to_lowercase();
            if result_hex == expected_hex {
                TestResult::Pass
            } else {
                TestResult::Fail {
                    expected: expected_hex,
                    actual: result_hex,
                }
            }
        } else {
            TestResult::Error {
                message: "Expected 'ok' result for fr_mul".to_string(),
            }
        }
    }

    /// Run poseidon_params test.
    fn run_poseidon_params(&self, vector: &TestVector) -> TestResult {
        use crate::poseidon::{FULL_ROUNDS, PARTIAL_ROUNDS, RATE, WIDTH};

        if let Some(ok) = vector.expected.get("ok") {
            let expected_width = ok.get("width").and_then(|v| v.as_u64()).unwrap_or(0) as usize;
            let expected_rate = ok.get("rate").and_then(|v| v.as_u64()).unwrap_or(0) as usize;
            let expected_full =
                ok.get("full_rounds").and_then(|v| v.as_u64()).unwrap_or(0) as usize;
            let expected_partial = ok
                .get("partial_rounds")
                .and_then(|v| v.as_u64())
                .unwrap_or(0) as usize;

            if WIDTH == expected_width
                && RATE == expected_rate
                && FULL_ROUNDS == expected_full
                && PARTIAL_ROUNDS == expected_partial
            {
                TestResult::Pass
            } else {
                TestResult::Fail {
                    expected: format!(
                        "t={}, r={}, RF={}, RP={}",
                        expected_width, expected_rate, expected_full, expected_partial
                    ),
                    actual: format!(
                        "t={}, r={}, RF={}, RP={}",
                        WIDTH, RATE, FULL_ROUNDS, PARTIAL_ROUNDS
                    ),
                }
            }
        } else {
            TestResult::Error {
                message: "Expected 'ok' result for poseidon_params".to_string(),
            }
        }
    }

    /// Run poseidon_hash test.
    fn run_poseidon_hash(&self, vector: &TestVector) -> TestResult {
        let elements = match vector.input.get("elements").and_then(|v| v.as_array()) {
            Some(arr) => arr,
            None => {
                return TestResult::Error {
                    message: "Missing 'elements' in input".to_string(),
                }
            }
        };

        let mut frs = Vec::new();
        for elem in elements {
            let hex = match elem.as_str() {
                Some(h) => h,
                None => {
                    return TestResult::Error {
                        message: "Element is not a string".to_string(),
                    }
                }
            };
            match parse_fr_hex(hex) {
                Ok(fr) => frs.push(fr),
                Err(e) => return TestResult::Error { message: e },
            }
        }

        // Hash using Poseidon
        let result = hash(&frs);
        let result_hex = hex::encode(result.to_bytes_le());

        if let Some(ok) = vector.expected.get("ok") {
            let expected_hex = ok
                .get("hash")
                .and_then(|v| v.as_str())
                .unwrap_or("")
                .to_lowercase();
            if result_hex == expected_hex {
                TestResult::Pass
            } else {
                TestResult::Fail {
                    expected: expected_hex,
                    actual: result_hex,
                }
            }
        } else {
            TestResult::Error {
                message: "Expected 'ok' result for poseidon_hash".to_string(),
            }
        }
    }

    /// Run poseidon_permute_trace test.
    fn run_poseidon_permute_trace(&self, vector: &TestVector) -> TestResult {
        let initial_state = match vector.input.get("initial_state").and_then(|v| v.as_array()) {
            Some(arr) => arr,
            None => {
                return TestResult::Error {
                    message: "Missing 'initial_state' in input".to_string(),
                }
            }
        };

        if initial_state.len() != 3 {
            return TestResult::Error {
                message: format!(
                    "initial_state must have 3 elements, got {}",
                    initial_state.len()
                ),
            };
        }

        let mut state = [Fr::ZERO; 3];
        for (i, elem) in initial_state.iter().enumerate() {
            let hex = match elem.as_str() {
                Some(h) => h,
                None => {
                    return TestResult::Error {
                        message: "State element is not a string".to_string(),
                    }
                }
            };
            match parse_fr_hex(hex) {
                Ok(fr) => state[i] = fr,
                Err(e) => return TestResult::Error { message: e },
            }
        }

        // Run permutation
        state = permute(&state);

        // Compare final state
        if let Some(ok) = vector.expected.get("ok") {
            let expected_final = match ok.get("final_state").and_then(|v| v.as_array()) {
                Some(arr) => arr,
                None => {
                    return TestResult::Error {
                        message: "Missing 'final_state' in expected".to_string(),
                    }
                }
            };

            for (i, expected_elem) in expected_final.iter().enumerate() {
                let expected_hex = expected_elem.as_str().unwrap_or("").to_lowercase();
                let actual_hex = hex::encode(state[i].to_bytes_le());
                if actual_hex != expected_hex {
                    return TestResult::Fail {
                        expected: format!("state[{}] = {}", i, expected_hex),
                        actual: format!("state[{}] = {}", i, actual_hex),
                    };
                }
            }
            TestResult::Pass
        } else {
            TestResult::Error {
                message: "Expected 'ok' result for poseidon_permute_trace".to_string(),
            }
        }
    }

    /// Run compute_state_digest test.
    fn run_compute_state_digest(&self, vector: &TestVector) -> TestResult {
        // Check if expected is TBD
        if let Some(ok) = vector.expected.get("ok") {
            if let Some(digest) = ok.get("digest").and_then(|v| v.as_str()) {
                if digest == "TBD" {
                    return TestResult::Skip {
                        reason: "Digest value is TBD in corpus".to_string(),
                    };
                }
            }
        }

        // TODO: Parse state and compute digest
        TestResult::Skip {
            reason: "compute_state_digest not yet implemented in corpus runner".to_string(),
        }
    }

    /// Run parse_json test (negative test).
    fn run_parse_json(&self, vector: &TestVector) -> TestResult {
        let raw = match vector.input.get("raw").and_then(|v| v.as_str()) {
            Some(r) => r,
            None => {
                return TestResult::Error {
                    message: "Missing 'raw' in input".to_string(),
                }
            }
        };

        let result = parse_json(raw.as_bytes());

        if let Some(err) = vector.expected.get("err") {
            // Expected error
            match result {
                Ok(_) => TestResult::Fail {
                    expected: format!("err: {:?}", err),
                    actual: "ok".to_string(),
                },
                Err(e) => {
                    let expected_code =
                        err.get("code").and_then(|v| v.as_u64()).unwrap_or(0) as u32;
                    let actual_code = e.code();
                    if actual_code == expected_code {
                        TestResult::Pass
                    } else {
                        TestResult::Fail {
                            expected: format!("E{}", expected_code),
                            actual: format!("E{}", actual_code),
                        }
                    }
                }
            }
        } else {
            TestResult::Error {
                message: "Expected 'err' result for negative test".to_string(),
            }
        }
    }

    /// Run parse_hex test (negative test).
    fn run_parse_hex(&self, vector: &TestVector) -> TestResult {
        let hex_str = match vector.input.get("hex").and_then(|v| v.as_str()) {
            Some(h) => h,
            None => {
                return TestResult::Error {
                    message: "Missing 'hex' in input".to_string(),
                }
            }
        };

        let result = hex::decode(hex_str);

        if let Some(err) = vector.expected.get("err") {
            // Expected error
            match result {
                Ok(_) => TestResult::Fail {
                    expected: format!("err: {:?}", err),
                    actual: "ok".to_string(),
                },
                Err(_) => {
                    // Hex decode error maps to E103
                    let expected_code =
                        err.get("code").and_then(|v| v.as_u64()).unwrap_or(0) as u32;
                    if expected_code == 103 {
                        TestResult::Pass
                    } else {
                        TestResult::Fail {
                            expected: format!("E{}", expected_code),
                            actual: "E103".to_string(),
                        }
                    }
                }
            }
        } else {
            TestResult::Error {
                message: "Expected 'err' result for negative test".to_string(),
            }
        }
    }
}

/// Parse hex string to Fr.
fn parse_fr_hex(hex: &str) -> Result<Fr, String> {
    let bytes = hex::decode(hex).map_err(|e| format!("Invalid hex: {}", e))?;
    if bytes.len() != 32 {
        return Err(format!("Expected 32 bytes, got {}", bytes.len()));
    }
    let mut arr = [0u8; 32];
    arr.copy_from_slice(&bytes);
    Fr::from_bytes_le(&arr).map_err(|e| format!("Invalid Fr: {:?}", e))
}

/// Convert Fr to decimal string.
fn fr_to_decimal(fr: &Fr) -> String {
    let bytes = fr.to_bytes_le();
    let mut result = vec![0u8];

    for &byte in bytes.iter().rev() {
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
    fn test_parse_fr_hex() {
        let zero_hex = "0000000000000000000000000000000000000000000000000000000000000000";
        let result = parse_fr_hex(zero_hex);
        assert!(result.is_ok());
        assert_eq!(fr_to_decimal(&result.unwrap()), "0");

        let one_hex = "0100000000000000000000000000000000000000000000000000000000000000";
        let result = parse_fr_hex(one_hex);
        assert!(result.is_ok());
        assert_eq!(fr_to_decimal(&result.unwrap()), "1");
    }

    #[test]
    fn test_corpus_results() {
        let mut results = CorpusResults::new();
        results.record("test1", TestResult::Pass);
        results.record("test2", TestResult::Pass);
        results.record(
            "test3",
            TestResult::Fail {
                expected: "a".to_string(),
                actual: "b".to_string(),
            },
        );
        results.record(
            "test4",
            TestResult::Skip {
                reason: "not implemented".to_string(),
            },
        );

        assert_eq!(results.passed, 2);
        assert_eq!(results.failed, 1);
        assert_eq!(results.skipped, 1);
        assert_eq!(results.total(), 4);
        assert!(!results.all_passed());
    }
}
