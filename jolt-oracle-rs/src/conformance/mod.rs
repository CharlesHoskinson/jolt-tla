//! Differential testing harness for Rust vs Lean conformance.
//!
//! This module provides infrastructure for comparing the Rust implementation
//! against the Lean oracle to ensure bit-identical output for all operations.
//!
//! # Requirements
//!
//! - CONF-002: Compare outputs as raw bytes, not parsed structures
//! - CONF-003: Emit repro bundle on mismatch
//! - QG-1: Conformance guarantee

pub mod corpus;
mod harness;
mod repro;
mod runner;

pub use corpus::{Corpus, CorpusResults, CorpusRunner, TestResult, TestVector};
pub use harness::{BatchResult, DiffResult, DiffTestHarness};
pub use repro::ReproBundle;
pub use runner::{LeanDigestRunner, OracleOutput, OracleRunner, RustDigestRunner};

/// Result type for conformance operations.
pub type ConformanceResult<T> = Result<T, ConformanceError>;

/// Errors that can occur during conformance testing.
#[derive(Debug)]
pub enum ConformanceError {
    /// Lean oracle not available
    LeanNotAvailable(String),
    /// Failed to run Lean oracle
    LeanExecutionFailed(String),
    /// Failed to parse Lean output
    LeanOutputParseError(String),
    /// Rust implementation error
    RustError(String),
    /// I/O error
    IoError(String),
    /// Mismatch between Rust and Lean outputs
    Mismatch {
        /// Input description
        input: String,
        /// Rust result
        rust_result: String,
        /// Lean result
        lean_result: String,
        /// First differing byte index (if applicable)
        first_diff: Option<usize>,
    },
}

impl std::fmt::Display for ConformanceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LeanNotAvailable(msg) => write!(f, "Lean oracle not available: {}", msg),
            Self::LeanExecutionFailed(msg) => write!(f, "Lean execution failed: {}", msg),
            Self::LeanOutputParseError(msg) => write!(f, "Failed to parse Lean output: {}", msg),
            Self::RustError(msg) => write!(f, "Rust implementation error: {}", msg),
            Self::IoError(msg) => write!(f, "I/O error: {}", msg),
            Self::Mismatch {
                input,
                rust_result,
                lean_result,
                first_diff,
            } => {
                write!(
                    f,
                    "Mismatch for input '{}': Rust='{}', Lean='{}'",
                    input, rust_result, lean_result
                )?;
                if let Some(idx) = first_diff {
                    write!(f, " (first diff at byte {})", idx)?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for ConformanceError {}
