//! Jolt Oracle - Rust implementation of the Jolt zkVM specification.
//!
//! This crate provides a verified drop-in replacement for the Lean 4 oracle,
//! with byte-identical output for all conformance test vectors.
//!
//! # Architecture
//!
//! The implementation is organized into modules matching the specification:
//!
//! - [`field`] - BLS12-381 scalar field arithmetic (Fr)
//! - [`poseidon`] - Poseidon hash function (JOLT_POSEIDON_FR_V1)
//! - [`state`] - VM state types and digest computation
//! - [`json`] - I-JSON parsing and JCS canonicalization
//! - [`error`] - Error codes matching the Lean specification
//!
//! # Conformance
//!
//! All outputs are verified against the Lean oracle using differential testing.
//! The build.rs script generates code from `metadata.json` exported by Lean,
//! ensuring error codes and cryptographic parameters stay in sync.

// Consensus-critical code must avoid unwrap/expect/panic in library code.
// Tests are checked separately with `cargo test`.
#![deny(clippy::unwrap_used)]
#![deny(clippy::expect_used)]
#![deny(clippy::panic)]
#![warn(missing_docs)]

pub mod conformance;
pub mod error;
pub mod field;
pub mod json;
pub mod poseidon;
pub mod runner;
pub mod state;

// Re-export commonly used types
pub use conformance::{DiffResult, DiffTestHarness};
pub use error::{ErrorCode, OracleResult};
pub use field::Fr;
pub use state::{compute_state_digest, Bytes32, ConfigTag, VMStateV1};
