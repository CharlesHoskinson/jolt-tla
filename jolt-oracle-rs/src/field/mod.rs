//! BLS12-381 scalar field (Fr) operations.
//!
//! This module provides the Fr type used throughout the oracle for
//! field arithmetic, Poseidon hashing, and state digests.
//!
//! # Requirements
//!
//! - FR-001: Pinned scalar-field implementation, canonical 32-byte LE encoding
//! - FR-002: Fr::new() validates canonical field element
//! - FR-003: Non-canonical bytes return ErrorCode::E300_NonCanonicalFr
//! - FR-004: Serialization produces canonical LE 32-byte output
//! - FR-005: Arithmetic produces bit-identical results to Lean
//! - FR-006: Division by zero returns ErrorCode::E303_InvalidFrEncoding

mod fr;

pub use fr::Fr;

// Include generated modulus constants
include!(concat!(env!("OUT_DIR"), "/modulus_generated.rs"));
