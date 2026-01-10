//! Error handling for the Jolt Oracle.
//!
//! Error codes are generated from Lean metadata to ensure exact correspondence
//! between the Rust and Lean implementations.
//!
//! # Requirements
//!
//! - ERR-001: ErrorCode enum generated from Lean metadata export
//! - ERR-002: Discriminant values match Lean exactly
//! - ERR-003: Identical ErrorCodes for identical invalid inputs
//! - ERR-004: Return ErrorCode::InternalError rather than panic

// Include the generated error code enum
include!(concat!(env!("OUT_DIR"), "/error_generated.rs"));
