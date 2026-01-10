//! JSON parsing and JCS canonicalization.
//!
//! Implements I-JSON (RFC 7493) parsing with strict validation and
//! JCS (RFC 8785) canonicalization for deterministic output.
//!
//! # Requirements
//!
//! - JSON-001: UTF-8 validation
//! - JSON-002: Reject unpaired surrogates
//! - JSON-003: Reject duplicate keys after unescaping
//! - JSON-004A/B: Number validation (finite IEEE-754, integer bounds)
//! - JSON-005: Unescape before duplicate key check
//! - JSON-006: Reject NaN/Infinity literals
//! - JCS-001..005: Canonicalization rules

// TODO: Implement in Phase 3
