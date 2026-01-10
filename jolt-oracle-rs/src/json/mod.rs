//! JSON parsing and JCS canonicalization.
//!
//! Implements I-JSON (RFC 7493) parsing with strict validation and
//! JCS (RFC 8785) canonicalization for deterministic output.
//!
//! # Architecture
//!
//! The JSON subsystem is organized into focused modules:
//!
//! - [`types`] - Core JSON value types
//! - [`limits`] - DoS protection limits
//! - [`lexer`] - Tokenizer with UTF-8/escape handling
//! - [`parser`] - Recursive descent parser with validation
//! - [`jcs`] - RFC 8785 canonicalization
//!
//! # Requirements
//!
//! ## Parsing (JSON-*)
//!
//! - JSON-001: UTF-8 validation
//! - JSON-002: Reject unpaired surrogates
//! - JSON-003: Reject duplicate keys after unescaping
//! - JSON-004A/B: Number validation (finite IEEE-754, integer bounds ±2^53-1)
//! - JSON-005: Unescape before duplicate key check
//! - JSON-006: Reject NaN/Infinity literals (not valid JSON)
//!
//! ## Canonicalization (JCS-*)
//!
//! - JCS-001..002: UTF-16 key comparator for object key ordering
//! - JCS-003: ECMAScript number serialization
//! - JCS-004..005: Full canonicalization conformance
//!
//! # Example
//!
//! ```
//! use jolt_oracle::json::{parse, canonicalize, JsonValue};
//!
//! // Parse JSON with consensus limits
//! let value = parse(b"{\"b\":2,\"a\":1}").unwrap();
//!
//! // Canonicalize produces deterministic output with sorted keys
//! let canonical = canonicalize(&value);
//! assert_eq!(canonical, "{\"a\":1,\"b\":2}");
//! ```

pub mod jcs;
pub mod lexer;
pub mod limits;
pub mod parser;
pub mod types;

// Re-export commonly used items
pub use jcs::canonicalize;
pub use limits::Limits;
pub use parser::{parse, parse_with_limits};
pub use types::JsonValue;
