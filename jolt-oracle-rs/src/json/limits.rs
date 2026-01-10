//! DoS protection limits for JSON parsing.
//!
//! These limits match the Lean specification Safety.lean to ensure consistent
//! rejection of maliciously large inputs across implementations.
//!
//! # Requirements
//!
//! - E110_InputTooLarge: Total input size limit
//! - E111_NestingTooDeep: Maximum nesting depth
//! - E112_StringTooLong: Maximum string length
//! - E113_TooManyFields: Maximum object fields
//! - E114_ArrayTooLong: Maximum array length

/// Maximum safe integer value (2^53 - 1) per I-JSON (RFC 7493).
///
/// JSON numbers must be within ±MAX_SAFE_INT for exact IEEE-754 representation.
pub const MAX_SAFE_INT: i64 = (1i64 << 53) - 1;

/// Minimum safe integer value (-(2^53 - 1)).
pub const MIN_SAFE_INT: i64 = -MAX_SAFE_INT;

/// DoS protection limits for JSON parsing.
///
/// These limits are configurable but have sensible defaults matching
/// the Lean specification for consensus-critical use cases.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// Maximum total input size in bytes (E110)
    pub max_input_size: u64,
    /// Maximum nesting depth for arrays/objects (E111)
    pub max_nesting_depth: u64,
    /// Maximum string length in bytes (E112)
    pub max_string_length: u64,
    /// Maximum number of fields in an object (E113)
    pub max_object_fields: u64,
    /// Maximum number of elements in an array (E114)
    pub max_array_length: u64,
    /// Whether to enforce ASCII-only strings (E115)
    pub ascii_only: bool,
}

impl Limits {
    /// Default limits for consensus-critical parsing.
    ///
    /// These match the Lean specification defaults.
    pub const fn consensus() -> Self {
        Self {
            max_input_size: 1024 * 1024,  // 1 MiB
            max_nesting_depth: 32,        // 32 levels
            max_string_length: 64 * 1024, // 64 KiB
            max_object_fields: 1024,      // 1024 fields
            max_array_length: 10_000,     // 10,000 elements
            ascii_only: true,             // ASCII-only for determinism
        }
    }

    /// Lenient limits for non-consensus use cases (e.g., debugging).
    pub const fn lenient() -> Self {
        Self {
            max_input_size: 16 * 1024 * 1024, // 16 MiB
            max_nesting_depth: 128,           // 128 levels
            max_string_length: 1024 * 1024,   // 1 MiB
            max_object_fields: 10_000,        // 10,000 fields
            max_array_length: 100_000,        // 100,000 elements
            ascii_only: false,                // Allow Unicode
        }
    }

    /// Check if a number is within safe integer bounds.
    pub fn is_safe_integer(value: i64) -> bool {
        (MIN_SAFE_INT..=MAX_SAFE_INT).contains(&value)
    }
}

impl Default for Limits {
    fn default() -> Self {
        Self::consensus()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_max_safe_int() {
        assert_eq!(MAX_SAFE_INT, 9007199254740991);
        assert_eq!(MIN_SAFE_INT, -9007199254740991);
    }

    #[test]
    fn test_safe_integer_bounds() {
        assert!(Limits::is_safe_integer(0));
        assert!(Limits::is_safe_integer(MAX_SAFE_INT));
        assert!(Limits::is_safe_integer(MIN_SAFE_INT));
        assert!(!Limits::is_safe_integer(MAX_SAFE_INT + 1));
        assert!(!Limits::is_safe_integer(MIN_SAFE_INT - 1));
    }

    #[test]
    fn test_consensus_limits() {
        let limits = Limits::consensus();
        assert_eq!(limits.max_input_size, 1024 * 1024);
        assert_eq!(limits.max_nesting_depth, 32);
        assert_eq!(limits.max_string_length, 64 * 1024);
        assert_eq!(limits.max_object_fields, 1024);
        assert_eq!(limits.max_array_length, 10_000);
        assert!(limits.ascii_only);
    }

    #[test]
    fn test_lenient_limits() {
        let limits = Limits::lenient();
        assert!(!limits.ascii_only);
        assert!(limits.max_input_size > Limits::consensus().max_input_size);
    }
}
