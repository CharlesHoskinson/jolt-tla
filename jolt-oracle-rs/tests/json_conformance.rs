//! JSON subsystem conformance tests.
//!
//! These tests verify conformance with I-JSON (RFC 7493) parsing requirements
//! and JCS (RFC 8785) canonicalization rules.
//!
//! # Requirements Tested
//!
//! - JSON-001..006: Parsing validation
//! - JCS-001..005: Canonicalization conformance

use jolt_oracle::json::{canonicalize, parse, parse_with_limits, JsonValue, Limits};
use std::collections::BTreeMap;

// ============================================================================
// JSON-001: UTF-8 Validation
// ============================================================================

#[test]
fn json001_valid_utf8_accepted() {
    let result = parse(br#""hello""#);
    assert!(result.is_ok(), "JSON-001: Valid UTF-8 should be accepted");
}

#[test]
fn json001_invalid_utf8_rejected() {
    // Invalid UTF-8 sequence
    let invalid = vec![b'"', 0xFF, 0xFE, b'"'];
    let result = parse(&invalid);
    assert!(
        result.is_err(),
        "JSON-001: Invalid UTF-8 should be rejected"
    );
    assert_eq!(result.unwrap_err().code(), 105); // E105_InvalidUTF8
}

#[test]
fn json001_overlong_encoding_rejected() {
    // Overlong encoding of '/' (0x2F) as C0 AF (should be 2F directly)
    let overlong = vec![b'"', 0xC0, 0xAF, b'"'];
    let result = parse(&overlong);
    assert!(
        result.is_err(),
        "JSON-001: Overlong UTF-8 should be rejected"
    );
}

// ============================================================================
// JSON-002: Reject Unpaired Surrogates
// ============================================================================

#[test]
fn json002_unpaired_high_surrogate_rejected() {
    // \uD800 without a following low surrogate
    let result = parse(br#""\uD800""#);
    assert!(
        result.is_err(),
        "JSON-002: Unpaired high surrogate should be rejected"
    );
    assert_eq!(result.unwrap_err().code(), 105); // E105_InvalidUTF8
}

#[test]
fn json002_unpaired_low_surrogate_rejected() {
    // \uDC00 without a preceding high surrogate
    let result = parse(br#""\uDC00""#);
    assert!(
        result.is_err(),
        "JSON-002: Unpaired low surrogate should be rejected"
    );
    assert_eq!(result.unwrap_err().code(), 105); // E105_InvalidUTF8
}

#[test]
fn json002_valid_surrogate_pair_accepted() {
    // \uD83D\uDE00 = U+1F600 (grinning face emoji)
    // But only in non-ASCII mode
    let mut limits = Limits::lenient();
    limits.ascii_only = false;
    let result = parse_with_limits(br#""\uD83D\uDE00""#, limits);
    assert!(
        result.is_ok(),
        "JSON-002: Valid surrogate pair should be accepted"
    );
}

#[test]
fn json002_high_surrogate_followed_by_non_surrogate_rejected() {
    // \uD800\u0041 - high surrogate followed by regular character
    let result = parse(br#""\uD800\u0041""#);
    assert!(
        result.is_err(),
        "JSON-002: High surrogate followed by non-low surrogate should be rejected"
    );
}

// ============================================================================
// JSON-003: Reject Duplicate Keys After Unescaping
// ============================================================================

#[test]
fn json003_duplicate_keys_rejected() {
    let result = parse(br#"{"a": 1, "a": 2}"#);
    assert!(
        result.is_err(),
        "JSON-003: Duplicate keys should be rejected"
    );
    assert_eq!(result.unwrap_err().code(), 101); // E101_DuplicateKey
}

#[test]
fn json003_duplicate_keys_after_unescape_rejected() {
    // "a" and "\u0061" are the same key after unescaping
    let result = parse(br#"{"a": 1, "\u0061": 2}"#);
    assert!(
        result.is_err(),
        "JSON-003: Duplicate keys after unescape should be rejected"
    );
    assert_eq!(result.unwrap_err().code(), 101); // E101_DuplicateKey
}

#[test]
fn json003_different_keys_accepted() {
    let result = parse(br#"{"a": 1, "b": 2}"#);
    assert!(
        result.is_ok(),
        "JSON-003: Different keys should be accepted"
    );
}

// ============================================================================
// JSON-004A: Number Validation (Finite IEEE-754)
// ============================================================================

#[test]
fn json004a_fractional_number_rejected() {
    let result = parse(b"3.14");
    assert!(
        result.is_err(),
        "JSON-004A: Fractional numbers should be rejected"
    );
    assert_eq!(result.unwrap_err().code(), 108); // E108_FractionalNumber
}

#[test]
fn json004a_exponent_notation_rejected() {
    let result = parse(b"1e10");
    assert!(
        result.is_err(),
        "JSON-004A: Exponent notation should be rejected"
    );
    assert_eq!(result.unwrap_err().code(), 107); // E107_ExponentNotation
}

#[test]
fn json004a_exponent_uppercase_rejected() {
    let result = parse(b"1E10");
    assert!(
        result.is_err(),
        "JSON-004A: Uppercase exponent should be rejected"
    );
    assert_eq!(result.unwrap_err().code(), 107); // E107_ExponentNotation
}

#[test]
fn json004a_integer_accepted() {
    let result = parse(b"42");
    assert!(result.is_ok(), "JSON-004A: Integer should be accepted");
    assert_eq!(result.unwrap(), JsonValue::Number(42));
}

#[test]
fn json004a_negative_integer_accepted() {
    let result = parse(b"-42");
    assert!(
        result.is_ok(),
        "JSON-004A: Negative integer should be accepted"
    );
    assert_eq!(result.unwrap(), JsonValue::Number(-42));
}

#[test]
fn json004a_zero_accepted() {
    let result = parse(b"0");
    assert!(result.is_ok(), "JSON-004A: Zero should be accepted");
    assert_eq!(result.unwrap(), JsonValue::Number(0));
}

#[test]
fn json004a_leading_zero_rejected() {
    let result = parse(b"01");
    assert!(
        result.is_err(),
        "JSON-004A: Leading zeros should be rejected"
    );
}

// ============================================================================
// JSON-004B: Integer Bounds (±2^53-1)
// ============================================================================

#[test]
fn json004b_max_safe_int_accepted() {
    // 2^53 - 1 = 9007199254740991
    let result = parse(b"9007199254740991");
    assert!(result.is_ok(), "JSON-004B: MAX_SAFE_INT should be accepted");
    assert_eq!(result.unwrap(), JsonValue::Number(9007199254740991));
}

#[test]
fn json004b_min_safe_int_accepted() {
    // -(2^53 - 1) = -9007199254740991
    let result = parse(b"-9007199254740991");
    assert!(result.is_ok(), "JSON-004B: MIN_SAFE_INT should be accepted");
    assert_eq!(result.unwrap(), JsonValue::Number(-9007199254740991));
}

#[test]
fn json004b_above_max_safe_int_rejected() {
    // 2^53 = 9007199254740992
    let result = parse(b"9007199254740992");
    assert!(
        result.is_err(),
        "JSON-004B: Values above MAX_SAFE_INT should be rejected"
    );
    assert_eq!(result.unwrap_err().code(), 109); // E109_IntegerOutOfRange
}

#[test]
fn json004b_below_min_safe_int_rejected() {
    // -(2^53) = -9007199254740992
    let result = parse(b"-9007199254740992");
    assert!(
        result.is_err(),
        "JSON-004B: Values below MIN_SAFE_INT should be rejected"
    );
    assert_eq!(result.unwrap_err().code(), 109); // E109_IntegerOutOfRange
}

// ============================================================================
// JSON-005: Unescape Before Duplicate Check
// ============================================================================

#[test]
fn json005_escaped_and_unescaped_same_key() {
    // "\u0041" and "A" are the same after unescaping
    let result = parse(br#"{"A": 1, "\u0041": 2}"#);
    assert!(
        result.is_err(),
        "JSON-005: Escaped and unescaped same key should be rejected"
    );
}

#[test]
fn json005_escape_sequences_in_keys() {
    let result = parse(br#"{"a\nb": 1, "a\nb": 2}"#);
    assert!(
        result.is_err(),
        "JSON-005: Duplicate keys with escapes should be rejected"
    );
}

// ============================================================================
// JSON-006: Reject NaN/Infinity Literals
// ============================================================================

#[test]
fn json006_nan_rejected() {
    let result = parse(b"NaN");
    assert!(result.is_err(), "JSON-006: NaN literal should be rejected");
}

#[test]
fn json006_infinity_rejected() {
    let result = parse(b"Infinity");
    assert!(
        result.is_err(),
        "JSON-006: Infinity literal should be rejected"
    );
}

#[test]
fn json006_negative_infinity_rejected() {
    let result = parse(b"-Infinity");
    assert!(
        result.is_err(),
        "JSON-006: -Infinity literal should be rejected"
    );
}

// ============================================================================
// JCS-001..002: UTF-16 Key Comparator
// ============================================================================

#[test]
fn jcs001_keys_sorted_lexicographically() {
    let result = parse(br#"{"b": 2, "a": 1}"#).unwrap();
    let canonical = canonicalize(&result);
    // Keys should be sorted: a before b
    assert_eq!(
        canonical, r#"{"a":1,"b":2}"#,
        "JCS-001: Keys should be sorted"
    );
}

#[test]
fn jcs002_keys_sorted_by_length_then_content() {
    let result = parse(br#"{"aa": 2, "a": 1}"#).unwrap();
    let canonical = canonicalize(&result);
    // "a" < "aa" in UTF-16 ordering
    assert_eq!(
        canonical, r#"{"a":1,"aa":2}"#,
        "JCS-002: Shorter keys first"
    );
}

#[test]
fn jcs002_utf16_code_unit_ordering() {
    // Test that ordering is by UTF-16 code units, not codepoints
    let result = parse(br#"{"z": 1, "A": 2}"#).unwrap();
    let canonical = canonicalize(&result);
    // 'A' (0x41) < 'z' (0x7A) in UTF-16 ordering
    assert_eq!(
        canonical, r#"{"A":2,"z":1}"#,
        "JCS-002: UTF-16 code unit ordering"
    );
}

// ============================================================================
// JCS-003: ECMAScript Number Serialization
// ============================================================================

#[test]
fn jcs003_positive_integer_serialization() {
    let value = JsonValue::Number(42);
    assert_eq!(
        canonicalize(&value),
        "42",
        "JCS-003: Positive integer serialization"
    );
}

#[test]
fn jcs003_negative_integer_serialization() {
    let value = JsonValue::Number(-42);
    assert_eq!(
        canonicalize(&value),
        "-42",
        "JCS-003: Negative integer serialization"
    );
}

#[test]
fn jcs003_zero_serialization() {
    let value = JsonValue::Number(0);
    assert_eq!(canonicalize(&value), "0", "JCS-003: Zero serialization");
}

#[test]
fn jcs003_max_safe_int_serialization() {
    let value = JsonValue::Number(9007199254740991);
    assert_eq!(
        canonicalize(&value),
        "9007199254740991",
        "JCS-003: MAX_SAFE_INT serialization"
    );
}

// ============================================================================
// JCS-004..005: Canonicalization Conformance
// ============================================================================

#[test]
fn jcs004_no_whitespace_in_output() {
    let result = parse(br#"{ "a" : 1 , "b" : 2 }"#).unwrap();
    let canonical = canonicalize(&result);
    assert!(
        !canonical.contains(' '),
        "JCS-004: No whitespace in canonical output"
    );
}

#[test]
fn jcs004_string_escapes() {
    let value = JsonValue::String("a\nb\tc".to_string());
    let canonical = canonicalize(&value);
    assert_eq!(
        canonical, r#""a\nb\tc""#,
        "JCS-004: String escape sequences"
    );
}

#[test]
fn jcs005_nested_object_canonicalization() {
    let input = br#"{"z": {"b": 2, "a": 1}, "y": [3, 2, 1]}"#;
    let result = parse(input).unwrap();
    let canonical = canonicalize(&result);
    // Outer keys sorted, inner object keys sorted, array order preserved
    assert_eq!(
        canonical, r#"{"y":[3,2,1],"z":{"a":1,"b":2}}"#,
        "JCS-005: Nested canonicalization"
    );
}

#[test]
fn jcs005_empty_structures() {
    let empty_obj = JsonValue::Object(BTreeMap::new());
    let empty_arr = JsonValue::Array(vec![]);
    assert_eq!(canonicalize(&empty_obj), "{}", "JCS-005: Empty object");
    assert_eq!(canonicalize(&empty_arr), "[]", "JCS-005: Empty array");
}

#[test]
fn jcs005_deterministic_output() {
    // Same input should always produce same output
    let input = br#"{"c": 3, "a": 1, "b": 2}"#;
    let result1 = parse(input).unwrap();
    let result2 = parse(input).unwrap();
    assert_eq!(
        canonicalize(&result1),
        canonicalize(&result2),
        "JCS-005: Deterministic output"
    );
}

// ============================================================================
// DoS Protection Limits
// ============================================================================

#[test]
fn limit_e110_input_too_large() {
    let mut limits = Limits::consensus();
    limits.max_input_size = 10;
    let result = parse_with_limits(b"this input is too large for the limit", limits);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().code(), 110); // E110_InputTooLarge
}

#[test]
fn limit_e111_nesting_too_deep() {
    let mut limits = Limits::consensus();
    limits.max_nesting_depth = 2;
    let result = parse_with_limits(b"[[[1]]]", limits);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().code(), 111); // E111_NestingTooDeep
}

#[test]
fn limit_e112_string_too_long() {
    let mut limits = Limits::consensus();
    limits.max_string_length = 5;
    let result = parse_with_limits(br#""this string is too long""#, limits);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().code(), 112); // E112_StringTooLong
}

#[test]
fn limit_e113_too_many_fields() {
    let mut limits = Limits::consensus();
    limits.max_object_fields = 2;
    let result = parse_with_limits(br#"{"a": 1, "b": 2, "c": 3}"#, limits);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().code(), 113); // E113_TooManyFields
}

#[test]
fn limit_e114_array_too_long() {
    let mut limits = Limits::consensus();
    limits.max_array_length = 2;
    let result = parse_with_limits(b"[1, 2, 3]", limits);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().code(), 114); // E114_ArrayTooLong
}

#[test]
fn limit_e115_non_ascii_character() {
    // Consensus mode is ASCII-only
    let limits = Limits::consensus();
    let result = parse_with_limits(br#""\u00E9""#, limits); // é (non-ASCII)
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().code(), 115); // E115_NonASCIICharacter
}

#[test]
fn limit_non_ascii_allowed_in_lenient_mode() {
    let mut limits = Limits::lenient();
    limits.ascii_only = false;
    let result = parse_with_limits(br#""\u00E9""#, limits); // é
    assert!(
        result.is_ok(),
        "Non-ASCII should be allowed in lenient mode"
    );
}

// ============================================================================
// Edge Cases
// ============================================================================

#[test]
fn edge_empty_object() {
    let result = parse(b"{}");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), JsonValue::Object(BTreeMap::new()));
}

#[test]
fn edge_empty_array() {
    let result = parse(b"[]");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), JsonValue::Array(vec![]));
}

#[test]
fn edge_empty_string() {
    let result = parse(br#""""#);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), JsonValue::String(String::new()));
}

#[test]
fn edge_null_literal() {
    let result = parse(b"null");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), JsonValue::Null);
}

#[test]
fn edge_true_literal() {
    let result = parse(b"true");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), JsonValue::Bool(true));
}

#[test]
fn edge_false_literal() {
    let result = parse(b"false");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), JsonValue::Bool(false));
}

#[test]
fn edge_trailing_content_rejected() {
    let result = parse(b"null extra");
    assert!(result.is_err(), "Trailing content should be rejected");
}

#[test]
fn edge_trailing_comma_in_array_rejected() {
    let result = parse(b"[1, 2,]");
    assert!(
        result.is_err(),
        "Trailing comma in array should be rejected"
    );
}

#[test]
fn edge_trailing_comma_in_object_rejected() {
    let result = parse(br#"{"a": 1,}"#);
    assert!(
        result.is_err(),
        "Trailing comma in object should be rejected"
    );
}

#[test]
fn edge_control_characters_in_string_rejected() {
    // Tab character (0x09) is a control character
    let input = b"\"a\tb\""; // literal tab, not \t
    let result = parse(input);
    assert!(
        result.is_err(),
        "Control characters in strings should be rejected"
    );
}

#[test]
fn edge_all_escape_sequences() {
    let result = parse(br#""\\\/\b\f\n\r\t""#);
    assert!(result.is_ok());
    let s = result.unwrap();
    assert_eq!(s.as_str().unwrap(), "\\/\x08\x0C\n\r\t");
}
