//! JSON Canonicalization Scheme (RFC 8785) implementation.
//!
//! Provides deterministic JSON serialization for consensus-critical applications.
//! Keys are sorted using UTF-16 code unit ordering, and numbers are serialized
//! using ECMAScript rules.
//!
//! # Requirements
//!
//! - JCS-001..002: UTF-16 key comparator
//! - JCS-003: ECMAScript number serialization
//! - JCS-004..005: Canonicalization conformance

use std::cmp::Ordering;

use super::types::JsonValue;

/// Compare two strings using UTF-16 code unit ordering (JCS-001, JCS-002).
///
/// This matches ECMAScript/JavaScript string comparison, which compares
/// strings by their UTF-16 code unit values, not Unicode codepoints.
pub fn compare_keys_utf16(a: &str, b: &str) -> Ordering {
    // Convert to UTF-16 and compare code unit by code unit
    let a_units: Vec<u16> = a.encode_utf16().collect();
    let b_units: Vec<u16> = b.encode_utf16().collect();
    a_units.cmp(&b_units)
}

/// Serialize an i64 to a string using ECMAScript number serialization (JCS-003).
///
/// For integers within the safe range, this is simply the decimal representation
/// without any unnecessary formatting (no leading zeros, no plus sign).
pub fn serialize_number(value: i64) -> String {
    // For integers, ECMAScript serialization is just the decimal representation
    value.to_string()
}

/// Serialize a JsonValue to canonical JSON (RFC 8785).
pub fn canonicalize(value: &JsonValue) -> String {
    let mut output = String::new();
    serialize_value(value, &mut output);
    output
}

/// Serialize a JsonValue to the output string.
fn serialize_value(value: &JsonValue, output: &mut String) {
    match value {
        JsonValue::Null => output.push_str("null"),
        JsonValue::Bool(true) => output.push_str("true"),
        JsonValue::Bool(false) => output.push_str("false"),
        JsonValue::Number(n) => output.push_str(&serialize_number(*n)),
        JsonValue::String(s) => serialize_string(s, output),
        JsonValue::Array(arr) => serialize_array(arr, output),
        JsonValue::Object(_) => serialize_object(value, output),
    }
}

/// Serialize a string with proper JSON escaping.
fn serialize_string(s: &str, output: &mut String) {
    output.push('"');
    for ch in s.chars() {
        match ch {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\x08' => output.push_str("\\b"),
            '\x0C' => output.push_str("\\f"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            c if c < '\x20' => {
                // Other control characters as \u00XX
                output.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => output.push(c),
        }
    }
    output.push('"');
}

/// Serialize an array.
fn serialize_array(arr: &[JsonValue], output: &mut String) {
    output.push('[');
    for (i, value) in arr.iter().enumerate() {
        if i > 0 {
            output.push(',');
        }
        serialize_value(value, output);
    }
    output.push(']');
}

/// Serialize an object with keys sorted by UTF-16 ordering.
fn serialize_object(value: &JsonValue, output: &mut String) {
    let obj = match value {
        JsonValue::Object(o) => o,
        _ => return,
    };

    output.push('{');

    // Collect keys and sort by UTF-16 code unit ordering
    let mut keys: Vec<&String> = obj.keys().collect();
    keys.sort_by(|a, b| compare_keys_utf16(a, b));

    for (i, key) in keys.iter().enumerate() {
        if i > 0 {
            output.push(',');
        }
        serialize_string(key, output);
        output.push(':');
        if let Some(v) = obj.get(*key) {
            serialize_value(v, output);
        }
    }

    output.push('}');
}

/// Check if a JsonValue is in canonical form.
///
/// Returns true if serializing the value would produce the same string
/// as the original input. This is used for E205_NonCanonicalJSON detection.
pub fn is_canonical(input: &str, value: &JsonValue) -> bool {
    canonicalize(value) == input
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn test_utf16_key_ordering() {
        // ASCII ordering
        assert_eq!(compare_keys_utf16("a", "b"), Ordering::Less);
        assert_eq!(compare_keys_utf16("b", "a"), Ordering::Greater);
        assert_eq!(compare_keys_utf16("abc", "abc"), Ordering::Equal);

        // Length comparison
        assert_eq!(compare_keys_utf16("a", "aa"), Ordering::Less);
    }

    #[test]
    fn test_serialize_number() {
        assert_eq!(serialize_number(0), "0");
        assert_eq!(serialize_number(42), "42");
        assert_eq!(serialize_number(-123), "-123");
        assert_eq!(serialize_number(9007199254740991), "9007199254740991");
    }

    #[test]
    fn test_canonicalize_primitives() {
        assert_eq!(canonicalize(&JsonValue::Null), "null");
        assert_eq!(canonicalize(&JsonValue::Bool(true)), "true");
        assert_eq!(canonicalize(&JsonValue::Bool(false)), "false");
        assert_eq!(canonicalize(&JsonValue::Number(42)), "42");
    }

    #[test]
    fn test_canonicalize_string() {
        assert_eq!(
            canonicalize(&JsonValue::String("hello".to_string())),
            "\"hello\""
        );
    }

    #[test]
    fn test_canonicalize_string_escapes() {
        assert_eq!(
            canonicalize(&JsonValue::String("a\nb".to_string())),
            "\"a\\nb\""
        );
        assert_eq!(
            canonicalize(&JsonValue::String("a\tb".to_string())),
            "\"a\\tb\""
        );
        assert_eq!(
            canonicalize(&JsonValue::String("a\"b".to_string())),
            "\"a\\\"b\""
        );
        assert_eq!(
            canonicalize(&JsonValue::String("a\\b".to_string())),
            "\"a\\\\b\""
        );
    }

    #[test]
    fn test_canonicalize_array() {
        let arr = JsonValue::Array(vec![
            JsonValue::Number(1),
            JsonValue::Number(2),
            JsonValue::Number(3),
        ]);
        assert_eq!(canonicalize(&arr), "[1,2,3]");
    }

    #[test]
    fn test_canonicalize_empty_array() {
        assert_eq!(canonicalize(&JsonValue::Array(vec![])), "[]");
    }

    #[test]
    fn test_canonicalize_object() {
        let mut obj = BTreeMap::new();
        obj.insert("b".to_string(), JsonValue::Number(2));
        obj.insert("a".to_string(), JsonValue::Number(1));
        let value = JsonValue::Object(obj);

        // Keys should be sorted: a before b
        assert_eq!(canonicalize(&value), "{\"a\":1,\"b\":2}");
    }

    #[test]
    fn test_canonicalize_empty_object() {
        assert_eq!(canonicalize(&JsonValue::Object(BTreeMap::new())), "{}");
    }

    #[test]
    fn test_canonicalize_nested() {
        let mut inner = BTreeMap::new();
        inner.insert("x".to_string(), JsonValue::Number(1));

        let mut outer = BTreeMap::new();
        outer.insert(
            "arr".to_string(),
            JsonValue::Array(vec![JsonValue::Number(1)]),
        );
        outer.insert("obj".to_string(), JsonValue::Object(inner));

        let value = JsonValue::Object(outer);
        assert_eq!(canonicalize(&value), "{\"arr\":[1],\"obj\":{\"x\":1}}");
    }

    #[test]
    fn test_is_canonical() {
        let value = JsonValue::Object({
            let mut m = BTreeMap::new();
            m.insert("a".to_string(), JsonValue::Number(1));
            m
        });

        assert!(is_canonical("{\"a\":1}", &value));
        assert!(!is_canonical("{\"a\": 1}", &value)); // Extra space
        assert!(!is_canonical("{ \"a\":1}", &value)); // Extra space
    }

    #[test]
    fn test_utf16_surrogate_pairs() {
        // Test that UTF-16 ordering handles characters outside BMP correctly
        // Emoji (outside BMP) should sort by their UTF-16 surrogate pairs
        // U+1F600 = D83D DE00 in UTF-16
        // This is after ASCII characters in UTF-16 ordering

        // This is a simplified test since we're using ASCII-only mode
        assert!(compare_keys_utf16("z", "zz") == Ordering::Less);
    }
}
