//! JSON value types for the Jolt Oracle.
//!
//! This module provides the core JSON data types matching the Lean specification.
//! All types are designed for consensus-critical parsing where determinism is essential.
//!
//! # Requirements
//!
//! - JSON values must support exact structural equality
//! - Object keys are ordered (BTreeMap for determinism)
//! - Numbers are stored as validated i64 within safe integer bounds

use std::collections::BTreeMap;

/// A JSON value matching the Lean JsonValue inductive type.
///
/// All variants are immutable and implement structural equality.
/// Objects use BTreeMap for deterministic key ordering in canonicalization.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum JsonValue {
    /// JSON null literal
    #[default]
    Null,
    /// JSON boolean (true/false)
    Bool(bool),
    /// JSON number as validated i64 within ±(2^53-1) bounds
    Number(i64),
    /// JSON string (validated UTF-8, ASCII-only in strict mode)
    String(String),
    /// JSON array of values
    Array(Vec<JsonValue>),
    /// JSON object with ordered keys (BTreeMap for determinism)
    Object(BTreeMap<String, JsonValue>),
}

impl JsonValue {
    /// Returns true if this is a null value.
    pub fn is_null(&self) -> bool {
        matches!(self, JsonValue::Null)
    }

    /// Returns true if this is a boolean value.
    pub fn is_bool(&self) -> bool {
        matches!(self, JsonValue::Bool(_))
    }

    /// Returns true if this is a number value.
    pub fn is_number(&self) -> bool {
        matches!(self, JsonValue::Number(_))
    }

    /// Returns true if this is a string value.
    pub fn is_string(&self) -> bool {
        matches!(self, JsonValue::String(_))
    }

    /// Returns true if this is an array value.
    pub fn is_array(&self) -> bool {
        matches!(self, JsonValue::Array(_))
    }

    /// Returns true if this is an object value.
    pub fn is_object(&self) -> bool {
        matches!(self, JsonValue::Object(_))
    }

    /// Returns the boolean value if this is a Bool, None otherwise.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            JsonValue::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Returns the number value if this is a Number, None otherwise.
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            JsonValue::Number(n) => Some(*n),
            _ => None,
        }
    }

    /// Returns a reference to the string if this is a String, None otherwise.
    pub fn as_str(&self) -> Option<&str> {
        match self {
            JsonValue::String(s) => Some(s),
            _ => None,
        }
    }

    /// Returns a reference to the array if this is an Array, None otherwise.
    pub fn as_array(&self) -> Option<&Vec<JsonValue>> {
        match self {
            JsonValue::Array(a) => Some(a),
            _ => None,
        }
    }

    /// Returns a reference to the object if this is an Object, None otherwise.
    pub fn as_object(&self) -> Option<&BTreeMap<String, JsonValue>> {
        match self {
            JsonValue::Object(o) => Some(o),
            _ => None,
        }
    }

    /// Get a value from an object by key.
    pub fn get(&self, key: &str) -> Option<&JsonValue> {
        match self {
            JsonValue::Object(map) => map.get(key),
            _ => None,
        }
    }

    /// Get a value from an array by index.
    pub fn get_index(&self, index: usize) -> Option<&JsonValue> {
        match self {
            JsonValue::Array(arr) => arr.get(index),
            _ => None,
        }
    }

    /// Returns the type name as a string for error messages.
    pub fn type_name(&self) -> &'static str {
        match self {
            JsonValue::Null => "null",
            JsonValue::Bool(_) => "boolean",
            JsonValue::Number(_) => "number",
            JsonValue::String(_) => "string",
            JsonValue::Array(_) => "array",
            JsonValue::Object(_) => "object",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_json_value_types() {
        assert!(JsonValue::Null.is_null());
        assert!(JsonValue::Bool(true).is_bool());
        assert!(JsonValue::Number(42).is_number());
        assert!(JsonValue::String("test".to_string()).is_string());
        assert!(JsonValue::Array(vec![]).is_array());
        assert!(JsonValue::Object(BTreeMap::new()).is_object());
    }

    #[test]
    fn test_json_value_accessors() {
        assert_eq!(JsonValue::Bool(true).as_bool(), Some(true));
        assert_eq!(JsonValue::Number(42).as_i64(), Some(42));
        assert_eq!(JsonValue::String("test".to_string()).as_str(), Some("test"));
    }

    #[test]
    fn test_json_value_equality() {
        let obj1: BTreeMap<String, JsonValue> = [("a".to_string(), JsonValue::Number(1))]
            .into_iter()
            .collect();
        let obj2: BTreeMap<String, JsonValue> = [("a".to_string(), JsonValue::Number(1))]
            .into_iter()
            .collect();
        assert_eq!(JsonValue::Object(obj1), JsonValue::Object(obj2));
    }

    #[test]
    fn test_type_names() {
        assert_eq!(JsonValue::Null.type_name(), "null");
        assert_eq!(JsonValue::Bool(false).type_name(), "boolean");
        assert_eq!(JsonValue::Number(0).type_name(), "number");
        assert_eq!(JsonValue::String(String::new()).type_name(), "string");
        assert_eq!(JsonValue::Array(vec![]).type_name(), "array");
        assert_eq!(JsonValue::Object(BTreeMap::new()).type_name(), "object");
    }
}
