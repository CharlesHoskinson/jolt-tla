//! JSON parser with strict validation.
//!
//! Recursive descent parser that validates JSON according to I-JSON (RFC 7493)
//! with additional consensus-critical constraints.
//!
//! # Requirements
//!
//! - JSON-003: Reject duplicate keys after unescaping
//! - JSON-004B: Integer bounds validation (±2^53-1)
//! - E111: Nesting depth limit
//! - E113: Object field count limit
//! - E114: Array length limit

use std::collections::BTreeMap;

use super::lexer::{Lexer, Token};
use super::limits::{Limits, MAX_SAFE_INT, MIN_SAFE_INT};
use super::types::JsonValue;
use crate::error::ErrorCode;
use crate::OracleResult;

/// JSON parser with strict validation.
pub struct Parser<'a> {
    lexer: Lexer<'a>,
    current: Token,
    limits: Limits,
    depth: u64,
}

impl<'a> Parser<'a> {
    /// Create a new parser for the given input.
    pub fn new(input: &'a [u8], limits: Limits) -> OracleResult<Self> {
        let mut lexer = Lexer::new(input, limits)?;
        let current = lexer.next_token()?;
        Ok(Self {
            lexer,
            current,
            limits,
            depth: 0,
        })
    }

    /// Parse the input and return a JsonValue.
    pub fn parse(&mut self) -> OracleResult<JsonValue> {
        let value = self.parse_value()?;

        // Ensure no trailing content
        if self.current != Token::Eof {
            return Err(ErrorCode::E100_InvalidJSON);
        }

        Ok(value)
    }

    /// Advance to the next token.
    fn advance(&mut self) -> OracleResult<()> {
        self.current = self.lexer.next_token()?;
        Ok(())
    }

    /// Parse a single JSON value.
    fn parse_value(&mut self) -> OracleResult<JsonValue> {
        match &self.current {
            Token::Null => {
                self.advance()?;
                Ok(JsonValue::Null)
            }
            Token::True => {
                self.advance()?;
                Ok(JsonValue::Bool(true))
            }
            Token::False => {
                self.advance()?;
                Ok(JsonValue::Bool(false))
            }
            Token::String(s) => {
                let value = JsonValue::String(s.clone());
                self.advance()?;
                Ok(value)
            }
            Token::Number(s) => {
                let value = self.parse_number(s)?;
                self.advance()?;
                Ok(value)
            }
            Token::LeftBrace => self.parse_object(),
            Token::LeftBracket => self.parse_array(),
            Token::Eof => Err(ErrorCode::E100_InvalidJSON),
            _ => Err(ErrorCode::E100_InvalidJSON),
        }
    }

    /// Parse a number token into a JsonValue.
    fn parse_number(&self, s: &str) -> OracleResult<JsonValue> {
        // Parse as i64
        let value: i64 = s.parse().map_err(|_| ErrorCode::E109_IntegerOutOfRange)?;

        // Check safe integer bounds (JSON-004B)
        if !(MIN_SAFE_INT..=MAX_SAFE_INT).contains(&value) {
            return Err(ErrorCode::E109_IntegerOutOfRange);
        }

        Ok(JsonValue::Number(value))
    }

    /// Parse a JSON object.
    fn parse_object(&mut self) -> OracleResult<JsonValue> {
        // Check nesting depth (E111)
        self.depth += 1;
        if self.depth > self.limits.max_nesting_depth {
            return Err(ErrorCode::E111_NestingTooDeep(
                self.depth,
                self.limits.max_nesting_depth,
            ));
        }

        // Consume opening brace
        self.advance()?;

        let mut map = BTreeMap::new();
        let mut field_count: u64 = 0;

        // Empty object
        if self.current == Token::RightBrace {
            self.advance()?;
            self.depth -= 1;
            return Ok(JsonValue::Object(map));
        }

        loop {
            // Expect string key
            let key = match &self.current {
                Token::String(s) => s.clone(),
                _ => return Err(ErrorCode::E100_InvalidJSON),
            };
            self.advance()?;

            // Check for duplicate key (JSON-003)
            if map.contains_key(&key) {
                return Err(ErrorCode::E101_DuplicateKey(key));
            }

            // Expect colon
            if self.current != Token::Colon {
                return Err(ErrorCode::E100_InvalidJSON);
            }
            self.advance()?;

            // Parse value
            let value = self.parse_value()?;
            map.insert(key, value);
            field_count += 1;

            // Check field count limit (E113)
            if field_count > self.limits.max_object_fields {
                return Err(ErrorCode::E113_TooManyFields(
                    field_count,
                    self.limits.max_object_fields,
                ));
            }

            // Expect comma or closing brace
            match &self.current {
                Token::Comma => {
                    self.advance()?;
                    // Trailing comma is not allowed in JSON
                    if self.current == Token::RightBrace {
                        return Err(ErrorCode::E100_InvalidJSON);
                    }
                }
                Token::RightBrace => {
                    self.advance()?;
                    break;
                }
                _ => return Err(ErrorCode::E100_InvalidJSON),
            }
        }

        self.depth -= 1;
        Ok(JsonValue::Object(map))
    }

    /// Parse a JSON array.
    fn parse_array(&mut self) -> OracleResult<JsonValue> {
        // Check nesting depth (E111)
        self.depth += 1;
        if self.depth > self.limits.max_nesting_depth {
            return Err(ErrorCode::E111_NestingTooDeep(
                self.depth,
                self.limits.max_nesting_depth,
            ));
        }

        // Consume opening bracket
        self.advance()?;

        let mut arr = Vec::new();

        // Empty array
        if self.current == Token::RightBracket {
            self.advance()?;
            self.depth -= 1;
            return Ok(JsonValue::Array(arr));
        }

        loop {
            let value = self.parse_value()?;
            arr.push(value);

            // Check array length limit (E114)
            if arr.len() as u64 > self.limits.max_array_length {
                return Err(ErrorCode::E114_ArrayTooLong(
                    arr.len() as u64,
                    self.limits.max_array_length,
                ));
            }

            // Expect comma or closing bracket
            match &self.current {
                Token::Comma => {
                    self.advance()?;
                    // Trailing comma is not allowed in JSON
                    if self.current == Token::RightBracket {
                        return Err(ErrorCode::E100_InvalidJSON);
                    }
                }
                Token::RightBracket => {
                    self.advance()?;
                    break;
                }
                _ => return Err(ErrorCode::E100_InvalidJSON),
            }
        }

        self.depth -= 1;
        Ok(JsonValue::Array(arr))
    }
}

/// Parse a JSON string into a JsonValue with consensus limits.
pub fn parse(input: &[u8]) -> OracleResult<JsonValue> {
    parse_with_limits(input, Limits::consensus())
}

/// Parse a JSON string into a JsonValue with custom limits.
pub fn parse_with_limits(input: &[u8], limits: Limits) -> OracleResult<JsonValue> {
    let mut parser = Parser::new(input, limits)?;
    parser.parse()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_lenient(input: &str) -> OracleResult<JsonValue> {
        parse_with_limits(input.as_bytes(), Limits::lenient())
    }

    #[test]
    fn test_parse_null() {
        let result = parse_lenient("null").unwrap();
        assert_eq!(result, JsonValue::Null);
    }

    #[test]
    fn test_parse_booleans() {
        assert_eq!(parse_lenient("true").unwrap(), JsonValue::Bool(true));
        assert_eq!(parse_lenient("false").unwrap(), JsonValue::Bool(false));
    }

    #[test]
    fn test_parse_number() {
        assert_eq!(parse_lenient("42").unwrap(), JsonValue::Number(42));
        assert_eq!(parse_lenient("-123").unwrap(), JsonValue::Number(-123));
        assert_eq!(parse_lenient("0").unwrap(), JsonValue::Number(0));
    }

    #[test]
    fn test_parse_string() {
        assert_eq!(
            parse_lenient(r#""hello""#).unwrap(),
            JsonValue::String("hello".to_string())
        );
    }

    #[test]
    fn test_parse_array() {
        let result = parse_lenient("[1, 2, 3]").unwrap();
        assert_eq!(
            result,
            JsonValue::Array(vec![
                JsonValue::Number(1),
                JsonValue::Number(2),
                JsonValue::Number(3),
            ])
        );
    }

    #[test]
    fn test_parse_object() {
        let result = parse_lenient(r#"{"a": 1, "b": 2}"#).unwrap();
        let mut expected = BTreeMap::new();
        expected.insert("a".to_string(), JsonValue::Number(1));
        expected.insert("b".to_string(), JsonValue::Number(2));
        assert_eq!(result, JsonValue::Object(expected));
    }

    #[test]
    fn test_duplicate_key_rejected() {
        let result = parse_lenient(r#"{"a": 1, "a": 2}"#);
        assert!(result.is_err());
        if let Err(e) = result {
            assert_eq!(e.code(), 101); // E101_DuplicateKey
        }
    }

    #[test]
    fn test_integer_out_of_range() {
        // 2^53 is out of range
        let result = parse_lenient("9007199254740992");
        assert!(result.is_err());
        if let Err(e) = result {
            assert_eq!(e.code(), 109); // E109_IntegerOutOfRange
        }
    }

    #[test]
    fn test_max_safe_integer() {
        // 2^53 - 1 is valid
        let result = parse_lenient("9007199254740991").unwrap();
        assert_eq!(result, JsonValue::Number(9007199254740991));
    }

    #[test]
    fn test_nesting_depth_limit() {
        let mut limits = Limits::consensus();
        limits.max_nesting_depth = 2;

        // Depth 2 is allowed
        let result = parse_with_limits(b"[[1]]", limits);
        assert!(result.is_ok());

        // Depth 3 exceeds limit
        let result = parse_with_limits(b"[[[1]]]", limits);
        assert!(result.is_err());
    }

    #[test]
    fn test_object_field_limit() {
        let mut limits = Limits::lenient();
        limits.max_object_fields = 2;

        let result = parse_with_limits(br#"{"a": 1, "b": 2, "c": 3}"#, limits);
        assert!(result.is_err());
        if let Err(e) = result {
            assert_eq!(e.code(), 113); // E113_TooManyFields
        }
    }

    #[test]
    fn test_array_length_limit() {
        let mut limits = Limits::lenient();
        limits.max_array_length = 2;

        let result = parse_with_limits(b"[1, 2, 3]", limits);
        assert!(result.is_err());
        if let Err(e) = result {
            assert_eq!(e.code(), 114); // E114_ArrayTooLong
        }
    }

    #[test]
    fn test_trailing_content_rejected() {
        let result = parse_lenient("null extra");
        assert!(result.is_err());
    }

    #[test]
    fn test_trailing_comma_rejected() {
        let result = parse_lenient("[1, 2,]");
        assert!(result.is_err());
    }

    #[test]
    fn test_nested_structure() {
        let result = parse_lenient(r#"{"arr": [1, {"nested": true}], "num": 42}"#).unwrap();
        assert!(result.is_object());
        let arr = result.get("arr").unwrap();
        assert!(arr.is_array());
    }
}
