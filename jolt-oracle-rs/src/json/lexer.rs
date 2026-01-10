//! JSON lexer/tokenizer.
//!
//! Converts raw JSON input bytes into a stream of tokens for the parser.
//! Handles UTF-8 validation, escape sequences, and ASCII-only enforcement.
//!
//! # Requirements
//!
//! - JSON-001: UTF-8 validation
//! - JSON-002: Reject unpaired surrogates
//! - JSON-005: Unescape strings
//! - E115: Non-ASCII character detection

use super::limits::Limits;
use crate::error::ErrorCode;
use crate::OracleResult;

/// Token types produced by the lexer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    /// Left brace `{`
    LeftBrace,
    /// Right brace `}`
    RightBrace,
    /// Left bracket `[`
    LeftBracket,
    /// Right bracket `]`
    RightBracket,
    /// Colon `:`
    Colon,
    /// Comma `,`
    Comma,
    /// Null literal
    Null,
    /// True literal
    True,
    /// False literal
    False,
    /// String value (unescaped)
    String(String),
    /// Number value (as raw string for validation)
    Number(String),
    /// End of input
    Eof,
}

/// JSON lexer that tokenizes input.
pub struct Lexer<'a> {
    input: &'a [u8],
    pos: usize,
    limits: Limits,
}

impl<'a> Lexer<'a> {
    /// Create a new lexer for the given input.
    pub fn new(input: &'a [u8], limits: Limits) -> OracleResult<Self> {
        // Check input size limit (E110)
        if input.len() as u64 > limits.max_input_size {
            return Err(ErrorCode::E110_InputTooLarge(
                input.len() as u64,
                limits.max_input_size,
            ));
        }

        // Validate UTF-8 (JSON-001)
        if std::str::from_utf8(input).is_err() {
            return Err(ErrorCode::E105_InvalidUTF8);
        }

        Ok(Self {
            input,
            pos: 0,
            limits,
        })
    }

    /// Get the current position in the input.
    pub fn position(&self) -> usize {
        self.pos
    }

    /// Peek at the current byte without consuming it.
    fn peek(&self) -> Option<u8> {
        self.input.get(self.pos).copied()
    }

    /// Consume and return the current byte.
    fn advance(&mut self) -> Option<u8> {
        let b = self.input.get(self.pos).copied();
        if b.is_some() {
            self.pos += 1;
        }
        b
    }

    /// Skip whitespace characters.
    fn skip_whitespace(&mut self) {
        while let Some(b) = self.peek() {
            match b {
                b' ' | b'\t' | b'\n' | b'\r' => {
                    self.advance();
                }
                _ => break,
            }
        }
    }

    /// Read the next token from the input.
    pub fn next_token(&mut self) -> OracleResult<Token> {
        self.skip_whitespace();

        match self.peek() {
            None => Ok(Token::Eof),
            Some(b'{') => {
                self.advance();
                Ok(Token::LeftBrace)
            }
            Some(b'}') => {
                self.advance();
                Ok(Token::RightBrace)
            }
            Some(b'[') => {
                self.advance();
                Ok(Token::LeftBracket)
            }
            Some(b']') => {
                self.advance();
                Ok(Token::RightBracket)
            }
            Some(b':') => {
                self.advance();
                Ok(Token::Colon)
            }
            Some(b',') => {
                self.advance();
                Ok(Token::Comma)
            }
            Some(b'"') => self.read_string(),
            Some(b'-') | Some(b'0'..=b'9') => self.read_number(),
            Some(b't') => self.read_true(),
            Some(b'f') => self.read_false(),
            Some(b'n') => self.read_null(),
            Some(_) => Err(ErrorCode::E100_InvalidJSON),
        }
    }

    /// Read a string token, handling escape sequences.
    fn read_string(&mut self) -> OracleResult<Token> {
        // Consume opening quote
        self.advance();

        let mut result = String::new();
        let start_pos = self.pos;

        loop {
            match self.advance() {
                None => return Err(ErrorCode::E100_InvalidJSON),
                Some(b'"') => break,
                Some(b'\\') => {
                    let escaped = self.read_escape_sequence()?;
                    result.push(escaped);
                }
                Some(b) if b < 0x20 => {
                    // Control characters are not allowed in strings
                    return Err(ErrorCode::E100_InvalidJSON);
                }
                Some(b) if b > 0x7F && self.limits.ascii_only => {
                    // Non-ASCII character (E115)
                    return Err(ErrorCode::E115_NonASCIICharacter(b as u64));
                }
                Some(b) if b <= 0x7F => {
                    result.push(b as char);
                }
                Some(_) => {
                    // UTF-8 multi-byte sequence
                    // Back up and read the full UTF-8 character
                    self.pos -= 1;
                    let ch = self.read_utf8_char()?;
                    result.push(ch);
                }
            }

            // Check string length limit (E112)
            if result.len() as u64 > self.limits.max_string_length {
                return Err(ErrorCode::E112_StringTooLong(
                    result.len() as u64,
                    self.limits.max_string_length,
                ));
            }
        }

        // Final string length check
        let byte_len = (self.pos - start_pos - 1) as u64; // -1 for closing quote
        if byte_len > self.limits.max_string_length {
            return Err(ErrorCode::E112_StringTooLong(
                byte_len,
                self.limits.max_string_length,
            ));
        }

        Ok(Token::String(result))
    }

    /// Read a UTF-8 character from the current position.
    fn read_utf8_char(&mut self) -> OracleResult<char> {
        let b0 = self.advance().ok_or(ErrorCode::E105_InvalidUTF8)?;

        // Check for non-ASCII in ASCII-only mode
        if self.limits.ascii_only && b0 > 0x7F {
            return Err(ErrorCode::E115_NonASCIICharacter(b0 as u64));
        }

        if b0 <= 0x7F {
            return Ok(b0 as char);
        }

        // Determine the number of bytes in this UTF-8 sequence
        let (len, mut codepoint) = if b0 & 0xE0 == 0xC0 {
            (2, (b0 & 0x1F) as u32)
        } else if b0 & 0xF0 == 0xE0 {
            (3, (b0 & 0x0F) as u32)
        } else if b0 & 0xF8 == 0xF0 {
            (4, (b0 & 0x07) as u32)
        } else {
            return Err(ErrorCode::E105_InvalidUTF8);
        };

        // Read continuation bytes
        for _ in 1..len {
            let b = self.advance().ok_or(ErrorCode::E105_InvalidUTF8)?;
            if b & 0xC0 != 0x80 {
                return Err(ErrorCode::E105_InvalidUTF8);
            }
            codepoint = (codepoint << 6) | ((b & 0x3F) as u32);
        }

        // Check for surrogate codepoints (JSON-002)
        if (0xD800..=0xDFFF).contains(&codepoint) {
            return Err(ErrorCode::E105_InvalidUTF8);
        }

        char::from_u32(codepoint).ok_or(ErrorCode::E105_InvalidUTF8)
    }

    /// Read an escape sequence after a backslash.
    fn read_escape_sequence(&mut self) -> OracleResult<char> {
        match self.advance() {
            None => Err(ErrorCode::E100_InvalidJSON),
            Some(b'"') => Ok('"'),
            Some(b'\\') => Ok('\\'),
            Some(b'/') => Ok('/'),
            Some(b'b') => Ok('\x08'),
            Some(b'f') => Ok('\x0C'),
            Some(b'n') => Ok('\n'),
            Some(b'r') => Ok('\r'),
            Some(b't') => Ok('\t'),
            Some(b'u') => self.read_unicode_escape(),
            Some(_) => Err(ErrorCode::E100_InvalidJSON),
        }
    }

    /// Read a \uXXXX unicode escape sequence.
    fn read_unicode_escape(&mut self) -> OracleResult<char> {
        let codepoint = self.read_hex4()?;

        // Check if this is a high surrogate (JSON-002)
        if (0xD800..=0xDBFF).contains(&codepoint) {
            // Must be followed by \uXXXX low surrogate
            if self.advance() != Some(b'\\') || self.advance() != Some(b'u') {
                // Unpaired high surrogate
                return Err(ErrorCode::E105_InvalidUTF8);
            }
            let low = self.read_hex4()?;
            if !(0xDC00..=0xDFFF).contains(&low) {
                // Not a valid low surrogate
                return Err(ErrorCode::E105_InvalidUTF8);
            }
            // Combine surrogates into codepoint
            let combined = 0x10000 + ((codepoint as u32 - 0xD800) << 10) + (low as u32 - 0xDC00);
            let ch = char::from_u32(combined).ok_or(ErrorCode::E105_InvalidUTF8)?;

            // Check ASCII-only mode
            if self.limits.ascii_only {
                return Err(ErrorCode::E115_NonASCIICharacter(combined as u64));
            }

            return Ok(ch);
        }

        // Check for unpaired low surrogate
        if (0xDC00..=0xDFFF).contains(&codepoint) {
            return Err(ErrorCode::E105_InvalidUTF8);
        }

        let ch = char::from_u32(codepoint as u32).ok_or(ErrorCode::E105_InvalidUTF8)?;

        // Check ASCII-only mode for non-ASCII codepoints
        if self.limits.ascii_only && codepoint > 0x7F {
            return Err(ErrorCode::E115_NonASCIICharacter(codepoint as u64));
        }

        Ok(ch)
    }

    /// Read 4 hex digits and return the value.
    fn read_hex4(&mut self) -> OracleResult<u16> {
        let mut value: u16 = 0;
        for _ in 0..4 {
            let b = self.advance().ok_or(ErrorCode::E100_InvalidJSON)?;
            let digit = match b {
                b'0'..=b'9' => b - b'0',
                b'a'..=b'f' => b - b'a' + 10,
                b'A'..=b'F' => b - b'A' + 10,
                _ => return Err(ErrorCode::E100_InvalidJSON),
            };
            value = (value << 4) | (digit as u16);
        }
        Ok(value)
    }

    /// Read a number token.
    fn read_number(&mut self) -> OracleResult<Token> {
        let start = self.pos;

        // Optional minus sign
        if self.peek() == Some(b'-') {
            self.advance();
        }

        // Integer part
        match self.peek() {
            Some(b'0') => {
                self.advance();
                // After leading zero, must not have more digits
                if let Some(b'0'..=b'9') = self.peek() {
                    return Err(ErrorCode::E100_InvalidJSON);
                }
            }
            Some(b'1'..=b'9') => {
                self.advance();
                while let Some(b'0'..=b'9') = self.peek() {
                    self.advance();
                }
            }
            _ => return Err(ErrorCode::E100_InvalidJSON),
        }

        // Fractional part (not allowed in I-JSON consensus mode)
        if self.peek() == Some(b'.') {
            return Err(ErrorCode::E108_FractionalNumber);
        }

        // Exponent (not allowed in I-JSON consensus mode)
        if let Some(b'e') | Some(b'E') = self.peek() {
            return Err(ErrorCode::E107_ExponentNotation);
        }

        let num_str = std::str::from_utf8(&self.input[start..self.pos])
            .map_err(|_| ErrorCode::E100_InvalidJSON)?;

        Ok(Token::Number(num_str.to_string()))
    }

    /// Read the 'true' literal.
    fn read_true(&mut self) -> OracleResult<Token> {
        self.expect_bytes(b"true")?;
        Ok(Token::True)
    }

    /// Read the 'false' literal.
    fn read_false(&mut self) -> OracleResult<Token> {
        self.expect_bytes(b"false")?;
        Ok(Token::False)
    }

    /// Read the 'null' literal.
    fn read_null(&mut self) -> OracleResult<Token> {
        self.expect_bytes(b"null")?;
        Ok(Token::Null)
    }

    /// Expect specific bytes at the current position.
    fn expect_bytes(&mut self, expected: &[u8]) -> OracleResult<()> {
        for &b in expected {
            if self.advance() != Some(b) {
                return Err(ErrorCode::E100_InvalidJSON);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(input: &str) -> OracleResult<Vec<Token>> {
        let mut lexer = Lexer::new(input.as_bytes(), Limits::lenient())?;
        let mut tokens = Vec::new();
        loop {
            let token = lexer.next_token()?;
            if token == Token::Eof {
                break;
            }
            tokens.push(token);
        }
        Ok(tokens)
    }

    #[test]
    fn test_structural_tokens() {
        let tokens = lex("{}[],:").unwrap();
        assert_eq!(
            tokens,
            vec![
                Token::LeftBrace,
                Token::RightBrace,
                Token::LeftBracket,
                Token::RightBracket,
                Token::Comma,
                Token::Colon,
            ]
        );
    }

    #[test]
    fn test_literals() {
        let tokens = lex("null true false").unwrap();
        assert_eq!(tokens, vec![Token::Null, Token::True, Token::False]);
    }

    #[test]
    fn test_string() {
        let tokens = lex(r#""hello""#).unwrap();
        assert_eq!(tokens, vec![Token::String("hello".to_string())]);
    }

    #[test]
    fn test_string_escapes() {
        let tokens = lex(r#""a\nb\tc""#).unwrap();
        assert_eq!(tokens, vec![Token::String("a\nb\tc".to_string())]);
    }

    #[test]
    fn test_unicode_escape() {
        let mut lexer = Lexer::new(r#""\u0041""#.as_bytes(), Limits::lenient()).unwrap();
        let token = lexer.next_token().unwrap();
        assert_eq!(token, Token::String("A".to_string()));
    }

    #[test]
    fn test_number() {
        let tokens = lex("42 -123 0").unwrap();
        assert_eq!(
            tokens,
            vec![
                Token::Number("42".to_string()),
                Token::Number("-123".to_string()),
                Token::Number("0".to_string()),
            ]
        );
    }

    #[test]
    fn test_fractional_rejected() {
        let result = lex("3.14");
        assert!(result.is_err());
        if let Err(e) = result {
            assert_eq!(e.code(), 108); // E108_FractionalNumber
        }
    }

    #[test]
    fn test_exponent_rejected() {
        let result = lex("1e10");
        assert!(result.is_err());
        if let Err(e) = result {
            assert_eq!(e.code(), 107); // E107_ExponentNotation
        }
    }

    #[test]
    fn test_invalid_utf8() {
        let invalid = vec![0xFF, 0xFE];
        let result = Lexer::new(&invalid, Limits::consensus());
        assert!(result.is_err());
    }

    #[test]
    fn test_input_too_large() {
        let mut limits = Limits::consensus();
        limits.max_input_size = 10;
        let result = Lexer::new(b"this is more than 10 bytes", limits);
        assert!(result.is_err());
    }
}
