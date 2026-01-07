/-!
# JSON Lexer

Custom JSON lexer that preserves raw number strings.

## Main Definitions
* `Token` - JSON token type
* `lexJSON` - Tokenize JSON bytes

## Implementation Notes
Standard JSON parsers normalize numbers (losing lexical form) and silently
deduplicate keys. The spec requires detecting:
- Exponent notation (e.g., 1e10)
- Fractional numbers (e.g., 1.5)
- Duplicate keys

We preserve the raw string representation of numbers for validation.

## References
* Jolt Spec §2.3
-/

import Jolt.Errors

namespace Jolt.JSON

/-- JSON token type with raw number preservation. -/
inductive Token where
  | lbrace    -- {
  | rbrace    -- }
  | lbracket  -- [
  | rbracket  -- ]
  | colon     -- :
  | comma     -- ,
  | string (s : String)
  | number (raw : String) (value : Int)
  | true_
  | false_
  | null_
  deriving Repr, DecidableEq

/-- Lexer state. -/
structure LexerState where
  bytes : ByteArray
  pos : Nat
  deriving Repr

namespace LexerState

def peek (s : LexerState) : Option UInt8 :=
  if s.pos < s.bytes.size then some s.bytes[s.pos]! else none

def advance (s : LexerState) : LexerState :=
  { s with pos := s.pos + 1 }

def peekChar (s : LexerState) : Option Char :=
  s.peek.map (·.toNat.toUInt32.toChar)

def isEOF (s : LexerState) : Bool := s.pos ≥ s.bytes.size

def skipWhitespace (s : LexerState) : LexerState := Id.run do
  let mut st := s
  while !st.isEOF do
    match st.peek with
    | some 0x20 | some 0x09 | some 0x0A | some 0x0D => st := st.advance
    | _ => break
  return st

end LexerState

/-- Parse a JSON string literal (after opening quote). -/
private def parseString (s : LexerState) : OracleResult (String × LexerState) := do
  let mut st := s
  let mut result := ""
  while !st.isEOF do
    match st.peek with
    | some 0x22 => -- closing quote
      return (result, st.advance)
    | some 0x5C => -- backslash escape
      st := st.advance
      match st.peek with
      | some 0x22 => result := result.push '"'; st := st.advance
      | some 0x5C => result := result.push '\\'; st := st.advance
      | some 0x2F => result := result.push '/'; st := st.advance
      | some 0x62 => result := result.push '\x08'; st := st.advance
      | some 0x66 => result := result.push '\x0C'; st := st.advance
      | some 0x6E => result := result.push '\n'; st := st.advance
      | some 0x72 => result := result.push '\r'; st := st.advance
      | some 0x74 => result := result.push '\t'; st := st.advance
      | some 0x75 => -- \uXXXX
        st := st.advance
        if st.pos + 4 > st.bytes.size then throw ErrorCode.E100_InvalidJSON
        let mut codepoint : UInt32 := 0
        for _ in [:4] do
          let b := st.bytes[st.pos]!
          let digit := if b >= 0x30 && b <= 0x39 then b - 0x30
                       else if b >= 0x41 && b <= 0x46 then b - 0x41 + 10
                       else if b >= 0x61 && b <= 0x66 then b - 0x61 + 10
                       else 255
          if digit > 15 then throw ErrorCode.E100_InvalidJSON
          codepoint := codepoint * 16 + digit.toUInt32
          st := st.advance
        result := result.push (Char.ofNat codepoint.toNat)
      | _ => throw ErrorCode.E100_InvalidJSON
    | some b =>
      if b < 0x20 then throw ErrorCode.E100_InvalidJSON  -- control chars not allowed
      result := result.push (Char.ofNat b.toNat)
      st := st.advance
    | none => throw ErrorCode.E100_InvalidJSON
  throw ErrorCode.E100_InvalidJSON  -- unterminated string

/-- Parse a JSON number (raw string preserved). -/
private def parseNumber (s : LexerState) : OracleResult (String × Int × LexerState) := do
  let mut st := s
  let mut raw := ""
  let mut negative := false

  -- Optional minus
  if st.peek == some 0x2D then
    negative := true
    raw := raw.push '-'
    st := st.advance

  -- Integer part
  match st.peek with
  | some 0x30 =>  -- leading zero
    raw := raw.push '0'
    st := st.advance
  | some b =>
    if b >= 0x31 && b <= 0x39 then
      while !st.isEOF do
        match st.peek with
        | some d => if d >= 0x30 && d <= 0x39 then
                      raw := raw.push (Char.ofNat d.toNat)
                      st := st.advance
                    else break
        | none => break
    else throw ErrorCode.E100_InvalidJSON
  | none => throw ErrorCode.E100_InvalidJSON

  -- Fractional part (optional)
  if st.peek == some 0x2E then
    raw := raw.push '.'
    st := st.advance
    let startFrac := raw.length
    while !st.isEOF do
      match st.peek with
      | some d => if d >= 0x30 && d <= 0x39 then
                    raw := raw.push (Char.ofNat d.toNat)
                    st := st.advance
                  else break
      | none => break
    if raw.length == startFrac then throw ErrorCode.E100_InvalidJSON

  -- Exponent (optional)
  if st.peek == some 0x65 || st.peek == some 0x45 then
    raw := raw.push (Char.ofNat st.peek.get!.toNat)
    st := st.advance
    if st.peek == some 0x2B || st.peek == some 0x2D then
      raw := raw.push (Char.ofNat st.peek.get!.toNat)
      st := st.advance
    let startExp := raw.length
    while !st.isEOF do
      match st.peek with
      | some d => if d >= 0x30 && d <= 0x39 then
                    raw := raw.push (Char.ofNat d.toNat)
                    st := st.advance
                  else break
      | none => break
    if raw.length == startExp then throw ErrorCode.E100_InvalidJSON

  -- Parse value (simple integer parsing for now)
  let value : Int := match raw.toInt? with
    | some v => v
    | none => 0  -- Will be validated later if needed

  return (raw, value, st)

/-- Parse a keyword (true, false, null). -/
private def parseKeyword (s : LexerState) (kw : String) (tok : Token) :
    OracleResult (Token × LexerState) := do
  let kwBytes := kw.toUTF8
  if s.pos + kwBytes.size > s.bytes.size then throw ErrorCode.E100_InvalidJSON
  for i in [:kwBytes.size] do
    if s.bytes[s.pos + i]! ≠ kwBytes[i]! then throw ErrorCode.E100_InvalidJSON
  return (tok, { s with pos := s.pos + kwBytes.size })

/-- Tokenize JSON bytes, preserving raw number strings.

Returns array of tokens for further parsing. -/
def lexJSON (bytes : ByteArray) : OracleResult (Array Token) := do
  let mut tokens : Array Token := #[]
  let mut st : LexerState := { bytes := bytes, pos := 0 }

  while !st.isEOF do
    st := st.skipWhitespace
    if st.isEOF then break

    match st.peek with
    | some 0x7B => tokens := tokens.push .lbrace; st := st.advance
    | some 0x7D => tokens := tokens.push .rbrace; st := st.advance
    | some 0x5B => tokens := tokens.push .lbracket; st := st.advance
    | some 0x5D => tokens := tokens.push .rbracket; st := st.advance
    | some 0x3A => tokens := tokens.push .colon; st := st.advance
    | some 0x2C => tokens := tokens.push .comma; st := st.advance
    | some 0x22 => -- string
      st := st.advance
      let (s, st') ← parseString st
      tokens := tokens.push (.string s)
      st := st'
    | some 0x74 => -- true
      let (tok, st') ← parseKeyword st "true" .true_
      tokens := tokens.push tok
      st := st'
    | some 0x66 => -- false
      let (tok, st') ← parseKeyword st "false" .false_
      tokens := tokens.push tok
      st := st'
    | some 0x6E => -- null
      let (tok, st') ← parseKeyword st "null" .null_
      tokens := tokens.push tok
      st := st'
    | some b =>
      if b == 0x2D || (b >= 0x30 && b <= 0x39) then
        let (raw, value, st') ← parseNumber st
        tokens := tokens.push (.number raw value)
        st := st'
      else
        throw ErrorCode.E100_InvalidJSON
    | none => throw ErrorCode.E100_InvalidJSON

  return tokens

end Jolt.JSON
