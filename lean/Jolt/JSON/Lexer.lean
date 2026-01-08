import Jolt.Errors
import Jolt.JSON.Safety

/-!
# JSON Lexer

Custom JSON lexer that preserves raw number strings.

## Main Definitions
* `Token` - JSON token type
* `lexJSON` - Tokenize JSON bytes

## ASCII-Only Profile (Deliberate Non-RFC-8259)

This parser implements an **ASCII-only subset** of JSON for consensus determinism:

1. **Bytes >= 0x80 are rejected** (E115_NonASCIICharacter)
   - No UTF-8 multi-byte sequences allowed in string values
   - Defense against encoding ambiguity across implementations

2. **\uXXXX escapes producing codepoints > 127 are rejected**
   - `\u00e9` (é) → E115_NonASCIICharacter
   - `\uD83D\uDE00` (😀 via surrogate pair) → E115_NonASCIICharacter
   - `\u0041` (A) → OK (ASCII range)

3. **Rationale**: Consensus-critical systems require bit-exact determinism.
   Different implementations may handle UTF-8 differently (normalization,
   encoding errors, etc.). ASCII-only eliminates this class of bugs.

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
  deriving Repr, DecidableEq, Inhabited

/-- Lexer state. -/
structure LexerState where
  bytes : ByteArray
  pos : Nat

namespace LexerState

def peek (s : LexerState) : Option UInt8 :=
  if s.pos < s.bytes.size then some s.bytes[s.pos]! else none

def advance (s : LexerState) : LexerState :=
  { s with pos := s.pos + 1 }

def peekChar (s : LexerState) : Option Char :=
  s.peek.map (fun b => Char.ofNat b.toNat)

def isEOF (s : LexerState) : Bool := s.pos ≥ s.bytes.size

def skipWhitespace (s : LexerState) : LexerState := Id.run do
  let mut st := s
  while !st.isEOF do
    match st.peek with
    | some 0x20 | some 0x09 | some 0x0A | some 0x0D => st := st.advance
    | _ => break
  return st

end LexerState

/-- Check if a code unit is a high surrogate (0xD800-0xDBFF). -/
private def isHighSurrogate (cu : UInt32) : Bool :=
  cu >= 0xD800 && cu <= 0xDBFF

/-- Check if a code unit is a low surrogate (0xDC00-0xDFFF). -/
private def isLowSurrogate (cu : UInt32) : Bool :=
  cu >= 0xDC00 && cu <= 0xDFFF

/-- Check if a code point is a surrogate (0xD800-0xDFFF). -/
private def isSurrogate (cp : UInt32) : Bool :=
  cp >= 0xD800 && cp <= 0xDFFF

/-- Check if a code point is an I-JSON noncharacter.
    Per RFC 7493: U+FDD0-U+FDEF and U+nFFFE/U+nFFFF for all planes. -/
private def isNoncharacter (cp : UInt32) : Bool :=
  -- U+FDD0 to U+FDEF
  (cp >= 0xFDD0 && cp <= 0xFDEF) ||
  -- U+FFFE and U+FFFF in any plane (0x__FFFE or 0x__FFFF)
  ((cp &&& 0xFFFF) == 0xFFFE || (cp &&& 0xFFFF) == 0xFFFF)

/-- Combine a surrogate pair into a Unicode scalar value.
    high ∈ [0xD800, 0xDBFF], low ∈ [0xDC00, 0xDFFF]
    Result: ((high - 0xD800) << 10) + (low - 0xDC00) + 0x10000 -/
private def combineSurrogatePair (high low : UInt32) : UInt32 :=
  ((high - 0xD800) <<< 10) + (low - 0xDC00) + 0x10000

/-- Validate a decoded code point per I-JSON (RFC 7493).
    Rejects surrogates and noncharacters. -/
private def validateCodePoint (cp : UInt32) : OracleResult Unit := do
  if isSurrogate cp then throw ErrorCode.E100_InvalidJSON
  if isNoncharacter cp then throw ErrorCode.E100_InvalidJSON
  if cp > 0x10FFFF then throw ErrorCode.E100_InvalidJSON

/-- Decode a UTF-8 sequence starting at the current position.
    Returns the decoded code point and advances past the sequence.
    Rejects:
    - Invalid UTF-8 sequences
    - Overlong encodings
    - Surrogates encoded in UTF-8
    - Code points > U+10FFFF -/
private def decodeUTF8 (st : LexerState) : OracleResult (UInt32 × LexerState) := do
  let b0 := st.bytes[st.pos]!

  -- 1-byte sequence (ASCII): 0xxxxxxx
  if b0 < 0x80 then
    return (b0.toUInt32, st.advance)

  -- Continuation byte or invalid start byte
  if b0 < 0xC2 then throw ErrorCode.E100_InvalidJSON  -- 0x80-0xBF or 0xC0-0xC1 (overlong)

  -- 2-byte sequence: 110xxxxx 10xxxxxx (U+0080 to U+07FF)
  if b0 < 0xE0 then
    if st.pos + 2 > st.bytes.size then throw ErrorCode.E100_InvalidJSON
    let b1 := st.bytes[st.pos + 1]!
    if b1 < 0x80 || b1 >= 0xC0 then throw ErrorCode.E100_InvalidJSON  -- Must be 10xxxxxx
    let cp := ((b0.toUInt32 &&& 0x1F) <<< 6) ||| (b1.toUInt32 &&& 0x3F)
    -- Overlong check: must be >= 0x80
    if cp < 0x80 then throw ErrorCode.E100_InvalidJSON
    return (cp, { st with pos := st.pos + 2 })

  -- 3-byte sequence: 1110xxxx 10xxxxxx 10xxxxxx (U+0800 to U+FFFF)
  if b0 < 0xF0 then
    if st.pos + 3 > st.bytes.size then throw ErrorCode.E100_InvalidJSON
    let b1 := st.bytes[st.pos + 1]!
    let b2 := st.bytes[st.pos + 2]!
    if b1 < 0x80 || b1 >= 0xC0 then throw ErrorCode.E100_InvalidJSON
    if b2 < 0x80 || b2 >= 0xC0 then throw ErrorCode.E100_InvalidJSON
    let cp := ((b0.toUInt32 &&& 0x0F) <<< 12) |||
              ((b1.toUInt32 &&& 0x3F) <<< 6) |||
              (b2.toUInt32 &&& 0x3F)
    -- Overlong check: must be >= 0x800
    if cp < 0x800 then throw ErrorCode.E100_InvalidJSON
    -- Surrogate check (U+D800 to U+DFFF not allowed in UTF-8)
    if isSurrogate cp then throw ErrorCode.E100_InvalidJSON
    return (cp, { st with pos := st.pos + 3 })

  -- 4-byte sequence: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx (U+10000 to U+10FFFF)
  if b0 < 0xF5 then
    if st.pos + 4 > st.bytes.size then throw ErrorCode.E100_InvalidJSON
    let b1 := st.bytes[st.pos + 1]!
    let b2 := st.bytes[st.pos + 2]!
    let b3 := st.bytes[st.pos + 3]!
    if b1 < 0x80 || b1 >= 0xC0 then throw ErrorCode.E100_InvalidJSON
    if b2 < 0x80 || b2 >= 0xC0 then throw ErrorCode.E100_InvalidJSON
    if b3 < 0x80 || b3 >= 0xC0 then throw ErrorCode.E100_InvalidJSON
    let cp := ((b0.toUInt32 &&& 0x07) <<< 18) |||
              ((b1.toUInt32 &&& 0x3F) <<< 12) |||
              ((b2.toUInt32 &&& 0x3F) <<< 6) |||
              (b3.toUInt32 &&& 0x3F)
    -- Overlong check: must be >= 0x10000
    if cp < 0x10000 then throw ErrorCode.E100_InvalidJSON
    -- Range check: must be <= 0x10FFFF
    if cp > 0x10FFFF then throw ErrorCode.E100_InvalidJSON
    return (cp, { st with pos := st.pos + 4 })

  -- Invalid start byte (0xF5-0xFF)
  throw ErrorCode.E100_InvalidJSON

/-- Parse a 4-digit hex escape (\uXXXX) and return the code unit and new state. -/
private def parseHexEscape (st : LexerState) : OracleResult (UInt32 × LexerState) := do
  if st.pos + 4 > st.bytes.size then throw ErrorCode.E100_InvalidJSON
  let mut codeunit : UInt32 := 0
  let mut state := st
  for _ in [:4] do
    let b := state.bytes[state.pos]!
    let digit := if b >= 0x30 && b <= 0x39 then b - 0x30
                 else if b >= 0x41 && b <= 0x46 then b - 0x41 + 10
                 else if b >= 0x61 && b <= 0x66 then b - 0x61 + 10
                 else 255
    if digit > 15 then throw ErrorCode.E100_InvalidJSON
    codeunit := codeunit * 16 + digit.toUInt32
    state := state.advance
  return (codeunit, state)

/-- Parse a JSON string literal (after opening quote).

ASCII-only profile for consensus safety:
- Rejects any byte >= 0x80 (non-ASCII)
- Rejects \uXXXX escapes producing codepoints > 127
- Combines surrogate pairs in \uXXXX into proper Unicode scalars (then rejects if > 127)
- Enforces string length limit for DoS protection

This is a deliberate non-RFC-8259 subset for deterministic consensus.
All string content must be pure ASCII (0x00-0x7F).

Uses O(1) length tracking to avoid O(n²) from repeated String.length calls. -/
private def parseString (s : LexerState) (limits : Limits) : OracleResult (String × LexerState) := do
  let mut st := s
  let mut chars : Array Char := #[]  -- O(1) amortized append
  let mut charCount : Nat := 0       -- O(1) length tracking
  while !st.isEOF do
    match st.peek with
    | some 0x22 => -- closing quote - check for end FIRST, before limit check
      return (String.ofList chars.toList, st.advance)
    | some 0x5C => -- backslash escape
      -- Check string length limit with O(1) counter (check BEFORE adding next char)
      if charCount >= limits.maxStringLength then
        throw (ErrorCode.E112_StringTooLong charCount limits.maxStringLength)
      st := st.advance
      match st.peek with
      | some 0x22 => chars := chars.push '"'; charCount := charCount + 1; st := st.advance
      | some 0x5C => chars := chars.push '\\'; charCount := charCount + 1; st := st.advance
      | some 0x2F => chars := chars.push '/'; charCount := charCount + 1; st := st.advance
      | some 0x62 => chars := chars.push '\x08'; charCount := charCount + 1; st := st.advance
      | some 0x66 => chars := chars.push '\x0C'; charCount := charCount + 1; st := st.advance
      | some 0x6E => chars := chars.push '\n'; charCount := charCount + 1; st := st.advance
      | some 0x72 => chars := chars.push '\r'; charCount := charCount + 1; st := st.advance
      | some 0x74 => chars := chars.push '\t'; charCount := charCount + 1; st := st.advance
      | some 0x75 => -- \uXXXX escape
        st := st.advance
        let (codeunit, st') ← parseHexEscape st
        st := st'

        -- Handle surrogate pairs (for completeness, though result must still be ASCII)
        if isHighSurrogate codeunit then
          -- Must be followed by \uXXXX with low surrogate
          if st.peek != some 0x5C then throw ErrorCode.E100_InvalidJSON
          st := st.advance
          if st.peek != some 0x75 then throw ErrorCode.E100_InvalidJSON
          st := st.advance
          let (lowUnit, st') ← parseHexEscape st
          st := st'
          if !isLowSurrogate lowUnit then throw ErrorCode.E100_InvalidJSON
          let scalar := combineSurrogatePair codeunit lowUnit
          -- Surrogate pairs always produce codepoints >= 0x10000, which is non-ASCII
          throw (ErrorCode.E115_NonASCIICharacter scalar.toNat)
        else if isLowSurrogate codeunit then
          -- Lone low surrogate is invalid
          throw ErrorCode.E100_InvalidJSON
        else
          -- BMP character - must be ASCII (codepoint <= 127)
          if codeunit > 127 then
            throw (ErrorCode.E115_NonASCIICharacter codeunit.toNat)
          validateCodePoint codeunit
          chars := chars.push (Char.ofNat codeunit.toNat)
          charCount := charCount + 1
      | _ => throw ErrorCode.E100_InvalidJSON
    | some b =>
      -- Check string length limit with O(1) counter (check BEFORE adding next char)
      if charCount >= limits.maxStringLength then
        throw (ErrorCode.E112_StringTooLong charCount limits.maxStringLength)
      -- Reject unescaped control characters (< 0x20)
      if b < 0x20 then throw ErrorCode.E100_InvalidJSON
      -- ASCII-only profile: reject any byte >= 0x80
      if b >= 0x80 then throw (ErrorCode.E115_NonASCIICharacter b.toNat)
      -- ASCII character (0x20-0x7F, excluding control and quotes handled above)
      chars := chars.push (Char.ofNat b.toNat)
      charCount := charCount + 1
      st := st.advance
    | none => throw ErrorCode.E100_InvalidJSON
  throw ErrorCode.E100_InvalidJSON  -- unterminated string

/-- Maximum number of digits allowed in integer literals.
    ±(2^53-1) = ±9007199254740991 is 16 digits, so 17 chars with sign.
    Numbers exceeding this are rejected *before* big-int parsing to prevent DoS. -/
private def MAX_NUMBER_CHARS : Nat := 20  -- generous buffer for sign + digits + some margin

/-- Parse a JSON number (raw string preserved).

Uses Array Char with O(1) length tracking to avoid O(n²) from String operations.

DoS protection: Rejects numbers with more than MAX_NUMBER_CHARS before attempting
big-int parsing. This prevents CPU/memory exhaustion from multi-MB integer literals. -/
private def parseNumber (s : LexerState) : OracleResult (String × Int × LexerState) := do
  let mut st := s
  let mut chars : Array Char := #[]  -- O(1) amortized append
  let mut charCount : Nat := 0       -- O(1) length tracking
  let mut digitCount : Nat := 0      -- Track actual digits (excluding sign)

  -- Optional minus
  if st.peek == some 0x2D then
    chars := chars.push '-'
    charCount := charCount + 1
    st := st.advance

  -- Integer part
  match st.peek with
  | some 0x30 =>  -- leading zero
    chars := chars.push '0'
    charCount := charCount + 1
    digitCount := digitCount + 1
    st := st.advance
  | some b =>
    if b >= 0x31 && b <= 0x39 then
      while !st.isEOF do
        match st.peek with
        | some d => if d >= 0x30 && d <= 0x39 then
                      -- DoS guard: reject before parsing if too many digits
                      if digitCount >= MAX_NUMBER_CHARS then
                        throw ErrorCode.E109_IntegerOutOfRange
                      chars := chars.push (Char.ofNat d.toNat)
                      charCount := charCount + 1
                      digitCount := digitCount + 1
                      st := st.advance
                    else break
        | none => break
    else throw ErrorCode.E100_InvalidJSON
  | none => throw ErrorCode.E100_InvalidJSON

  -- Fractional part (optional)
  if st.peek == some 0x2E then
    chars := chars.push '.'
    charCount := charCount + 1
    st := st.advance
    let startFrac := charCount
    while !st.isEOF do
      match st.peek with
      | some d => if d >= 0x30 && d <= 0x39 then
                    chars := chars.push (Char.ofNat d.toNat)
                    charCount := charCount + 1
                    st := st.advance
                  else break
      | none => break
    if charCount == startFrac then throw ErrorCode.E100_InvalidJSON

  -- Exponent (optional)
  if st.peek == some 0x65 || st.peek == some 0x45 then
    chars := chars.push (Char.ofNat st.peek.get!.toNat)
    charCount := charCount + 1
    st := st.advance
    if st.peek == some 0x2B || st.peek == some 0x2D then
      chars := chars.push (Char.ofNat st.peek.get!.toNat)
      charCount := charCount + 1
      st := st.advance
    let startExp := charCount
    while !st.isEOF do
      match st.peek with
      | some d => if d >= 0x30 && d <= 0x39 then
                    chars := chars.push (Char.ofNat d.toNat)
                    charCount := charCount + 1
                    st := st.advance
                  else break
      | none => break
    if charCount == startExp then throw ErrorCode.E100_InvalidJSON

  -- Build raw string and parse value
  let raw : String := String.ofList chars.toList
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

/-- Tokenize JSON bytes with configurable limits.

Returns array of tokens for further parsing.
Enforces input size and string length limits for DoS protection. -/
def lexJSONWithLimits (bytes : ByteArray) (limits : Limits) : OracleResult (Array Token) := do
  -- Check input size limit
  checkInputSize bytes.size limits

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
      let (s, st') ← parseString st limits
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
      else if b >= 0x80 then
        -- Non-ASCII byte outside string context - consistent E115 error
        throw (ErrorCode.E115_NonASCIICharacter b.toNat)
      else
        throw ErrorCode.E100_InvalidJSON
    | none => throw ErrorCode.E100_InvalidJSON

  return tokens

/-- Tokenize JSON bytes with default limits.

Returns array of tokens for further parsing. -/
def lexJSON (bytes : ByteArray) : OracleResult (Array Token) :=
  lexJSONWithLimits bytes Limits.default

end Jolt.JSON
