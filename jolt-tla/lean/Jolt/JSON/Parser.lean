import Jolt.Errors
import Jolt.JSON.Types
import Jolt.JSON.Lexer
import Jolt.JSON.Safety
import Std.Data.TreeSet

/-!
# JSON Parser (ASCII-Only Profile)

Transforms token stream from Lexer into JsonValue AST.
Part of the JCS-ASCII consensus-critical JSON profile.

## Main Definitions
* `parseJSON` - Parse tokens into JsonValue
* `parseJSONBytes` - Parse raw bytes with full validation

## Implementation Notes
This parser enforces consensus-critical validation:
- Duplicate keys are rejected (E101) with O(log n) TreeSet lookup
- Exponent notation rejected (E107)
- Fractional numbers rejected (E108)
- Integer range enforced (E109)
- Non-ASCII characters rejected (E115)

TreeSet (red-black tree) provides guaranteed O(log n) worst-case lookup,
avoiding hash-flooding DoS attacks that could degrade HashSet to O(n).

## References
* Jolt Spec §2.6.1 (ASCII-only JSON profile)
-/

namespace Jolt.JSON

/-- Parser state tracking position in token stream. -/
structure ParserState where
  tokens : Array Token
  pos : Nat

namespace ParserState

/-- Get current token if available. -/
def current? (s : ParserState) : Option Token :=
  if s.pos < s.tokens.size then some s.tokens[s.pos]! else none

/-- Advance to next token. -/
def advance (s : ParserState) : ParserState :=
  { s with pos := s.pos + 1 }

/-- Check if at end of tokens. -/
def isEOF (s : ParserState) : Bool := s.pos ≥ s.tokens.size

/-- Remaining tokens count (for termination proofs). -/
def remaining (s : ParserState) : Nat := s.tokens.size - s.pos

end ParserState

/-- TreeSet for O(log n) worst-case duplicate key detection.
    TreeSet is backed by a red-black tree, providing guaranteed O(log n) lookup.
    This avoids hash-flooding DoS that could degrade HashSet to O(n). -/
abbrev KeySet := Std.TreeSet String compare

mutual
  /-- Parse a single JSON value with depth tracking and limits. -/
  partial def parseValueWithLimits (s : ParserState) (limits : Limits) (depth : Nat) :
      OracleResult (JsonValue × ParserState) := do
    match s.current? with
    | some .null_ => return (.null, s.advance)
    | some .true_ => return (.bool true, s.advance)
    | some .false_ => return (.bool false, s.advance)
    | some (.string str) => return (.str str, s.advance)
    | some (.number raw value) =>
        validateNumberToken raw value
        return (.num value, s.advance)
    | some .lbracket =>
        -- Check depth before descending into array
        let newDepth := depth + 1
        checkDepth newDepth limits
        parseArrayContentsWithLimits s.advance #[] limits newDepth
    | some .lbrace =>
        -- Check depth before descending into object
        let newDepth := depth + 1
        checkDepth newDepth limits
        parseObjectContentsWithLimits s.advance #[] Std.TreeSet.empty limits newDepth
    | some _ => throw .E100_InvalidJSON
    | none => throw .E100_InvalidJSON

  /-- Parse array contents with limits (accumulator-based). -/
  partial def parseArrayContentsWithLimits (s : ParserState) (acc : Array JsonValue)
      (limits : Limits) (depth : Nat) : OracleResult (JsonValue × ParserState) := do
    -- Empty array (only valid at start, not after comma)
    if acc.isEmpty && s.current? == some .rbracket then
      return (.arr acc, s.advance)

    -- Check array length limit before adding element
    if acc.size >= limits.maxArrayLength then
      throw (ErrorCode.E114_ArrayTooLong acc.size limits.maxArrayLength)

    -- Parse next value (required after comma or at start of non-empty array)
    let (val, s') ← parseValueWithLimits s limits depth
    let acc' := acc.push val

    -- Check for more elements or end
    match s'.current? with
    | some .rbracket => return (.arr acc', s'.advance)
    | some .comma => parseArrayContentsWithLimits s'.advance acc' limits depth
    | _ => throw .E100_InvalidJSON

  /-- Parse object contents with limits and O(1) duplicate key detection.

  Uses a HashSet to track seen keys, providing O(1) lookup instead of O(n) linear scan.
  The accumulator array still stores the key-value pairs for the final JsonValue. -/
  partial def parseObjectContentsWithLimits (s : ParserState) (acc : Array (String × JsonValue))
      (seenKeys : KeySet) (limits : Limits) (depth : Nat) : OracleResult (JsonValue × ParserState) := do
    -- Empty object (only valid at start, not after comma)
    if acc.isEmpty && s.current? == some .rbrace then
      return (.obj acc, s.advance)

    -- Check object field count limit before adding field
    if acc.size >= limits.maxObjectFields then
      throw (ErrorCode.E113_TooManyFields acc.size limits.maxObjectFields)

    -- Expect string key
    let key ← match s.current? with
      | some (.string k) => pure k
      | _ => throw .E100_InvalidJSON
    let s := s.advance

    -- Check for duplicate key with O(log n) RBMap lookup
    if seenKeys.contains key then
      throw (.E101_DuplicateKey key)

    -- Expect colon
    match s.current? with
    | some .colon => pure ()
    | _ => throw .E100_InvalidJSON
    let s := s.advance

    -- Parse value
    let (val, s') ← parseValueWithLimits s limits depth
    let acc' := acc.push (key, val)
    let seenKeys' := seenKeys.insert key

    -- Check for more elements or end
    match s'.current? with
    | some .rbrace => return (.obj acc', s'.advance)
    | some .comma => parseObjectContentsWithLimits s'.advance acc' seenKeys' limits depth
    | _ => throw .E100_InvalidJSON
end

/-- Parse a single JSON value (with default limits). -/
partial def parseValue (s : ParserState) : OracleResult (JsonValue × ParserState) :=
  parseValueWithLimits s Limits.default 0

/-- Parse array contents (with default limits). -/
partial def parseArrayContents (s : ParserState) (acc : Array JsonValue) :
    OracleResult (JsonValue × ParserState) :=
  parseArrayContentsWithLimits s acc Limits.default 0

/-- Parse object contents (with default limits). -/
partial def parseObjectContents (s : ParserState) (acc : Array (String × JsonValue)) :
    OracleResult (JsonValue × ParserState) :=
  parseObjectContentsWithLimits s acc Std.TreeSet.empty Limits.default 0

/-- Parse JSON tokens into a JsonValue AST with configurable limits.

Returns E100_InvalidJSON on malformed structure.
Returns E101_DuplicateKey if any object has repeated keys.
Returns E107/E108/E109 for number validation failures.
Returns E111/E113/E114 for limit violations. -/
def parseJSONWithLimits (tokens : Array Token) (limits : Limits) : OracleResult JsonValue := do
  if tokens.isEmpty then
    throw .E100_InvalidJSON

  let state : ParserState := { tokens := tokens, pos := 0 }
  let (value, finalState) ← parseValueWithLimits state limits 0

  -- Ensure no trailing tokens
  if finalState.pos < tokens.size then
    throw .E100_InvalidJSON

  return value

/-- Parse JSON tokens into a JsonValue AST (with default limits). -/
def parseJSON (tokens : Array Token) : OracleResult JsonValue :=
  parseJSONWithLimits tokens Limits.default

/-- Parse JSON from raw bytes with all validations and configurable limits.

This is the primary entry point for parsing JSON. It performs:
1. Input size check
2. BOM check (reject if present)
3. Tokenization via lexer (with string length limits)
4. Parsing with duplicate key detection
5. Number validation (no exponents, no fractions, range check)
6. Depth, array length, and object field count limits -/
def parseJSONBytesWithLimits (bytes : ByteArray) (limits : Limits) : OracleResult JsonValue := do
  -- Check input size limit
  checkInputSize bytes.size limits

  -- Pre-lexer checks
  if hasBOM bytes then
    throw .E100_InvalidJSON

  -- Tokenize with limits
  let tokens ← lexJSONWithLimits bytes limits

  -- Parse with validation and limits
  parseJSONWithLimits tokens limits

/-- Parse JSON from raw bytes with all validations (default limits). -/
def parseJSONBytes (bytes : ByteArray) : OracleResult JsonValue :=
  parseJSONBytesWithLimits bytes Limits.default

end Jolt.JSON
