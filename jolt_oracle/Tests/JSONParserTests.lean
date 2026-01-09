import Jolt.JSON.Parser
import Jolt.JSON.JCS
import Jolt.Errors

/-!
# JSON Parser Tests

Comprehensive test suite for the JSON parser per spec §2.6.1.
-/

namespace Jolt.Tests.JSON

open Jolt
open Jolt.JSON

/-! ## Helper Functions -/

/-- Convert string to ByteArray for testing. -/
def strToBytes (s : String) : ByteArray := s.toUTF8

/-- Check if result is Ok (any value). -/
def expectSuccess {α : Type} (name : String) (result : OracleResult α) : IO Bool := do
  match result with
  | .ok _ => return true
  | .error e =>
    IO.println s!"FAIL: {name} - unexpected error: {repr e}"
    return false

/-- Check if result is any error. -/
def expectAnyError {α : Type} (name : String) (result : OracleResult α) : IO Bool := do
  match result with
  | .ok _ =>
    IO.println s!"FAIL: {name} - expected error, got Ok"
    return false
  | .error _ => return true

/-- Check if result is an error with expected code. -/
def expectErrorCode {α : Type} (name : String) (result : OracleResult α) (expected : ErrorCode) : IO Bool := do
  match result with
  | .ok _ =>
    IO.println s!"FAIL: {name} - expected error {repr expected}, got Ok"
    return false
  | .error e =>
    if e == expected then
      return true
    else
      IO.println s!"FAIL: {name} - expected {repr expected}, got {repr e}"
      return false

/-! ## 1. Lexer Tests -/

def testLexerBasicTokens : IO Bool := do
  -- Test structural tokens
  let result := lexJSON (strToBytes "{}")
  match result with
  | .ok tokens =>
    if tokens.size != 2 then
      IO.println "FAIL: Lexer {} - wrong token count"
      return false
  | .error _ =>
    IO.println "FAIL: Lexer {} - unexpected error"
    return false

  -- Test array tokens
  let result2 := lexJSON (strToBytes "[]")
  match result2 with
  | .ok tokens =>
    if tokens.size != 2 then
      IO.println "FAIL: Lexer [] - wrong token count"
      return false
  | .error _ =>
    IO.println "FAIL: Lexer [] - unexpected error"
    return false

  IO.println "PASS: Lexer basic tokens"
  return true

def testLexerStrings : IO Bool := do
  -- Simple string
  let result := lexJSON (strToBytes "\"hello\"")
  match result with
  | .ok tokens =>
    match tokens[0]? with
    | some (Token.string s) =>
      if s != "hello" then
        IO.println s!"FAIL: Lexer string - got '{s}'"
        return false
    | _ =>
      IO.println "FAIL: Lexer string - wrong token type"
      return false
  | .error _ =>
    IO.println "FAIL: Lexer string - unexpected error"
    return false

  IO.println "PASS: Lexer strings"
  return true

def testLexerNumbers : IO Bool := do
  -- Positive integer
  let result := lexJSON (strToBytes "42")
  match result with
  | .ok tokens =>
    match tokens[0]? with
    | some (Token.number raw val) =>
      if raw != "42" || val != 42 then
        IO.println s!"FAIL: Lexer number 42 - raw='{raw}' val={val}"
        return false
    | _ =>
      IO.println "FAIL: Lexer number 42 - wrong token type"
      return false
  | .error _ =>
    IO.println "FAIL: Lexer number - unexpected error"
    return false

  -- Negative integer
  let result2 := lexJSON (strToBytes "-123")
  match result2 with
  | .ok tokens =>
    match tokens[0]? with
    | some (Token.number raw val) =>
      if raw != "-123" || val != -123 then
        IO.println s!"FAIL: Lexer number -123"
        return false
    | _ =>
      IO.println "FAIL: Lexer number -123 - wrong type"
      return false
  | .error _ =>
    IO.println "FAIL: Lexer number -123 - unexpected error"
    return false

  IO.println "PASS: Lexer numbers"
  return true

def testLexerKeywords : IO Bool := do
  -- true
  let result1 := lexJSON (strToBytes "true")
  match result1 with
  | .ok tokens =>
    if tokens.size != 1 || tokens[0]! != Token.true_ then
      IO.println "FAIL: Lexer keyword true"
      return false
  | .error _ =>
    IO.println "FAIL: Lexer keyword true - unexpected error"
    return false

  -- false
  let result2 := lexJSON (strToBytes "false")
  match result2 with
  | .ok tokens =>
    if tokens.size != 1 || tokens[0]! != Token.false_ then
      IO.println "FAIL: Lexer keyword false"
      return false
  | .error _ =>
    IO.println "FAIL: Lexer keyword false - unexpected error"
    return false

  -- null
  let result3 := lexJSON (strToBytes "null")
  match result3 with
  | .ok tokens =>
    if tokens.size != 1 || tokens[0]! != Token.null_ then
      IO.println "FAIL: Lexer keyword null"
      return false
  | .error _ =>
    IO.println "FAIL: Lexer keyword null - unexpected error"
    return false

  IO.println "PASS: Lexer keywords"
  return true

/-! ## 2. Parser Positive Tests -/

def testParserPrimitives : IO Bool := do
  -- null
  if !(← expectSuccess "null" (parseJSONBytes (strToBytes "null"))) then
    return false

  -- true
  if !(← expectSuccess "true" (parseJSONBytes (strToBytes "true"))) then
    return false

  -- false
  if !(← expectSuccess "false" (parseJSONBytes (strToBytes "false"))) then
    return false

  -- integer
  if !(← expectSuccess "integer 42" (parseJSONBytes (strToBytes "42"))) then
    return false

  -- string
  if !(← expectSuccess "string" (parseJSONBytes (strToBytes "\"hello\""))) then
    return false

  IO.println "PASS: Parser primitives"
  return true

def testParserEmptyStructures : IO Bool := do
  -- Empty object
  match parseJSONBytes (strToBytes "{}") with
  | .ok (.obj fields) =>
    if fields.size != 0 then
      IO.println "FAIL: Empty object has fields"
      return false
  | .ok _ =>
    IO.println "FAIL: Empty object wrong type"
    return false
  | .error e =>
    IO.println s!"FAIL: Empty object error: {repr e}"
    return false

  -- Empty array
  match parseJSONBytes (strToBytes "[]") with
  | .ok (.arr items) =>
    if items.size != 0 then
      IO.println "FAIL: Empty array has items"
      return false
  | .ok _ =>
    IO.println "FAIL: Empty array wrong type"
    return false
  | .error e =>
    IO.println s!"FAIL: Empty array error: {repr e}"
    return false

  IO.println "PASS: Parser empty structures"
  return true

def testParserNestedStructures : IO Bool := do
  -- Nested object: {"a": {"b": 1}}
  let nested := "{\"a\": {\"b\": 1}}"
  if !(← expectSuccess "nested object" (parseJSONBytes (strToBytes nested))) then
    return false

  -- Nested array
  let nestedArr := "[[1, 2], [3, 4]]"
  if !(← expectSuccess "nested array" (parseJSONBytes (strToBytes nestedArr))) then
    return false

  -- Mixed nesting: {"items": [1, 2, {"nested": true}]}
  let mixed := "{\"items\": [1, 2, {\"nested\": true}]}"
  if !(← expectSuccess "mixed nesting" (parseJSONBytes (strToBytes mixed))) then
    return false

  IO.println "PASS: Parser nested structures"
  return true

def testParserComplexObject : IO Bool := do
  -- {"name": "test", "count": 42, "active": true, "data": null, "items": [1, 2, 3]}
  let json := "{\"name\": \"test\", \"count\": 42, \"active\": true, \"data\": null, \"items\": [1, 2, 3]}"

  match parseJSONBytes (strToBytes json) with
  | .ok (.obj fields) =>
    if fields.size != 5 then
      IO.println s!"FAIL: Complex object field count: {fields.size}"
      return false
  | .ok _ =>
    IO.println "FAIL: Complex object wrong type"
    return false
  | .error e =>
    IO.println s!"FAIL: Complex object error: {repr e}"
    return false

  IO.println "PASS: Parser complex object"
  return true

/-! ## 3. Parser Negative Tests -/

def testParserInvalidJSON : IO Bool := do
  -- Trailing comma in array
  if !(← expectAnyError "trailing comma array" (parseJSONBytes (strToBytes "[1, 2, ]"))) then
    return false

  -- Trailing comma in object: {"a": 1, }
  if !(← expectAnyError "trailing comma object" (parseJSONBytes (strToBytes "{\"a\": 1, }"))) then
    return false

  -- Missing colon: {"a" 1}
  if !(← expectAnyError "missing colon" (parseJSONBytes (strToBytes "{\"a\" 1}"))) then
    return false

  -- Unclosed brace: {"a": 1
  if !(← expectAnyError "unclosed brace" (parseJSONBytes (strToBytes "{\"a\": 1"))) then
    return false

  -- Unclosed bracket
  if !(← expectAnyError "unclosed bracket" (parseJSONBytes (strToBytes "[1, 2"))) then
    return false

  -- Empty input
  if !(← expectAnyError "empty input" (parseJSONBytes (strToBytes ""))) then
    return false

  -- Trailing tokens
  if !(← expectAnyError "trailing tokens" (parseJSONBytes (strToBytes "1 2"))) then
    return false

  IO.println "PASS: Parser invalid JSON detection"
  return true

/-! ## 4. Number Validation Tests -/

def testNumberExponentRejection : IO Bool := do
  -- Exponent notation (lowercase e)
  if !(← expectErrorCode "exponent 1e10" (parseJSONBytes (strToBytes "1e10")) .E107_ExponentNotation) then
    return false

  -- Exponent notation (uppercase E)
  if !(← expectErrorCode "exponent 1E10" (parseJSONBytes (strToBytes "1E10")) .E107_ExponentNotation) then
    return false

  -- Negative exponent
  if !(← expectErrorCode "exponent 1e-5" (parseJSONBytes (strToBytes "1e-5")) .E107_ExponentNotation) then
    return false

  IO.println "PASS: Number exponent rejection"
  return true

def testNumberFractionRejection : IO Bool := do
  -- Simple fraction
  if !(← expectErrorCode "fraction 3.14" (parseJSONBytes (strToBytes "3.14")) .E108_FractionalNumber) then
    return false

  -- Negative fraction
  if !(← expectErrorCode "fraction -1.5" (parseJSONBytes (strToBytes "-1.5")) .E108_FractionalNumber) then
    return false

  -- Zero point something
  if !(← expectErrorCode "fraction 0.5" (parseJSONBytes (strToBytes "0.5")) .E108_FractionalNumber) then
    return false

  IO.println "PASS: Number fraction rejection"
  return true

def testNumberRangeValidation : IO Bool := do
  -- Max safe integer (should pass)
  if !(← expectSuccess "max safe int" (parseJSONBytes (strToBytes "9007199254740991"))) then
    return false

  -- Min safe integer (should pass)
  if !(← expectSuccess "min safe int" (parseJSONBytes (strToBytes "-9007199254740991"))) then
    return false

  -- Above max (should fail)
  if !(← expectErrorCode "above max" (parseJSONBytes (strToBytes "9007199254740992")) .E109_IntegerOutOfRange) then
    return false

  -- Below min (should fail)
  if !(← expectErrorCode "below min" (parseJSONBytes (strToBytes "-9007199254740992")) .E109_IntegerOutOfRange) then
    return false

  IO.println "PASS: Number range validation"
  return true

/-- Test that very long digit strings are rejected early (DoS protection). -/
def testBigNumberDoS : IO Bool := do
  -- 21-digit number should be rejected (MAX_NUMBER_CHARS = 20)
  let huge21 := strToBytes "123456789012345678901"
  if !(← expectErrorCode "21 digit number" (parseJSONBytes huge21) .E109_IntegerOutOfRange) then
    return false

  -- 50-digit number should be rejected
  let huge50 := strToBytes (String.ofList (List.replicate 50 '9'))
  if !(← expectErrorCode "50 digit number" (parseJSONBytes huge50) .E109_IntegerOutOfRange) then
    return false

  -- 20-digit number within range should pass (9007199254740991 is 16 digits)
  -- Use a valid 16-digit number
  if !(← expectSuccess "16 digit in-range" (parseJSONBytes (strToBytes "1234567890123456"))) then
    return false

  IO.println "PASS: Big number DoS protection"
  return true

/-- Test that non-ASCII bytes outside strings throw E115. -/
def testNonASCIIOutsideString : IO Bool := do
  -- High byte (0x80) as a token should fail with E115
  let highByte := ByteArray.mk #[0x80]
  match parseJSONBytes highByte with
  | .error (.E115_NonASCIICharacter _) => pure ()
  | .error e => IO.println s!"FAIL: Expected E115, got {repr e}"; return false
  | .ok _ => IO.println "FAIL: Expected E115, got success"; return false

  -- UTF-8 sequence for é (0xC3 0xA9) outside string
  let utf8Seq := ByteArray.mk #[0xC3, 0xA9]
  match parseJSONBytes utf8Seq with
  | .error (.E115_NonASCIICharacter _) => pure ()
  | .error e => IO.println s!"FAIL: Expected E115 for UTF-8 seq, got {repr e}"; return false
  | .ok _ => IO.println "FAIL: Expected E115 for UTF-8 seq, got success"; return false

  IO.println "PASS: Non-ASCII outside string (E115)"
  return true

/-! ## 5. Duplicate Key Tests -/

def testDuplicateKeyDetection : IO Bool := do
  -- Simple duplicate: {"a": 1, "a": 2}
  let dup1 := "{\"a\": 1, \"a\": 2}"
  if !(← expectErrorCode "duplicate key simple" (parseJSONBytes (strToBytes dup1)) (.E101_DuplicateKey "a")) then
    return false

  -- Duplicate with different value types: {"x": "string", "x": 123}
  let dup2 := "{\"x\": \"string\", \"x\": 123}"
  if !(← expectErrorCode "duplicate key diff types" (parseJSONBytes (strToBytes dup2)) (.E101_DuplicateKey "x")) then
    return false

  IO.println "PASS: Duplicate key detection"
  return true

def testNestedDuplicateKeys : IO Bool := do
  -- Duplicate in nested object: {"outer": {"a": 1, "a": 2}}
  let nestedDup := "{\"outer\": {\"a\": 1, \"a\": 2}}"
  if !(← expectErrorCode "nested duplicate" (parseJSONBytes (strToBytes nestedDup)) (.E101_DuplicateKey "a")) then
    return false

  -- Same key at different nesting levels (should be OK): {"a": {"a": 1}}
  let sameKeyDiffLevel := "{\"a\": {\"a\": 1}}"
  if !(← expectSuccess "same key diff level" (parseJSONBytes (strToBytes sameKeyDiffLevel))) then
    return false

  IO.println "PASS: Nested duplicate key detection"
  return true

def testNoDuplicateKeyFalsePositives : IO Bool := do
  -- Different keys (should pass): {"a": 1, "b": 2, "c": 3}
  let diffKeys := "{\"a\": 1, \"b\": 2, \"c\": 3}"
  if !(← expectSuccess "different keys" (parseJSONBytes (strToBytes diffKeys))) then
    return false

  -- Similar keys (should pass): {"aa": 1, "a": 2, "aaa": 3}
  let similarKeys := "{\"aa\": 1, \"a\": 2, \"aaa\": 3}"
  if !(← expectSuccess "similar keys" (parseJSONBytes (strToBytes similarKeys))) then
    return false

  IO.println "PASS: No duplicate key false positives"
  return true

/-! ## 6. BOM Rejection Test -/

def testBOMRejection : IO Bool := do
  -- UTF-8 BOM (0xEF 0xBB 0xBF) followed by valid JSON
  let bomBytes := ByteArray.mk #[0xEF, 0xBB, 0xBF] ++ strToBytes "{}"
  if !(← expectErrorCode "BOM rejection" (parseJSONBytes bomBytes) .E100_InvalidJSON) then
    return false

  IO.println "PASS: BOM rejection"
  return true

/-! ## 7. Edge Cases -/

def testEdgeCases : IO Bool := do
  -- Empty string value
  if !(← expectSuccess "empty string" (parseJSONBytes (strToBytes "\"\""))) then
    return false

  -- Empty key in object: {"": 1}
  if !(← expectSuccess "empty key" (parseJSONBytes (strToBytes "{\"\": 1}"))) then
    return false

  -- Negative zero (should parse as 0)
  match parseJSONBytes (strToBytes "-0") with
  | .ok (.num n) =>
    if n != 0 then
      IO.println s!"FAIL: -0 should be 0, got {n}"
      return false
  | .ok _ =>
    IO.println "FAIL: -0 wrong type"
    return false
  | .error e =>
    IO.println s!"FAIL: -0 error: {repr e}"
    return false

  -- Whitespace handling
  let withSpace := "  {  \"a\"  :  1  }  "
  if !(← expectSuccess "whitespace" (parseJSONBytes (strToBytes withSpace))) then
    return false

  IO.println "PASS: Edge cases"
  return true

def testDeepNesting : IO Bool := do
  -- 10 levels of array nesting
  let deep := "[[[[[[[[[[1]]]]]]]]]]"
  if !(← expectSuccess "deep array nesting" (parseJSONBytes (strToBytes deep))) then
    return false

  -- Mixed deep nesting: {"a":{"b":{"c":{"d":[1]}}}}
  let deepMixed := "{\"a\":{\"b\":{\"c\":{\"d\":[1]}}}}"
  if !(← expectSuccess "deep mixed nesting" (parseJSONBytes (strToBytes deepMixed))) then
    return false

  IO.println "PASS: Deep nesting"
  return true

/-! ## 8. Unicode and UTF-16 Tests -/

def testSurrogatePairParsing : IO Bool := do
  -- ASCII-only profile: surrogate pairs produce codepoints >= 0x10000, which are non-ASCII
  -- They should be rejected with E115_NonASCIICharacter

  -- Surrogate pair: \uD83D\uDE00 = 😀 (U+1F600) - rejected as non-ASCII
  let emojiJson := "\"\\uD83D\\uDE00\""
  match parseJSONBytes (strToBytes emojiJson) with
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: surrogate pair emoji - expected E115, got: {repr e}"
    return false
  | .ok _ =>
    IO.println "FAIL: surrogate pair emoji - should be rejected as non-ASCII"
    return false

  -- Surrogate pair: \uD834\uDD1E = 𝄞 (U+1D11E, musical G clef) - rejected as non-ASCII
  let musicJson := "\"\\uD834\\uDD1E\""
  match parseJSONBytes (strToBytes musicJson) with
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: surrogate pair G clef - expected E115, got: {repr e}"
    return false
  | .ok _ =>
    IO.println "FAIL: surrogate pair G clef - should be rejected as non-ASCII"
    return false

  IO.println "PASS: Surrogate pair rejection (ASCII-only profile)"
  return true

def testLoneSurrogateRejection : IO Bool := do
  -- Lone high surrogate: \uD83D without following low surrogate
  let loneHigh := "\"\\uD83D\""
  if !(← expectErrorCode "lone high surrogate" (parseJSONBytes (strToBytes loneHigh)) .E100_InvalidJSON) then
    return false

  -- Lone high surrogate followed by non-surrogate: \uD83D\u0041
  let highThenNonSurrogate := "\"\\uD83D\\u0041\""
  if !(← expectErrorCode "high then non-surrogate" (parseJSONBytes (strToBytes highThenNonSurrogate)) .E100_InvalidJSON) then
    return false

  -- Lone low surrogate: \uDE00
  let loneLow := "\"\\uDE00\""
  if !(← expectErrorCode "lone low surrogate" (parseJSONBytes (strToBytes loneLow)) .E100_InvalidJSON) then
    return false

  -- High surrogate at end of string (no following escape)
  let highAtEnd := "\"\\uD83Dabc\""
  if !(← expectErrorCode "high surrogate then text" (parseJSONBytes (strToBytes highAtEnd)) .E100_InvalidJSON) then
    return false

  IO.println "PASS: Lone surrogate rejection"
  return true

def testUTF8Decoding : IO Bool := do
  -- ASCII-only profile: non-ASCII bytes (>= 0x80) should be rejected

  -- UTF-8: é (0xC3 0xA9 = U+00E9) - rejected as non-ASCII byte
  let utf8Char := ByteArray.mk #[0x22, 0xC3, 0xA9, 0x22]  -- "é" in UTF-8
  match parseJSONBytes utf8Char with
  | .ok _ =>
    IO.println "FAIL: UTF-8 é - should be rejected as non-ASCII"
    return false
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: UTF-8 é - expected E115, got: {repr e}"
    return false

  -- UTF-8: € (0xE2 0x82 0xAC = U+20AC) - rejected as non-ASCII byte
  let utf8Euro := ByteArray.mk #[0x22, 0xE2, 0x82, 0xAC, 0x22]  -- "€" in UTF-8
  match parseJSONBytes utf8Euro with
  | .ok _ =>
    IO.println "FAIL: UTF-8 € - should be rejected as non-ASCII"
    return false
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: UTF-8 € - expected E115, got: {repr e}"
    return false

  -- UTF-8: 😀 (0xF0 0x9F 0x98 0x80 = U+1F600) - rejected as non-ASCII byte
  let utf8Emoji := ByteArray.mk #[0x22, 0xF0, 0x9F, 0x98, 0x80, 0x22]
  match parseJSONBytes utf8Emoji with
  | .ok _ =>
    IO.println "FAIL: UTF-8 emoji - should be rejected as non-ASCII"
    return false
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: UTF-8 emoji - expected E115, got: {repr e}"
    return false

  -- ASCII strings should still work
  let asciiStr := "\"Hello, World!\""
  match parseJSONBytes (strToBytes asciiStr) with
  | .ok (.str s) =>
    if s != "Hello, World!" then
      IO.println s!"FAIL: ASCII string - expected 'Hello, World!', got '{s}'"
      return false
  | .ok _ =>
    IO.println "FAIL: ASCII string - wrong type"
    return false
  | .error e =>
    IO.println s!"FAIL: ASCII string - unexpected error: {repr e}"
    return false

  IO.println "PASS: UTF-8 decoding"
  return true

def testInvalidUTF8Rejection : IO Bool := do
  -- ASCII-only profile: all bytes >= 0x80 are rejected with E115

  -- Byte 0x80 (would be lone continuation in UTF-8)
  let loneCont := ByteArray.mk #[0x22, 0x80, 0x22]
  match parseJSONBytes loneCont with
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: byte 0x80 - expected E115, got: {repr e}"
    return false
  | .ok _ =>
    IO.println "FAIL: byte 0x80 - should be rejected"
    return false

  -- Byte 0xC1 (would be overlong in UTF-8)
  let overlong := ByteArray.mk #[0x22, 0xC1, 0x81, 0x22]
  match parseJSONBytes overlong with
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: byte 0xC1 - expected E115, got: {repr e}"
    return false
  | .ok _ =>
    IO.println "FAIL: byte 0xC1 - should be rejected"
    return false

  -- Byte 0xC3 (would be 2-byte start in UTF-8)
  let truncated2 := ByteArray.mk #[0x22, 0xC3, 0x22]
  match parseJSONBytes truncated2 with
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: byte 0xC3 - expected E115, got: {repr e}"
    return false
  | .ok _ =>
    IO.println "FAIL: byte 0xC3 - should be rejected"
    return false

  -- Byte 0xE2 (would be 3-byte start in UTF-8)
  let truncated3 := ByteArray.mk #[0x22, 0xE2, 0x82, 0x22]
  match parseJSONBytes truncated3 with
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: byte 0xE2 - expected E115, got: {repr e}"
    return false
  | .ok _ =>
    IO.println "FAIL: byte 0xE2 - should be rejected"
    return false

  -- Byte 0xED (would be surrogate start in UTF-8)
  let surrogateUtf8 := ByteArray.mk #[0x22, 0xED, 0xA0, 0x80, 0x22]
  match parseJSONBytes surrogateUtf8 with
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: byte 0xED - expected E115, got: {repr e}"
    return false
  | .ok _ =>
    IO.println "FAIL: byte 0xED - should be rejected"
    return false

  -- Byte 0xF4 (would be 4-byte start in UTF-8)
  let tooHigh := ByteArray.mk #[0x22, 0xF4, 0x90, 0x80, 0x80, 0x22]
  match parseJSONBytes tooHigh with
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: byte 0xF4 - expected E115, got: {repr e}"
    return false
  | .ok _ =>
    IO.println "FAIL: byte 0xF4 - should be rejected"
    return false

  IO.println "PASS: Invalid UTF-8 rejection"
  return true

def testNoncharacterRejection : IO Bool := do
  -- ASCII-only profile: \uXXXX escapes for non-ASCII codepoints (> 127) are rejected with E115
  -- These happen to also be I-JSON noncharacters, but the ASCII check comes first

  -- U+FDD0 via \uFDD0 - rejected as non-ASCII (> 127)
  let nonchar1 := "\"\\ufdd0\""
  match parseJSONBytes (strToBytes nonchar1) with
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: U+FDD0 - expected E115, got: {repr e}"
    return false
  | .ok _ =>
    IO.println "FAIL: U+FDD0 - should be rejected"
    return false

  -- U+FDEF via \uFDEF - rejected as non-ASCII (> 127)
  let nonchar2 := "\"\\ufdef\""
  match parseJSONBytes (strToBytes nonchar2) with
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: U+FDEF - expected E115, got: {repr e}"
    return false
  | .ok _ =>
    IO.println "FAIL: U+FDEF - should be rejected"
    return false

  -- U+FFFE via \uFFFE - rejected as non-ASCII (> 127)
  let nonchar3 := "\"\\ufffe\""
  match parseJSONBytes (strToBytes nonchar3) with
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: U+FFFE - expected E115, got: {repr e}"
    return false
  | .ok _ =>
    IO.println "FAIL: U+FFFE - should be rejected"
    return false

  -- U+FFFF via \uFFFF - rejected as non-ASCII (> 127)
  let nonchar4 := "\"\\uffff\""
  match parseJSONBytes (strToBytes nonchar4) with
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: U+FFFF - expected E115, got: {repr e}"
    return false
  | .ok _ =>
    IO.println "FAIL: U+FFFF - should be rejected"
    return false

  -- U+1FFFE (plane 1) via surrogate pair - rejected as non-ASCII (> 127)
  -- U+1FFFE = 0x1FFFE, surrogate pair: D83F DFFE
  let nonchar5 := "\"\\ud83f\\udffe\""
  match parseJSONBytes (strToBytes nonchar5) with
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: U+1FFFE - expected E115, got: {repr e}"
    return false
  | .ok _ =>
    IO.println "FAIL: U+1FFFE - should be rejected"
    return false

  IO.println "PASS: Non-ASCII codepoint rejection (ASCII-only profile)"
  return true

def testBMPEscapes : IO Bool := do
  -- ASCII-only profile: BMP escapes producing codepoints > 127 are rejected

  -- \u00E9 = é (U+00E9 = 233) - rejected as non-ASCII
  let escaped := "\"\\u00e9\""
  match parseJSONBytes (strToBytes escaped) with
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: BMP escape \\u00e9 - expected E115, got: {repr e}"
    return false
  | .ok _ =>
    IO.println "FAIL: BMP escape \\u00e9 - should be rejected as non-ASCII"
    return false

  -- ASCII escapes should still work: \u0048\u0065\u006c\u006c\u006f = "Hello"
  let multiEsc := "\"\\u0048\\u0065\\u006c\\u006c\\u006f\""  -- "Hello"
  match parseJSONBytes (strToBytes multiEsc) with
  | .ok (.str s) =>
    if s != "Hello" then
      IO.println s!"FAIL: ASCII escapes - expected Hello, got '{s}'"
      return false
  | .ok _ =>
    IO.println "FAIL: ASCII escapes - wrong type"
    return false
  | .error e =>
    IO.println s!"FAIL: ASCII escapes - unexpected error: {repr e}"
    return false

  -- \u007F (DEL, 127) - should pass (ASCII boundary)
  let del := "\"\\u007f\""
  match parseJSONBytes (strToBytes del) with
  | .ok (.str s) =>
    if s.length != 1 || s.get! ⟨0⟩ != Char.ofNat 0x7F then
      IO.println s!"FAIL: \\u007f - wrong value"
      return false
  | .ok _ =>
    IO.println "FAIL: \\u007f - wrong type"
    return false
  | .error e =>
    IO.println s!"FAIL: \\u007f - unexpected error: {repr e}"
    return false

  -- \u0080 (128) - should fail (first non-ASCII)
  let firstNonAscii := "\"\\u0080\""
  match parseJSONBytes (strToBytes firstNonAscii) with
  | .error (.E115_NonASCIICharacter _) => pure ()  -- Expected
  | .error e =>
    IO.println s!"FAIL: \\u0080 - expected E115, got: {repr e}"
    return false
  | .ok _ =>
    IO.println "FAIL: \\u0080 - should be rejected as non-ASCII"
    return false

  IO.println "PASS: BMP escapes (ASCII-only profile)"
  return true

def testUTF16CodeUnitSorting : IO Bool := do
  -- RFC 8785 §3.2.3 requires sorting by UTF-16 code units
  -- This matters for supplementary characters (> U+FFFF)

  -- Test 1: Simple ASCII sorting
  let simple := "{\"b\": 1, \"a\": 2}"
  match parseJSONBytes (strToBytes simple) with
  | .ok json =>
    let canonical := JCS.canonicalizeJson json
    if canonical != "{\"a\":2,\"b\":1}" then
      IO.println s!"FAIL: UTF-16 sort simple - got '{canonical}'"
      return false
  | .error e =>
    IO.println s!"FAIL: UTF-16 sort simple - error: {repr e}"
    return false

  -- Test 2: Keys that differ in UTF-16 vs code point order
  -- Per RFC 8785 example: "\u20ac" (€, U+20AC) vs "\ud834\udd1e" (𝄞, U+1D11E)
  -- In code point order: 𝄞 (0x1D11E) < € (0x20AC)
  -- In UTF-16 order: € (0x20AC) < 𝄞 (0xD834 0xDD1E) because 0x20AC < 0xD834
  -- So UTF-16 ordering puts € first, then 𝄞

  -- Test with the JCS functions directly using actual characters
  let euroStr := "€"  -- U+20AC
  let clefStr := "𝄞"  -- U+1D11E (surrogate pair D834 DD1E)

  -- UTF-16 comparison: € (20AC) should come before 𝄞 (D834 DD1E)
  let cmp := JCS.compareUTF16 euroStr clefStr
  if cmp != .lt then
    let cmpStr := match cmp with | .lt => "lt" | .eq => "eq" | .gt => "gt"
    IO.println s!"FAIL: UTF-16 sort euro vs clef - expected lt, got {cmpStr}"
    return false

  -- Verify reverse
  let cmp2 := JCS.compareUTF16 clefStr euroStr
  if cmp2 != .gt then
    let cmpStr := match cmp2 with | .lt => "lt" | .eq => "eq" | .gt => "gt"
    IO.println s!"FAIL: UTF-16 sort clef vs euro - expected gt, got {cmpStr}"
    return false

  IO.println "PASS: UTF-16 code unit sorting"
  return true

def testLowercaseHexEscapes : IO Bool := do
  -- JCS requires lowercase hex in \uXXXX escapes
  -- Test by creating a string with a control character and checking output

  -- Create a JSON value with a control character (ASCII 0x01)
  let ctrlStr := String.singleton (Char.ofNat 1)
  let json := JsonValue.str ctrlStr

  let canonical := JCS.canonicalizeJson json
  -- Should be "\u0001" with lowercase hex, not "\u0001" with uppercase
  if canonical != "\"\\u0001\"" then
    IO.println s!"FAIL: lowercase hex - expected \"\\u0001\", got '{canonical}'"
    return false

  -- Test with 0x0F (should produce \u000f)
  let ctrlF := String.singleton (Char.ofNat 0x0F)
  let jsonF := JsonValue.str ctrlF
  let canonicalF := JCS.canonicalizeJson jsonF
  if canonicalF != "\"\\u000f\"" then
    IO.println s!"FAIL: lowercase hex 0F - expected \"\\u000f\", got '{canonicalF}'"
    return false

  IO.println "PASS: Lowercase hex escapes"
  return true

def testNonASCIIEscapingInCanonicalizer : IO Bool := do
  -- ASCII-only profile: canonicalizer escapes non-ASCII as \uXXXX for defense-in-depth
  -- (Parser rejects non-ASCII, but canonicalizer handles it for completeness)

  -- Emoji 😀 (U+1F600) - should be escaped as surrogate pair \ud83d\ude00
  let emoji := "😀"  -- U+1F600
  let json := JsonValue.str emoji
  let canonical := JCS.canonicalizeJson json
  if canonical != "\"\\ud83d\\ude00\"" then
    IO.println s!"FAIL: emoji escape - expected \"\\ud83d\\ude00\", got '{canonical}'"
    return false

  -- Musical G clef 𝄞 (U+1D11E) - should be escaped as \ud834\udd1e
  let clef := "𝄞"
  let jsonClef := JsonValue.str clef
  let canonicalClef := JCS.canonicalizeJson jsonClef
  if canonicalClef != "\"\\ud834\\udd1e\"" then
    IO.println s!"FAIL: clef escape - expected \"\\ud834\\udd1e\", got '{canonicalClef}'"
    return false

  -- BMP non-ASCII € (U+20AC) - should be escaped as \u20ac
  let euro := "€"
  let jsonEuro := JsonValue.str euro
  let canonicalEuro := JCS.canonicalizeJson jsonEuro
  if canonicalEuro != "\"\\u20ac\"" then
    IO.println s!"FAIL: euro escape - expected \"\\u20ac\", got '{canonicalEuro}'"
    return false

  -- ASCII characters should NOT be escaped (except control chars)
  let ascii := "Hello, World!"
  let jsonAscii := JsonValue.str ascii
  let canonicalAscii := JCS.canonicalizeJson jsonAscii
  if canonicalAscii != "\"Hello, World!\"" then
    IO.println s!"FAIL: ASCII should not escape - expected \"Hello, World!\", got '{canonicalAscii}'"
    return false

  IO.println "PASS: Non-ASCII escaping in canonicalizer (ASCII-only profile)"
  return true

def testIsCanonicalRoundtrip : IO Bool := do
  -- Test that canonical JSON stays canonical
  -- Canonical form: no whitespace, sorted keys, no unnecessary escapes
  let canonical := "{\"a\":1,\"b\":2}"
  let canonicalBytes := strToBytes canonical
  match parseJSONBytes canonicalBytes with
  | .ok json =>
    if !JCS.isCanonical canonicalBytes json then
      IO.println "FAIL: isCanonical - canonical input should return true"
      return false
  | .error e =>
    IO.println s!"FAIL: isCanonical parse error: {repr e}"
    return false

  -- Non-canonical: has whitespace
  let nonCanonical1 := "{ \"a\" : 1 }"
  let nonCanonicalBytes1 := strToBytes nonCanonical1
  match parseJSONBytes nonCanonicalBytes1 with
  | .ok json =>
    if JCS.isCanonical nonCanonicalBytes1 json then
      IO.println "FAIL: isCanonical - whitespace should make it non-canonical"
      return false
  | .error e =>
    IO.println s!"FAIL: isCanonical parse error: {repr e}"
    return false

  -- Non-canonical: unsorted keys
  let nonCanonical2 := "{\"b\":2,\"a\":1}"
  let nonCanonicalBytes2 := strToBytes nonCanonical2
  match parseJSONBytes nonCanonicalBytes2 with
  | .ok json =>
    if JCS.isCanonical nonCanonicalBytes2 json then
      IO.println "FAIL: isCanonical - unsorted keys should make it non-canonical"
      return false
  | .error e =>
    IO.println s!"FAIL: isCanonical parse error: {repr e}"
    return false

  -- Non-canonical: uses \u escape for ASCII that could be literal
  -- (This is a bit contrived since literal and escaped ASCII are equivalent,
  -- but tests that escapes don't change the byte representation)
  let withEscape := "{\"s\":\"\\u0041\"}"  -- "A" via escape
  let withEscapeBytes := strToBytes withEscape
  match parseJSONBytes withEscapeBytes with
  | .ok json =>
    -- Canonical form is {"s":"A"} (literal), but input has escape
    -- The bytes differ, so isCanonical should return false
    if JCS.isCanonical withEscapeBytes json then
      IO.println "FAIL: isCanonical - \\u escape for A should make it non-canonical"
      return false
  | .error e =>
    IO.println s!"FAIL: isCanonical escape parse error: {repr e}"
    return false

  IO.println "PASS: isCanonical roundtrip"
  return true

/-! ## 9. DoS Protection Limit Tests -/

def testInputSizeLimit : IO Bool := do
  -- Test that input size limit is enforced
  let tinyLimits : Limits := { Limits.default with maxInputSize := 10 }
  let largeInput := strToBytes "{\"key\":\"this is too long\"}"  -- > 10 bytes

  match parseJSONBytesWithLimits largeInput tinyLimits with
  | .ok _ =>
    IO.println "FAIL: input size limit - expected E110, got Ok"
    return false
  | .error (.E110_InputTooLarge _ _) =>
    pure ()
  | .error e =>
    IO.println s!"FAIL: input size limit - expected E110, got {repr e}"
    return false

  -- Small input should pass
  let smallInput := strToBytes "1"
  if !(← expectSuccess "small input" (parseJSONBytesWithLimits smallInput tinyLimits)) then
    return false

  IO.println "PASS: Input size limit"
  return true

def testNestingDepthLimit : IO Bool := do
  -- Test that nesting depth limit is enforced
  let shallowLimits : Limits := { Limits.default with maxDepth := 3 }

  -- Depth 3: [[[]]] - should pass
  let depth3 := strToBytes "[[[]]]"
  if !(← expectSuccess "depth 3" (parseJSONBytesWithLimits depth3 shallowLimits)) then
    return false

  -- Depth 4: [[[[]]]] - should fail
  let depth4 := strToBytes "[[[[]]]]"
  match parseJSONBytesWithLimits depth4 shallowLimits with
  | .ok _ =>
    IO.println "FAIL: nesting limit - expected E111, got Ok"
    return false
  | .error (.E111_NestingTooDeep _ _) =>
    pure ()
  | .error e =>
    IO.println s!"FAIL: nesting limit - expected E111, got {repr e}"
    return false

  -- Object nesting also counts
  let objDepth4 := strToBytes "{\"a\":{\"b\":{\"c\":{\"d\":1}}}}"
  match parseJSONBytesWithLimits objDepth4 shallowLimits with
  | .ok _ =>
    IO.println "FAIL: object nesting limit - expected E111, got Ok"
    return false
  | .error (.E111_NestingTooDeep _ _) =>
    pure ()
  | .error e =>
    IO.println s!"FAIL: object nesting limit - expected E111, got {repr e}"
    return false

  IO.println "PASS: Nesting depth limit"
  return true

def testStringLengthLimit : IO Bool := do
  -- Test that string length limit is enforced
  let shortLimits : Limits := { Limits.default with maxStringLength := 5 }

  -- String of length 5 - should pass
  let ok5 := strToBytes "\"abcde\""
  if !(← expectSuccess "string len 5" (parseJSONBytesWithLimits ok5 shortLimits)) then
    return false

  -- String of length 6 - should fail
  let too6 := strToBytes "\"abcdef\""
  match parseJSONBytesWithLimits too6 shortLimits with
  | .ok _ =>
    IO.println "FAIL: string length limit - expected E112, got Ok"
    return false
  | .error (.E112_StringTooLong _ _) =>
    pure ()
  | .error e =>
    IO.println s!"FAIL: string length limit - expected E112, got {repr e}"
    return false

  IO.println "PASS: String length limit"
  return true

def testObjectFieldCountLimit : IO Bool := do
  -- Test that object field count limit is enforced
  let fewLimits : Limits := { Limits.default with maxObjectFields := 2 }

  -- 2 fields - should pass
  let obj2 := strToBytes "{\"a\":1,\"b\":2}"
  if !(← expectSuccess "2 fields" (parseJSONBytesWithLimits obj2 fewLimits)) then
    return false

  -- 3 fields - should fail
  let obj3 := strToBytes "{\"a\":1,\"b\":2,\"c\":3}"
  match parseJSONBytesWithLimits obj3 fewLimits with
  | .ok _ =>
    IO.println "FAIL: object field limit - expected E113, got Ok"
    return false
  | .error (.E113_TooManyFields _ _) =>
    pure ()
  | .error e =>
    IO.println s!"FAIL: object field limit - expected E113, got {repr e}"
    return false

  IO.println "PASS: Object field count limit"
  return true

def testArrayLengthLimit : IO Bool := do
  -- Test that array length limit is enforced
  let shortLimits : Limits := { Limits.default with maxArrayLength := 3 }

  -- 3 elements - should pass
  let arr3 := strToBytes "[1,2,3]"
  if !(← expectSuccess "3 elements" (parseJSONBytesWithLimits arr3 shortLimits)) then
    return false

  -- 4 elements - should fail
  let arr4 := strToBytes "[1,2,3,4]"
  match parseJSONBytesWithLimits arr4 shortLimits with
  | .ok _ =>
    IO.println "FAIL: array length limit - expected E114, got Ok"
    return false
  | .error (.E114_ArrayTooLong _ _) =>
    pure ()
  | .error e =>
    IO.println s!"FAIL: array length limit - expected E114, got {repr e}"
    return false

  IO.println "PASS: Array length limit"
  return true

def testDefaultLimitsAreSane : IO Bool := do
  -- Ensure default limits work for reasonable inputs
  -- 128 levels of nesting
  let mut deep128 := ""
  for _ in List.range 128 do
    deep128 := deep128 ++ "["
  deep128 := deep128 ++ "1"
  for _ in List.range 128 do
    deep128 := deep128 ++ "]"

  if !(← expectSuccess "128 nesting levels" (parseJSONBytes (strToBytes deep128))) then
    return false

  -- Large but reasonable object
  let mut objMany := "{"
  for i in List.range 100 do
    if i > 0 then objMany := objMany ++ ","
    objMany := objMany ++ s!"\"k{i}\":{i}"
  objMany := objMany ++ "}"

  if !(← expectSuccess "100 field object" (parseJSONBytes (strToBytes objMany))) then
    return false

  IO.println "PASS: Default limits are sane"
  return true

/-! ## 10. JCS Integration Tests -/

def testJCSCanonicalization : IO Bool := do
  -- Object with unsorted keys: {"b": 2, "a": 1}
  let unsorted := "{\"b\": 2, \"a\": 1}"
  match parseJSONBytes (strToBytes unsorted) with
  | .ok json =>
    let canonical := JCS.canonicalizeJson json
    if canonical != "{\"a\":1,\"b\":2}" then
      IO.println s!"FAIL: JCS sort - got '{canonical}'"
      return false
  | .error e =>
    IO.println s!"FAIL: JCS parse error: {repr e}"
    return false

  -- Whitespace normalization: { "key" : "value" }
  let spaced := "{ \"key\" : \"value\" }"
  match parseJSONBytes (strToBytes spaced) with
  | .ok json =>
    let canonical := JCS.canonicalizeJson json
    if canonical != "{\"key\":\"value\"}" then
      IO.println s!"FAIL: JCS whitespace - got '{canonical}'"
      return false
  | .error e =>
    IO.println s!"FAIL: JCS whitespace parse error: {repr e}"
    return false

  IO.println "PASS: JCS canonicalization"
  return true

/-! ## Test Runner -/

/-- Run all JSON parser tests. Returns (passed, failed) counts. -/
def runJSONTests : IO (Nat × Nat) := do
  IO.println "=== JSON Parser Tests ==="
  IO.println ""

  let mut passed := 0
  let mut failed := 0

  -- Lexer tests
  IO.println "--- Lexer ---"
  if ← testLexerBasicTokens then passed := passed + 1 else failed := failed + 1
  if ← testLexerStrings then passed := passed + 1 else failed := failed + 1
  if ← testLexerNumbers then passed := passed + 1 else failed := failed + 1
  if ← testLexerKeywords then passed := passed + 1 else failed := failed + 1

  -- Parser positive tests
  IO.println ""
  IO.println "--- Parser Positive ---"
  if ← testParserPrimitives then passed := passed + 1 else failed := failed + 1
  if ← testParserEmptyStructures then passed := passed + 1 else failed := failed + 1
  if ← testParserNestedStructures then passed := passed + 1 else failed := failed + 1
  if ← testParserComplexObject then passed := passed + 1 else failed := failed + 1

  -- Parser negative tests
  IO.println ""
  IO.println "--- Parser Negative ---"
  if ← testParserInvalidJSON then passed := passed + 1 else failed := failed + 1

  -- Number validation
  IO.println ""
  IO.println "--- Number Validation ---"
  if ← testNumberExponentRejection then passed := passed + 1 else failed := failed + 1
  if ← testNumberFractionRejection then passed := passed + 1 else failed := failed + 1
  if ← testNumberRangeValidation then passed := passed + 1 else failed := failed + 1
  if ← testBigNumberDoS then passed := passed + 1 else failed := failed + 1
  if ← testNonASCIIOutsideString then passed := passed + 1 else failed := failed + 1

  -- Duplicate key detection
  IO.println ""
  IO.println "--- Duplicate Keys ---"
  if ← testDuplicateKeyDetection then passed := passed + 1 else failed := failed + 1
  if ← testNestedDuplicateKeys then passed := passed + 1 else failed := failed + 1
  if ← testNoDuplicateKeyFalsePositives then passed := passed + 1 else failed := failed + 1

  -- BOM and edge cases
  IO.println ""
  IO.println "--- Edge Cases ---"
  if ← testBOMRejection then passed := passed + 1 else failed := failed + 1
  if ← testEdgeCases then passed := passed + 1 else failed := failed + 1
  if ← testDeepNesting then passed := passed + 1 else failed := failed + 1

  -- Unicode and UTF-16
  IO.println ""
  IO.println "--- Unicode and UTF-16 ---"
  if ← testSurrogatePairParsing then passed := passed + 1 else failed := failed + 1
  if ← testLoneSurrogateRejection then passed := passed + 1 else failed := failed + 1
  if ← testUTF8Decoding then passed := passed + 1 else failed := failed + 1
  if ← testInvalidUTF8Rejection then passed := passed + 1 else failed := failed + 1
  if ← testNoncharacterRejection then passed := passed + 1 else failed := failed + 1
  if ← testBMPEscapes then passed := passed + 1 else failed := failed + 1
  if ← testUTF16CodeUnitSorting then passed := passed + 1 else failed := failed + 1
  if ← testLowercaseHexEscapes then passed := passed + 1 else failed := failed + 1
  if ← testNonASCIIEscapingInCanonicalizer then passed := passed + 1 else failed := failed + 1
  if ← testIsCanonicalRoundtrip then passed := passed + 1 else failed := failed + 1

  -- DoS protection limits
  IO.println ""
  IO.println "--- DoS Protection Limits ---"
  if ← testInputSizeLimit then passed := passed + 1 else failed := failed + 1
  if ← testNestingDepthLimit then passed := passed + 1 else failed := failed + 1
  if ← testStringLengthLimit then passed := passed + 1 else failed := failed + 1
  if ← testObjectFieldCountLimit then passed := passed + 1 else failed := failed + 1
  if ← testArrayLengthLimit then passed := passed + 1 else failed := failed + 1
  if ← testDefaultLimitsAreSane then passed := passed + 1 else failed := failed + 1

  -- JCS integration
  IO.println ""
  IO.println "--- JCS Integration ---"
  if ← testJCSCanonicalization then passed := passed + 1 else failed := failed + 1

  return (passed, failed)

end Jolt.Tests.JSON
