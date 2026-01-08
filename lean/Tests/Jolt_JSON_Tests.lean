import Std
import Jolt.Errors
import Jolt.JSON.Parser
import Jolt.JSON.JCS

open Std

namespace Jolt.JSON.Tests

open Jolt.JSON
open Jolt.JSON.JCS

/-- Convenience: make a UInt8 from a Nat literal. -/
def u8 (n : Nat) : UInt8 := UInt8.ofNat n

/-- Build a ByteArray from a list of Nat byte values. -/
def bytes (ns : List Nat) : ByteArray :=
  ByteArray.mk <| ns.toArray.map u8

/-- Single-codepoint string. -/
def strCp (cp : Nat) : String :=
  String.singleton (Char.ofNat cp)

/-- Quote a string as a JSON string literal *without escaping*.
    Use only for test strings that contain no U+0000..U+001F, '"' or '\' . -/
def quoteRaw (s : String) : String :=
  "\"" ++ s ++ "\""

def assert (name : String) (cond : Bool) : IO Unit := do
  if cond then
    pure ()
  else
    throw <| IO.userError s!"[FAIL] {name}"

def assertEq (name : String) (got expected : String) : IO Unit := do
  if got == expected then
    pure ()
  else
    throw <| IO.userError s!"[FAIL] {name}\n  expected: {expected}\n  got:      {got}"

def assertOkStr (name : String) (r : OracleResult JsonValue) (expected : String) : IO Unit := do
  match r with
  | .ok (.str s) =>
      assertEq name s expected
  | .ok v =>
      throw <| IO.userError s!"[FAIL] {name}\n  expected: JsonValue.str ...\n  got:      {repr v}"
  | .error e =>
      throw <| IO.userError s!"[FAIL] {name}\n  expected: ok\n  got err:  {repr e}"

def assertErr {α : Type} (name : String) (r : OracleResult α) (expected : ErrorCode) : IO Unit := do
  match r with
  | .ok _ =>
      throw <| IO.userError s!"[FAIL] {name}\n  expected err: {repr expected}\n  got: ok"
  | .error e =>
      if decide (e = expected) then
        pure ()
      else
        throw <| IO.userError s!"[FAIL] {name}\n  expected err: {repr expected}\n  got err:      {repr e}"

def assertCanon (name : String) (json : String) (expected : String) : IO Unit := do
  match parseJSONBytes json.toUTF8 with
  | .ok v =>
      let got := canonicalizeJson v
      assertEq name got expected
  | .error e =>
      throw <| IO.userError s!"[FAIL] {name}\n  expected: parse ok\n  got err:  {repr e}"

def assertCompare (name : String) (a b : String) (expected : Ordering) : IO Unit := do
  let got := compareUTF16 a b
  if got == expected then
    pure ()
  else
    throw <| IO.userError s!"[FAIL] {name}\n  expected: {expected}\n  got:      {got}"

/-!
## TESTS

Run with (example):
  lake env lean --run Jolt/JSON/Tests.lean

Notes:
- The lexer currently implements a fail-closed policy for consensus safety:
  raw non-ASCII bytes in string literals are rejected.
- JCS canonicalization must still follow RFC 8785 serialization rules:
  Unicode outside U+0000..U+001F (except `"` and `\`) is emitted "as is". -/

def main : IO Unit := do
  ---------------------------------------------------------------------------
  -- UTF-8 / byte-level policy
  ---------------------------------------------------------------------------
  -- Raw non-ASCII in string literals is rejected (fail-closed policy).
  assertErr "utf8: raw non-ASCII byte rejected"
    (parseJSONBytes "\"é\"".toUTF8) ErrorCode.E100_InvalidJSON

  -- Invalid UTF-8 is also rejected (and this test ensures we don't accidentally
  -- treat bytes as Latin-1 and accept garbage).
  -- Bytes: 0x22 " , 0xC3 (start 2-byte), 0x28 (invalid continuation), 0x22 "
  let badUtf8 := bytes [0x22, 0xC3, 0x28, 0x22]
  assertErr "utf8: invalid byte sequence rejected"
    (parseJSONBytes badUtf8) ErrorCode.E100_InvalidJSON

  -- Unicode via \u escapes is accepted and decoded.
  assertOkStr "unicode: \\u00e9 parses to é"
    (parseJSONBytes "\"\\u00e9\"".toUTF8) "é"

  ---------------------------------------------------------------------------
  -- \uXXXX decoding + surrogate handling (must reject lone surrogates)
  ---------------------------------------------------------------------------
  let gClef : String := strCp 0x1D11E  -- U+1D11E MUSICAL SYMBOL G CLEF

  -- Valid surrogate pair: \uD834\uDD1E => U+1D11E
  assertOkStr "surrogates: valid pair combines"
    (parseJSONBytes "\"\\uD834\\uDD1E\"".toUTF8) gClef

  -- Lone surrogates must be rejected.
  assertErr "surrogates: lone high surrogate rejected"
    (parseJSONBytes "\"\\uD800\"".toUTF8) ErrorCode.E100_InvalidJSON
  assertErr "surrogates: lone low surrogate rejected"
    (parseJSONBytes "\"\\uDC00\"".toUTF8) ErrorCode.E100_InvalidJSON

  -- High surrogate not followed by low surrogate must be rejected.
  assertErr "surrogates: bad pair rejected"
    (parseJSONBytes "\"\\uD800\\u0041\"".toUTF8) ErrorCode.E100_InvalidJSON

  ---------------------------------------------------------------------------
  -- RFC 8785 string serialization rules (emit Unicode "as is")
  ---------------------------------------------------------------------------
  let emoji : String := strCp 0x1F600  -- 😀
  assertCanon "jcs: emoji emitted as-is (not surrogate escapes)"
    "\"\\uD83D\\uDE00\"" (quoteRaw emoji)

  assertCanon "jcs: non-BMP emitted as-is (G clef)"
    "\"\\uD834\\uDD1E\"" (quoteRaw gClef)

  -- Control chars: use short escapes where required.
  assertCanon "jcs: newline uses \\n"
    "\"\\u000A\"" "\"\\n\""
  assertCanon "jcs: carriage return uses \\r"
    "\"\\u000D\"" "\"\\r\""

  -- Other control chars: \uXXXX with lowercase hex.
  assertCanon "jcs: lowercase hex in \\uXXXX"
    "\"\\u000B\"" "\"\\u000b\""

  -- Forward slash must not be escaped.
  assertCanon "jcs: / not escaped"
    "\"\\/\"" "\"/\""

  ---------------------------------------------------------------------------
  -- UTF-16 key sorting (RFC 8785 §3.2.3)
  ---------------------------------------------------------------------------
  let priv : String := strCp 0xE000   -- U+E000, UTF-16 single unit 0xE000

  -- UTF-16 code-unit compare should order emoji (0xD83D...) before U+E000 (0xE000).
  assertCompare "utf16: compareUTF16 emoji < priv" emoji priv .lt

  -- Canonical object output must reflect UTF-16 ordering of keys.
  -- Input keys are provided via escapes so the test does not depend on raw UTF-8 decoding.
  let objInput := "{\"\\uE000\":1,\"\\uD83D\\uDE00\":2}"
  let expectedSorted := "{" ++ quoteRaw emoji ++ ":2," ++ quoteRaw priv ++ ":1}"
  assertCanon "utf16: canonicalize sorts keys by UTF-16" objInput expectedSorted

  -- Full RFC 8785 sorting test vector: validate value order after sortFields.
  -- (Expected order listed in RFC 8785, Section 3.2.3).  See:
  -- "Expected argument order after sorting property strings".
  let rfcSortInput :=
    "{"
    ++ "\"\\u20ac\":\"Euro Sign\","
    ++ "\"\\r\":\"Carriage Return\","
    ++ "\"\\ufb33\":\"Hebrew Letter Dalet With Dagesh\","
    ++ "\"1\":\"One\","
    ++ "\"\\ud83d\\ude00\":\"Emoji: Grinning Face\","
    ++ "\"\\u0080\":\"Control\","
    ++ "\"\\u00f6\":\"Latin Small Letter O With Diaeresis\""
    ++ "}"

  match parseJSONBytes rfcSortInput.toUTF8 with
  | .error e =>
      throw <| IO.userError s!"[FAIL] rfc sort vector: parse failed: {repr e}"
  | .ok v =>
      match v with
      | .obj fields =>
          let sorted := sortFields fields
          let values :=
            sorted.map (fun (_, jv) =>
              match jv with
              | .str s => s
              | _ => "<non-string>")
          let expected : Array String :=
            #[
              "Carriage Return",
              "One",
              "Control",
              "Latin Small Letter O With Diaeresis",
              "Euro Sign",
              "Emoji: Grinning Face",
              "Hebrew Letter Dalet With Dagesh"
            ]
          assert "rfc sort vector: value order matches RFC 8785" (values == expected)
      | _ =>
          throw <| IO.userError "[FAIL] rfc sort vector: expected object"

  ---------------------------------------------------------------------------
  -- Number validation: exponent/fraction/range
  ---------------------------------------------------------------------------
  assertErr "numbers: exponent rejected"
    (parseJSONBytes "1e2".toUTF8) ErrorCode.E107_ExponentNotation
  assertErr "numbers: fraction rejected"
    (parseJSONBytes "1.5".toUTF8) ErrorCode.E108_FractionalNumber
  assertErr "numbers: out-of-range rejected"
    (parseJSONBytes "9007199254740992".toUTF8) ErrorCode.E109_IntegerOutOfRange

  ---------------------------------------------------------------------------
  -- Duplicate key rejection
  ---------------------------------------------------------------------------
  assertErr "objects: duplicate keys rejected"
    (parseJSONBytes "{\"a\":1,\"a\":2}".toUTF8) (ErrorCode.E101_DuplicateKey "a")

  ---------------------------------------------------------------------------
  -- BOM rejection
  ---------------------------------------------------------------------------
  let bomObj := bytes [0xEF,0xBB,0xBF,0x7B,0x7D]  -- BOM + "{}"
  assertErr "bytes: UTF-8 BOM rejected"
    (parseJSONBytes bomObj) ErrorCode.E100_InvalidJSON

  ---------------------------------------------------------------------------
  -- isCanonical sanity checks
  ---------------------------------------------------------------------------
  let canon := "{\"a\":1,\"b\":2}"
  match parseJSONBytes canon.toUTF8 with
  | .ok v =>
      assert "isCanonical: canonical input returns true" (isCanonical canon.toUTF8 v)
  | .error e =>
      throw <| IO.userError s!"[FAIL] isCanonical: parse failed: {repr e}"

  let notCanon := "{\"b\":2,\"a\":1}"
  match parseJSONBytes notCanon.toUTF8 with
  | .ok v =>
      assert "isCanonical: non-canonical input returns false" (!isCanonical notCanon.toUTF8 v)
  | .error e =>
      throw <| IO.userError s!"[FAIL] isCanonical: parse failed: {repr e}"

  IO.println "[OK] all JSON/JCS tests passed"

end Jolt.JSON.Tests
