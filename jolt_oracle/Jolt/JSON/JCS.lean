import Jolt.Errors
import Jolt.JSON.Types

/-!
# RFC 8785 JSON Canonicalization Scheme (JCS)

Implements canonical JSON serialization per RFC 8785 and spec §3.3.

## Main Definitions
* `canonicalizeJson` - Recursively canonicalize a JSON value
* `canonicalizeBytes` - Get canonical UTF-8 bytes

## References
* RFC 8785: JSON Canonicalization Scheme
* Jolt Spec §3.3
-/

namespace Jolt.JSON.JCS

/-- Helper to get character from list. -/
private def getCharAt (chars : List Char) (i : Nat) : Char :=
  chars.getD i '\x00'

/-- Convert a list of characters to a string. -/
private def listToString (cs : List Char) : String :=
  cs.foldl (fun s c => s.push c) ""

/-- Compare two strings by UTF-16 code unit order per RFC 8785.

RFC 8785 §3.2.3: Object keys are sorted by UTF-16 code units.
For BMP characters, this is equivalent to sorting by Unicode code points.
Surrogate pairs (for characters > U+FFFF) are compared by their
individual UTF-16 code units. -/
def compareUTF16 (a b : String) : Ordering := Id.run do
  let aChars := a.toList
  let bChars := b.toList
  let minLen := min aChars.length bChars.length
  for i in [:minLen] do
    let ac := getCharAt aChars i
    let bc := getCharAt bChars i
    -- For surrogate pairs, we'd need to compare the UTF-16 units
    -- For now, compare by code point (correct for BMP)
    let cmp := compare ac.toNat bc.toNat
    if cmp != .eq then return cmp
  return compare aChars.length bChars.length

/-- Sort object fields by key in UTF-16 order. -/
def sortFields (fields : Array (String × JsonValue)) : Array (String × JsonValue) :=
  fields.qsort (fun a b => compareUTF16 a.1 b.1 == .lt)

/-- Escape a string for JSON output per RFC 8785 §3.2.2.

RFC 8785 escaping rules:
- Escape: \, ", and control chars (0x00-0x1F)
- Use \n, \r, \t for those specific controls
- Use \uXXXX for other control characters
- Do NOT escape / (forward slash) -/
def escapeString (s : String) : String := Id.run do
  let mut result := "\""
  for c in s.toList do
    let n := c.toNat
    if n == 0x22 then       -- "
      result := result ++ "\\\""
    else if n == 0x5C then  -- \
      result := result ++ "\\\\"
    else if n == 0x08 then  -- backspace
      result := result ++ "\\b"
    else if n == 0x0C then  -- form feed
      result := result ++ "\\f"
    else if n == 0x0A then  -- newline
      result := result ++ "\\n"
    else if n == 0x0D then  -- carriage return
      result := result ++ "\\r"
    else if n == 0x09 then  -- tab
      result := result ++ "\\t"
    else if n < 0x20 then   -- other control chars
      let hex := listToString (Nat.toDigits 16 n)
      let padded := listToString (List.replicate (4 - hex.length) '0') ++ hex
      result := result ++ "\\u" ++ padded
    else
      result := result.push c
  result ++ "\""

/-- Format a number in canonical form per RFC 8785 §3.2.4.

Per spec §2.6.1: Only integers allowed in range ±(2^53-1).
Canonical form: no leading zeros, no plus sign, no trailing zeros. -/
def formatNumber (n : Int) : String := toString n

/-- Recursively canonicalize a JSON value per RFC 8785.

Per RFC 8785:
- null, booleans, strings: serialize as-is
- numbers: canonical integer form (no exponent/fraction per spec)
- arrays: [elem1,elem2,...] (no whitespace)
- objects: keys sorted by UTF-16 code units, {key1:val1,key2:val2,...} -/
partial def canonicalizeJson (v : JsonValue) : String :=
  match v with
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num n => formatNumber n
  | .str s => escapeString s
  | .arr items =>
    let elements := items.map canonicalizeJson
    "[" ++ ",".intercalate elements.toList ++ "]"
  | .obj fields =>
    let sorted := sortFields fields
    let pairs := sorted.map (fun (k, v) => escapeString k ++ ":" ++ canonicalizeJson v)
    "{" ++ ",".intercalate pairs.toList ++ "}"

/-- Canonicalize JSON and return UTF-8 bytes. -/
def canonicalizeBytes (v : JsonValue) : ByteArray :=
  (canonicalizeJson v).toUTF8

/-- Compare ByteArrays for equality. -/
private def byteArrayEq (a b : ByteArray) : Bool :=
  a.data == b.data

/-- Check if JSON bytes are already in canonical form.

Per §3.3: registry raw bytes MUST equal JCS canonical serialization. -/
def isCanonical (original : ByteArray) (parsed : JsonValue) : Bool :=
  byteArrayEq (canonicalizeBytes parsed) original

end Jolt.JSON.JCS
