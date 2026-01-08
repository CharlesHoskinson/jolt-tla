import Jolt.Errors
import Jolt.JSON.Types

/-!
# JCS-ASCII: ASCII-Only JSON Canonicalization

Implements a **consensus-critical ASCII-only profile** of JSON canonicalization
based on RFC 8785 (JCS), tailored for zkVM registry data.

## Profile Divergences from RFC 8259/8785

This is NOT a full RFC 8785 implementation. Key restrictions:
- **ASCII-only strings**: Non-ASCII codepoints (U+0080+) are rejected, not escaped
- **Integer-only numbers**: Fractions and exponents are rejected (E107/E108)
- **Safe integer range**: ±(2^53-1) enforced (E109)
- **Duplicate keys rejected**: E101 error (RFC 8259 allows implementation choice)

These restrictions ensure deterministic behavior across all implementations.

## Main Definitions
* `canonicalizeJson` - Recursively canonicalize a JSON value
* `canonicalizeBytes` - Get canonical UTF-8 bytes

## References
* RFC 8785: JSON Canonicalization Scheme (basis for key sorting/escaping)
* Jolt Spec §3.3 (defines ASCII-only profile)
-/

namespace Jolt.JSON.JCS

/-- Convert a string to its UTF-16 code unit representation as an Array.
    Uses Array for O(1) indexing during comparisons. -/
private def stringToUTF16Array (s : String) : Array UInt16 := Id.run do
  let mut units : Array UInt16 := #[]
  for c in s.toList do
    let n := c.toNat
    if n < 0x10000 then
      units := units.push n.toUInt16
    else
      -- Supplementary character: encode as surrogate pair
      let n' := n - 0x10000
      let high := (0xD800 + (n' >>> 10)).toUInt16
      let low := (0xDC00 + (n' &&& 0x3FF)).toUInt16
      units := units.push high
      units := units.push low
  units

/-- Compare two precomputed UTF-16 arrays lexicographically.
    O(min(m,n)) where m and n are the array lengths. -/
private def compareUTF16Arrays (a b : Array UInt16) : Ordering := Id.run do
  let minLen := min a.size b.size
  for i in [:minLen] do
    let au := a[i]!
    let bu := b[i]!
    if au < bu then return .lt
    if au > bu then return .gt
  return compare a.size b.size

/-- Compare two strings by UTF-16 code unit order per RFC 8785 §3.2.3.

RFC 8785 requires sorting keys by arrays of UTF-16 code units,
compared lexicographically as unsigned 16-bit integers.
This correctly handles supplementary characters (emoji, etc.) by
comparing their individual surrogate code units.

Note: For sorting multiple keys, use sortFields which precomputes
UTF-16 arrays to avoid redundant conversions. -/
def compareUTF16 (a b : String) : Ordering :=
  compareUTF16Arrays (stringToUTF16Array a) (stringToUTF16Array b)

/-- Sort object fields by key in UTF-16 code unit order.

Precomputes UTF-16 arrays for all keys once, then sorts using
the precomputed values. This avoids O(n log n) redundant string-to-UTF16
conversions that would occur if we converted during each comparison.

Complexity: O(n * k) for precomputation + O(n log n * k) for sorting,
where n = number of fields and k = average key length in UTF-16 units.
Without precomputation, each comparison would reconvert both keys. -/
def sortFields (fields : Array (String × JsonValue)) : Array (String × JsonValue) := Id.run do
  if fields.size <= 1 then return fields

  -- Precompute UTF-16 arrays for all keys: O(n * k)
  let keysWithUnits := fields.map (fun (k, v) => (stringToUTF16Array k, k, v))

  -- Sort by precomputed UTF-16 arrays: O(n log n) comparisons, O(k) per comparison
  let sorted := keysWithUnits.qsort (fun a b => compareUTF16Arrays a.1 b.1 == .lt)

  -- Extract original key-value pairs (discard precomputed arrays)
  sorted.map (fun (_, k, v) => (k, v))

/-- Convert a nibble (0-15) to a lowercase hex character.
    RFC 8785 requires lowercase hex for \uXXXX escapes. -/
private def nibbleToHexLower (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n)  -- '0'-'9'
  else Char.ofNat (0x61 + n - 10)       -- 'a'-'f' (lowercase!)

/-- Convert a list of characters to a string. -/
private def listToString (cs : List Char) : String :=
  cs.foldl (fun s c => s.push c) ""

/-- Format a 16-bit value as 4 lowercase hex digits. -/
private def toHex4Lower (n : Nat) : String :=
  let d0 := nibbleToHexLower ((n >>> 12) &&& 0xF)
  let d1 := nibbleToHexLower ((n >>> 8) &&& 0xF)
  let d2 := nibbleToHexLower ((n >>> 4) &&& 0xF)
  let d3 := nibbleToHexLower (n &&& 0xF)
  listToString [d0, d1, d2, d3]

/-- Escape a string for JSON output (ASCII-only profile).

ASCII-only escaping rules (modified from RFC 8785):
- Escape: \, ", and control chars (0x00-0x1F)
- Use \b, \f, \n, \r, \t for those specific controls
- Use \uXXXX with LOWERCASE hex for other control characters
- Do NOT escape / (forward slash)
- Non-ASCII characters (>= 0x80) are escaped as \uXXXX (defense-in-depth)

This ensures canonical output is always pure ASCII bytes.
Note: The parser rejects non-ASCII, so this escaping is defensive only.

Uses Array Char with O(1) amortized append to avoid O(n²) from string concatenation. -/
def escapeString (s : String) : String := Id.run do
  let mut chars : Array Char := #['"']  -- Start with opening quote
  for c in s.toList do
    let n := c.toNat
    if n == 0x22 then       -- "
      chars := chars.push '\\'
      chars := chars.push '"'
    else if n == 0x5C then  -- \
      chars := chars.push '\\'
      chars := chars.push '\\'
    else if n == 0x08 then  -- backspace
      chars := chars.push '\\'
      chars := chars.push 'b'
    else if n == 0x0C then  -- form feed
      chars := chars.push '\\'
      chars := chars.push 'f'
    else if n == 0x0A then  -- newline
      chars := chars.push '\\'
      chars := chars.push 'n'
    else if n == 0x0D then  -- carriage return
      chars := chars.push '\\'
      chars := chars.push 'r'
    else if n == 0x09 then  -- tab
      chars := chars.push '\\'
      chars := chars.push 't'
    else if n < 0x20 then   -- other control chars: \u00XX with lowercase hex
      chars := chars.push '\\'
      chars := chars.push 'u'
      chars := chars.push (nibbleToHexLower ((n >>> 12) &&& 0xF))
      chars := chars.push (nibbleToHexLower ((n >>> 8) &&& 0xF))
      chars := chars.push (nibbleToHexLower ((n >>> 4) &&& 0xF))
      chars := chars.push (nibbleToHexLower (n &&& 0xF))
    else if n >= 0x80 then
      -- Non-ASCII: escape as \uXXXX (defense-in-depth, parser rejects these)
      if n < 0x10000 then
        -- BMP character
        chars := chars.push '\\'
        chars := chars.push 'u'
        chars := chars.push (nibbleToHexLower ((n >>> 12) &&& 0xF))
        chars := chars.push (nibbleToHexLower ((n >>> 8) &&& 0xF))
        chars := chars.push (nibbleToHexLower ((n >>> 4) &&& 0xF))
        chars := chars.push (nibbleToHexLower (n &&& 0xF))
      else
        -- Supplementary character: surrogate pair
        let n' := n - 0x10000
        let high := 0xD800 + (n' >>> 10)
        let low := 0xDC00 + (n' &&& 0x3FF)
        chars := chars.push '\\'
        chars := chars.push 'u'
        chars := chars.push (nibbleToHexLower ((high >>> 12) &&& 0xF))
        chars := chars.push (nibbleToHexLower ((high >>> 8) &&& 0xF))
        chars := chars.push (nibbleToHexLower ((high >>> 4) &&& 0xF))
        chars := chars.push (nibbleToHexLower (high &&& 0xF))
        chars := chars.push '\\'
        chars := chars.push 'u'
        chars := chars.push (nibbleToHexLower ((low >>> 12) &&& 0xF))
        chars := chars.push (nibbleToHexLower ((low >>> 8) &&& 0xF))
        chars := chars.push (nibbleToHexLower ((low >>> 4) &&& 0xF))
        chars := chars.push (nibbleToHexLower (low &&& 0xF))
    else
      -- ASCII printable character (0x20-0x7F, excluding \ and " handled above)
      chars := chars.push c
  chars := chars.push '"'  -- Closing quote
  String.ofList chars.toList

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
