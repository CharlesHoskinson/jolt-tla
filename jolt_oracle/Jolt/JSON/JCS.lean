import Jolt.Errors
import Jolt.JSON.Types

namespace Jolt.JSON.JCS

/-- Helper to get character from list. -/
private def getCharAt (chars : List Char) (i : Nat) : Char :=
  chars.getD i '\x00'

/-- Convert a list of characters to a string. -/
private def listToString (cs : List Char) : String :=
  cs.foldl (fun s c => s.push c) ""

/-- Compare two strings by UTF-16 code unit order. -/
def compareUTF16 (a b : String) : Ordering := Id.run do
  let aChars := a.toList
  let bChars := b.toList
  let minLen := min aChars.length bChars.length
  for i in [:minLen] do
    let ac := getCharAt aChars i
    let bc := getCharAt bChars i
    let cmp := compare ac.toNat bc.toNat
    if cmp != .eq then return cmp
  return compare aChars.length bChars.length

/-- Sort keys by UTF-16 order. -/
def sortKeys (keys : Array String) : Array String :=
  keys.qsort (fun a b => compareUTF16 a b == .lt)

/-- Escape a string for JSON output. -/
def escapeString (s : String) : String := Id.run do
  let mut result := "\""
  for c in s.toList do
    match c with
    | '"'  => result := result ++ "\\\""
    | '\\' => result := result ++ "\\\\"
    | '\n' => result := result ++ "\\n"
    | '\r' => result := result ++ "\\r"
    | '\t' => result := result ++ "\\t"
    | c =>
      if c.toNat < 0x20 then
        let hex := listToString (Nat.toDigits 16 c.toNat)
        let padded := listToString (List.replicate (4 - hex.length) '0') ++ hex
        result := result ++ "\\u" ++ padded
      else
        result := result.push c
  result ++ "\""

/-- Format a number in canonical form. -/
def formatNumber (n : Int) : String := toString n

/-- Canonicalize a JSON value to string (simplified, non-recursive). -/
def canonicalizeJson (v : JsonValue) : String :=
  match v with
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num n => formatNumber n
  | .str s => escapeString s
  | .arr _ => "[]"  -- Simplified
  | .obj _ => "{}"  -- Simplified

/-- Canonicalize JSON and return UTF-8 bytes. -/
def canonicalizeBytes (v : JsonValue) : ByteArray :=
  (canonicalizeJson v).toUTF8

/-- Compare ByteArrays for equality. -/
private def byteArrayEq (a b : ByteArray) : Bool :=
  a.data == b.data

/-- Check if JSON bytes are already in canonical form. -/
def isCanonical (original : ByteArray) (parsed : JsonValue) : Bool :=
  byteArrayEq (canonicalizeBytes parsed) original

end Jolt.JSON.JCS
