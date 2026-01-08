import Jolt.Field.Fr
import Jolt.Encoding.Bytes32
import CLI.Report.Types

/-!
# JSON Output Formatter

Machine-readable JSON output for CLI commands.
Follows JCS (JSON Canonicalization Scheme) for deterministic output.

## Key Points
* Keys sorted lexicographically
* No whitespace between tokens
* Fr values as decimal strings
* Bytes32 as 0x-prefixed lowercase hex
* Single JSON object per output (--format=json)
* Newline-delimited for streaming (--format=ndjson)
-/

namespace CLI.Format

open Jolt
open CLI.Report

/-- Escape a string for JSON output. -/
def escapeJsonString (s : String) : String := Id.run do
  let mut result := ""
  for c in s.toList do
    if c == '"' then result := result ++ "\\\""
    else if c == '\\' then result := result ++ "\\\\"
    else if c == '\n' then result := result ++ "\\n"
    else if c == '\r' then result := result ++ "\\r"
    else if c == '\t' then result := result ++ "\\t"
    else if c.toNat < 32 then
      -- Control characters as \uXXXX
      let hex := Nat.toDigits 16 c.toNat
      result := result ++ "\\u" ++ String.ofList ("0000".toList.drop hex.length ++ hex)
    else
      result := result.push c
  result

/-- Format a JSON string value. -/
def jsonString (s : String) : String := "\"" ++ escapeJsonString s ++ "\""

/-- Format an integer as JSON. -/
def jsonInt (n : Int) : String := toString n

/-- Format a natural number as JSON. -/
def jsonNat (n : Nat) : String := toString n

/-- Format a boolean as JSON. -/
def jsonBool (b : Bool) : String := if b then "true" else "false"

/-- Format Fr as decimal string (JSON string). -/
def jsonFr (f : Fr) : String := jsonString (toString f.val)

/-- Format Bytes32 as 0x-prefixed hex string (JSON string). -/
def jsonBytes32 (b : Bytes32) : String := Id.run do
  let mut hex := "0x"
  for i in [:32] do
    let byte := if i < b.data.size then b.data.data[i]!.toNat else 0
    let hi := if byte / 16 < 10 then Char.ofNat ('0'.toNat + byte / 16)
              else Char.ofNat ('a'.toNat + byte / 16 - 10)
    let lo := if byte % 16 < 10 then Char.ofNat ('0'.toNat + byte % 16)
              else Char.ofNat ('a'.toNat + byte % 16 - 10)
    hex := hex.push hi
    hex := hex.push lo
  jsonString hex

/-- Format a key-value pair. -/
def jsonKv (key : String) (value : String) : String :=
  jsonString key ++ ":" ++ value

/-- Format an object from key-value pairs.
    Keys are sorted lexicographically per JCS. -/
def jsonObject (pairs : List (String × String)) : String :=
  let sorted := pairs.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  let content := sorted.map (fun (k, v) => jsonKv k v)
  "{" ++ String.intercalate "," content ++ "}"

/-- Format an array of JSON values. -/
def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"

/-- Status strings (controlled vocabulary). -/
def statusString : VerifyStatus → String
  | .verified => "VERIFIED"
  | .mismatch => "MISMATCH"
  | .unknown => "UNKNOWN"

def healthString : HealthStatus → String
  | .healthy => "HEALTHY"
  | .degraded => "DEGRADED"
  | .unhealthy => "UNHEALTHY"

def validString : ValidStatus → String
  | .valid => "VALID"
  | .invalid => "INVALID"

/-- Format digest result as JSON. -/
def formatDigestJson (digest : Fr) : String :=
  jsonObject [("digest", jsonFr digest)] ++ "\n"

/-- Format digest error as JSON. -/
def formatDigestErrorJson (code : String) (message : String) (path : Option String) : String :=
  let basePairs := [
    ("status", jsonString "INVALID"),
    ("error", jsonString code),
    ("message", jsonString message)
  ]
  let pairs := match path with
    | some p => basePairs ++ [("path", jsonString p)]
    | none => basePairs
  jsonObject pairs ++ "\n"

/-- Format chain verification result as JSON. -/
def formatChainJson (report : ChainReport) : String :=
  let basePairs := [
    ("status", jsonString (statusString report.status)),
    ("chunks_verified", jsonNat report.chunksVerified)
  ]
  let errorPairs := match report.error with
    | some e => [("error", jsonString (ErrorReport.fromCode e).codeString)]
    | none => []
  let indexPairs := match report.failedChunkIndex with
    | some i => [("chunk_index", jsonNat i)]
    | none => []
  jsonObject (basePairs ++ errorPairs ++ indexPairs) ++ "\n"

/-- Format test vector result as JSON. -/
def formatTestVectorJson (result : TestVectorResult) : String :=
  let basePairs := [
    ("name", jsonString result.name),
    ("pass", jsonBool result.passed)
  ]
  let expectedPairs := match result.expected with
    | some e => [("expected", jsonString e)]
    | none => []
  let actualPairs := match result.actual with
    | some a => [("got", jsonString a)]
    | none => []
  jsonObject (basePairs ++ expectedPairs ++ actualPairs)

/-- Format test report as JSON. -/
def formatTestReportJson (report : TestReport) : String :=
  let results := report.results.toList.map formatTestVectorJson
  jsonObject [
    ("passed", jsonNat report.passed),
    ("failed", jsonNat report.failed),
    ("results", jsonArray results)
  ] ++ "\n"

/-- Format generic error as JSON. -/
def formatErrorJson (report : ErrorReport) : String :=
  let basePairs := [
    ("status", jsonString "INVALID"),
    ("error", jsonString report.codeString),
    ("message", jsonString report.message)
  ]
  let pathPairs := match report.path with
    | some p => [("path", jsonString p)]
    | none => []
  jsonObject (basePairs ++ pathPairs) ++ "\n"

/-- NDJSON event wrapper. -/
structure NdjsonEvent where
  event : String
  data : List (String × String) := []
  deriving Repr

/-- Format NDJSON event. -/
def formatNdjsonEvent (e : NdjsonEvent) : String :=
  let pairs := [("event", jsonString e.event)] ++ e.data.map (fun (k, v) => (k, v))
  jsonObject pairs ++ "\n"

end CLI.Format
