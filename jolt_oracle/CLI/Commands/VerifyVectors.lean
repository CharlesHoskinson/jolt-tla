import Jolt.Oracle
import CLI.Schema.TestVector
import CLI.Report.Types
import CLI.Terminal.Doc
import CLI.Terminal.RenderPlain
import CLI.Format.Json

/-!
# Verify Vectors Command

Run conformance test vectors.

## Usage
```
oracle verify vectors <vectors.json>
```

## Input JSON Schema
```json
{
  "vectors": [
    {
      "name": "basic_state_digest",
      "type": "state_digest",
      "input": { "program_hash": "...", "state": {...} },
      "expected": "<decimal Fr>"
    }
  ]
}
```

## Output (--format=json)
```json
{
  "passed": 10,
  "failed": 0,
  "results": [
    {"name": "basic_state_digest", "pass": true},
    {"name": "bad_case", "pass": false, "expected": "...", "got": "..."}
  ]
}
```
-/

namespace CLI.Commands

open Jolt
open CLI.Report
open CLI.Schema
open CLI.Terminal
open CLI.Format

/-- Convert Fr to decimal string. -/
private def frToDecimalVV (f : Fr) : String := toString f.val

/-- Run a single test vector and return the result. -/
def runVector (cfg : OracleConfig) (vec : TestVector) : VectorResult := Id.run do
  match vec.input, vec.expected with
  | .digestInput input, .fr expectedFr =>
    match Oracle.computeStateDigest cfg input.programHash input.state with
    | .ok gotFr =>
      if gotFr == expectedFr then
        VectorResult.mk vec.name true none none
      else
        VectorResult.mk vec.name false (some (frToDecimalVV expectedFr)) (some (frToDecimalVV gotFr))
    | .error _ =>
      VectorResult.mk vec.name false (some (frToDecimalVV expectedFr)) (some "ERROR")
  | .chainInput chain, .status expectedVerified =>
    match Oracle.verifyChain cfg chain with
    | .ok () =>
      if expectedVerified then
        VectorResult.mk vec.name true none none
      else
        VectorResult.mk vec.name false (some "MISMATCH") (some "VERIFIED")
    | .error _ =>
      if expectedVerified then
        VectorResult.mk vec.name false (some "VERIFIED") (some "MISMATCH")
      else
        VectorResult.mk vec.name true none none
  | _, _ =>
    -- Type mismatch between input and expected
    VectorResult.mk vec.name false (some "TYPE_MATCH") (some "TYPE_MISMATCH")

/-- Run the verify vectors command.

Returns (ExitCode, output string). -/
def runVerifyVectors (filePath : String) (format : OutputFormat := .pretty)
    (caps : Caps := Caps.plain) : IO (ExitCode × String) := do
  -- Read input file
  let bytes ← try
    let content ← IO.FS.readBinFile filePath
    pure content
  catch _ =>
    return (.ioError, formatVVError format "E900_FileNotFound"
      s!"Cannot read file: {filePath}")

  -- Parse JSON and extract vectors
  let vecFile ← match parseTestVectorBytes bytes with
    | .ok vf => pure vf
    | .error e =>
      let report := ErrorReport.fromCode e
      return (exitCodeForError e, formatVVError format report.codeString report.message)

  -- Run all vectors
  let cfg := Oracle.init
  let mut results : Array VectorResult := #[]
  for vec in vecFile.vectors do
    let result := runVector cfg vec
    results := results.push result

  -- Count pass/fail
  let passed := results.filter (·.pass) |>.size
  let failed := results.size - passed

  -- Determine exit code
  let exitCode := if failed == 0 then ExitCode.success else ExitCode.unhealthy

  -- Format output
  let output := formatVVSuccess format passed failed results caps
  return (exitCode, output)

where
  /-- Format error output based on format. -/
  formatVVError (format : OutputFormat) (code : String) (message : String) : String :=
    match format with
    | .json | .ndjson =>
      jsonObject [
        ("status", jsonString "ERROR"),
        ("error", jsonString code),
        ("message", jsonString message)
      ] ++ "\n"
    | .pretty | .plain =>
      s!"Error: {code}\n  {message}\n"

  /-- Format a single result for JSON. -/
  formatResultJson (r : VectorResult) : String :=
    if r.pass then
      jsonObject [("name", jsonString r.name), ("pass", "true")]
    else
      let basePairs := [("name", jsonString r.name), ("pass", "false")]
      let expectedPair := match r.expected with
        | some e => [("expected", jsonString e)]
        | none => []
      let gotPair := match r.got with
        | some g => [("got", jsonString g)]
        | none => []
      jsonObject (basePairs ++ expectedPair ++ gotPair)

  /-- Format success output based on format. -/
  formatVVSuccess (format : OutputFormat) (passed failed : Nat)
      (results : Array VectorResult) (caps : Caps) : String :=
    match format with
    | .json | .ndjson =>
      let resultStrs := results.map formatResultJson
      let resultsJson := "[" ++ String.intercalate ", " resultStrs.toList ++ "]"
      jsonObject [
        ("passed", jsonNat passed),
        ("failed", jsonNat failed),
        ("results", resultsJson)
      ] ++ "\n"
    | .pretty | .plain =>
      let doc := buildVVDoc passed failed results caps
      renderPlain doc

  /-- Build Doc for verify vectors output. -/
  buildVVDoc (passed failed : Nat) (results : Array VectorResult) (caps : Caps) : Doc :=
    let icons := selectIcons caps
    let total := passed + failed
    let allPassed := failed == 0

    -- Build result lines
    let resultDocs := results.toList.map fun r =>
      if r.pass then
        Doc.status icons true r.name
      else
        let detail := match r.expected, r.got with
          | some e, some g => s!" (expected: {e}, got: {g})"
          | _, _ => ""
        Doc.status icons false (r.name ++ detail)

    Doc.vcat ([
      Doc.headerBar "Jolt Oracle" (some "verify vectors"),
      Doc.line,
      Doc.keyValue [
        Doc.kvStr "Total" (toString total),
        Doc.kvStr "Passed" (toString passed),
        Doc.kvStr "Failed" (toString failed)
      ],
      Doc.line
    ] ++ resultDocs ++ [
      Doc.line,
      if allPassed then
        Doc.status icons true "All vectors passed"
      else
        Doc.status icons false s!"{failed} vector(s) failed"
    ])

/-- Main entry point for verify vectors command. -/
def verifyVectorsMain (args : List String) : IO UInt32 := do
  match args with
  | [filePath] =>
    let (code, output) ← runVerifyVectors filePath .plain Caps.plain
    IO.print output
    return code.toUInt32
  | _ =>
    IO.println "Usage: oracle verify vectors <vectors.json>"
    return 4

end CLI.Commands
