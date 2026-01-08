import Jolt.Oracle
import CLI.Schema.StateInput
import CLI.Report.Types
import CLI.Terminal.Doc
import CLI.Terminal.RenderPlain
import CLI.Format.Json

/-!
# Diff Command

Compare two state files and show differences.

## Usage
```
oracle diff <expected.json> <actual.json>
```

## Output
Shows field-by-field comparison highlighting differences.
-/

namespace CLI.Commands

open Jolt
open Jolt.State
open CLI.Report
open CLI.Schema
open CLI.Terminal
open CLI.Format

/-- A single difference between two values. -/
structure FieldDiff where
  field : String
  expected : String
  actual : String
  deriving Repr

/-- Result of comparing two states. -/
structure DiffResult where
  identical : Bool
  diffs : List FieldDiff
  deriving Repr

/-- Convert Bytes32 to hex for comparison. -/
private def bytes32ToHexDiff (b : Bytes32) : String := Id.run do
  let mut result := "0x"
  for i in [:32] do
    let byte := if i < b.data.size then b.data.data[i]!.toNat else 0
    let hi := if byte / 16 < 10 then Char.ofNat ('0'.toNat + byte / 16)
              else Char.ofNat ('a'.toNat + byte / 16 - 10)
    let lo := if byte % 16 < 10 then Char.ofNat ('0'.toNat + byte % 16)
              else Char.ofNat ('a'.toNat + byte % 16 - 10)
    result := result.push hi
    result := result.push lo
  result

/-- Truncate long values for display. -/
private def truncateForDisplay (s : String) (maxLen : Nat := 40) : String :=
  if s.length <= maxLen then s
  else s.take 18 ++ "..." ++ s.drop (s.length - 18)

/-- Compare two VMStateV1 values. -/
def compareStates (expected actual : VMStateV1) : DiffResult := Id.run do
  let mut diffs : List FieldDiff := []

  -- Compare pc
  if expected.pc != actual.pc then
    diffs := diffs ++ [FieldDiff.mk "pc" (toString expected.pc) (toString actual.pc)]

  -- Compare step_counter
  if expected.stepCounter != actual.stepCounter then
    diffs := diffs ++ [FieldDiff.mk "step_counter" (toString expected.stepCounter) (toString actual.stepCounter)]

  -- Compare halted
  if expected.halted != actual.halted then
    diffs := diffs ++ [FieldDiff.mk "halted" (toString expected.halted) (toString actual.halted)]

  -- Compare exit_code
  if expected.exitCode != actual.exitCode then
    diffs := diffs ++ [FieldDiff.mk "exit_code" (toString expected.exitCode) (toString actual.exitCode)]

  -- Compare rw_mem_root
  if expected.rwMemRoot != actual.rwMemRoot then
    diffs := diffs ++ [FieldDiff.mk "rw_mem_root"
      (truncateForDisplay (bytes32ToHexDiff expected.rwMemRoot))
      (truncateForDisplay (bytes32ToHexDiff actual.rwMemRoot))]

  -- Compare io_root
  if expected.ioRoot != actual.ioRoot then
    diffs := diffs ++ [FieldDiff.mk "io_root"
      (truncateForDisplay (bytes32ToHexDiff expected.ioRoot))
      (truncateForDisplay (bytes32ToHexDiff actual.ioRoot))]

  -- Compare registers
  for i in [:32] do
    let expReg := if i < expected.regs.size then expected.regs[i]! else 0
    let actReg := if i < actual.regs.size then actual.regs[i]! else 0
    if expReg != actReg then
      diffs := diffs ++ [FieldDiff.mk s!"regs[{i}]" (toString expReg) (toString actReg)]

  -- Compare config_tags count
  if expected.configTags.size != actual.configTags.size then
    diffs := diffs ++ [FieldDiff.mk "config_tags.length"
      (toString expected.configTags.size)
      (toString actual.configTags.size)]

  DiffResult.mk diffs.isEmpty diffs

/-- Compare two DigestInput values (including program_hash). -/
def compareDigestInputs (expected actual : DigestInput) : DiffResult := Id.run do
  let mut diffs : List FieldDiff := []

  -- Compare program_hash
  if expected.programHash != actual.programHash then
    diffs := diffs ++ [FieldDiff.mk "program_hash"
      (truncateForDisplay (bytes32ToHexDiff expected.programHash))
      (truncateForDisplay (bytes32ToHexDiff actual.programHash))]

  -- Compare states
  let stateDiff := compareStates expected.state actual.state
  diffs := diffs ++ stateDiff.diffs

  DiffResult.mk diffs.isEmpty diffs

/-- Run the diff command.

Returns (ExitCode, output string). -/
def runDiff (expectedPath actualPath : String) (format : OutputFormat := .pretty)
    (caps : Caps := Caps.plain) : IO (ExitCode × String) := do
  -- Read expected file
  let expectedBytes ← try
    IO.FS.readBinFile expectedPath
  catch _ =>
    return (.ioError, formatDiffError format "E900_FileNotFound" s!"Cannot read file: {expectedPath}")

  -- Read actual file
  let actualBytes ← try
    IO.FS.readBinFile actualPath
  catch _ =>
    return (.ioError, formatDiffError format "E900_FileNotFound" s!"Cannot read file: {actualPath}")

  -- Parse expected
  let expected ← match parseDigestInputBytes expectedBytes with
    | .ok i => pure i
    | .error e =>
      let report := ErrorReport.fromCode e
      return (exitCodeForError e, formatDiffError format report.codeString s!"In {expectedPath}: {report.message}")

  -- Parse actual
  let actual ← match parseDigestInputBytes actualBytes with
    | .ok i => pure i
    | .error e =>
      let report := ErrorReport.fromCode e
      return (exitCodeForError e, formatDiffError format report.codeString s!"In {actualPath}: {report.message}")

  -- Compare
  let result := compareDigestInputs expected actual

  let output := match format with
    | .json | .ndjson =>
      if result.identical then
        jsonObject [
          ("status", jsonString "IDENTICAL"),
          ("differences", "0")
        ] ++ "\n"
      else
        let diffsJson := result.diffs.map fun d =>
          jsonObject [
            ("field", jsonString d.field),
            ("expected", jsonString d.expected),
            ("actual", jsonString d.actual)
          ]
        jsonObject [
          ("status", jsonString "DIFFERENT"),
          ("difference_count", jsonNat result.diffs.length),
          ("differences", "[" ++ String.intercalate ", " diffsJson ++ "]")
        ] ++ "\n"
    | .pretty | .plain =>
      let icons := selectIcons caps
      buildDiffOutput result icons expectedPath actualPath

  let exitCode := if result.identical then ExitCode.success else ExitCode.unhealthy
  pure (exitCode, output)

where
  formatDiffError (format : OutputFormat) (code : String) (message : String) : String :=
    match format with
    | .json | .ndjson =>
      jsonObject [
        ("status", jsonString "ERROR"),
        ("error", jsonString code),
        ("message", jsonString message)
      ] ++ "\n"
    | .pretty | .plain =>
      s!"Error: {code}\n  {message}\n"

  buildDiffOutput (result : DiffResult) (icons : IconSet) (expPath actPath : String) : String :=
    if result.identical then
      let doc := Doc.vcat [
        Doc.headerBar "Jolt Oracle" (some "diff"),
        Doc.line,
        Doc.keyValue [
          Doc.kvStr "Expected" expPath,
          Doc.kvStr "Actual" actPath
        ],
        Doc.line,
        Doc.status icons true "Files are identical"
      ]
      renderPlain doc
    else
      let diffDocs := result.diffs.map fun d =>
        Doc.vcat [
          Doc.plain s!"  {d.field}:",
          Doc.plain s!"    expected: {d.expected}",
          Doc.plain s!"    actual:   {d.actual}"
        ]
      let doc := Doc.vcat ([
        Doc.headerBar "Jolt Oracle" (some "diff"),
        Doc.line,
        Doc.keyValue [
          Doc.kvStr "Expected" expPath,
          Doc.kvStr "Actual" actPath,
          Doc.kvStr "Differences" (toString result.diffs.length)
        ],
        Doc.line
      ] ++ diffDocs ++ [
        Doc.line,
        Doc.status icons false s!"{result.diffs.length} difference(s) found"
      ])
      renderPlain doc

/-- Main entry point for diff command. -/
def diffMain (args : List String) : IO UInt32 := do
  match args with
  | [expectedPath, actualPath] =>
    let (code, output) ← runDiff expectedPath actualPath .plain Caps.plain
    IO.print output
    return code.toUInt32
  | _ =>
    IO.println "Usage: oracle diff <expected.json> <actual.json>"
    IO.println ""
    IO.println "Compares two state files and shows differences."
    IO.println "Input files should be in digest command format:"
    IO.println "  { \"program_hash\": \"0x...\", \"state\": { ... } }"
    return 4

end CLI.Commands
