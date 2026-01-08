import Jolt.Oracle
import CLI.Schema.StateInput
import CLI.Report.Types
import CLI.Terminal.Doc
import CLI.Terminal.RenderPlain

/-!
# Digest Command

Compute StateDigestV1 from VMState + programHash.

## Usage
```
oracle digest <state.json>
```

## Input JSON Schema
```json
{
  "program_hash": "0x<64 hex chars>",
  "state": {
    "pc": 4096,
    "regs": [0, 1, 2, ...],  // 32 elements
    "step_counter": 100,
    "rw_mem_root": "0x<64 hex>",
    "io_root": "0x<64 hex>",
    "halted": 0,
    "exit_code": 0,
    "config_tags": [{"name": "0x...", "value": "0x..."}]
  }
}
```

## Output (--format=json)
```json
{"digest": "<decimal Fr string>"}
```
-/

namespace CLI.Commands

open Jolt
open CLI.Report
open CLI.Schema
open CLI.Terminal

/-- Convert Fr to decimal string. -/
def frToDecimal (f : Fr) : String := toString f.val

/-- Convert Bytes32 to 0x-prefixed lowercase hex. -/
def bytes32ToHex (b : Bytes32) : String := Id.run do
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

/-- Truncate hex for display (first 8 + ... + last 4). -/
def truncateHex (s : String) (maxLen : Nat := 20) : String :=
  if s.length <= maxLen then s
  else
    let prefixPart := s.take 12  -- 0x + 10 chars
    let suffixPart := s.drop (s.length - 4)
    prefixPart ++ "..." ++ suffixPart

/-- Run the digest command.

Returns (ExitCode, output string). -/
def runDigest (filePath : String) (format : OutputFormat := .pretty)
    (caps : Caps := Caps.plain) : IO (ExitCode × String) := do
  -- Read input file
  let bytes ← try
    let content ← IO.FS.readBinFile filePath
    pure content
  catch _ =>
    return (.ioError, formatError format "E900_FileNotFound" s!"Cannot read file: {filePath}" (some filePath))

  -- Parse JSON and extract state
  let input ← match parseDigestInputBytes bytes with
    | .ok i => pure i
    | .error e =>
      let report := ErrorReport.fromCode e
      return (exitCodeForError e, formatError format report.codeString report.message none)

  -- Compute digest
  let cfg := Oracle.init
  let digest ← match Oracle.computeStateDigest cfg input.programHash input.state with
    | .ok d => pure d
    | .error e =>
      let report := ErrorReport.fromCode e
      return (exitCodeForError e, formatError format report.codeString report.message none)

  -- Format output
  let output := formatSuccess format input.programHash digest caps
  return (.success, output)

where
  /-- Format error output based on format. -/
  formatError (format : OutputFormat) (code : String) (message : String)
      (path : Option String) : String :=
    match format with
    | .json | .ndjson =>
      let pathStr := match path with
        | some p => s!", \"path\": \"{p}\""
        | none => ""
      s!"\{\"status\": \"INVALID\", \"error\": \"{code}\", \"message\": \"{message}\"{pathStr}}\n"
    | .pretty | .plain =>
      let pathLine := match path with
        | some p => s!"\n  at: {p}"
        | none => ""
      s!"Error: {code}\n  {message}{pathLine}\n"

  /-- Format success output based on format. -/
  formatSuccess (format : OutputFormat) (programHash : Bytes32) (digest : Fr)
      (caps : Caps) : String :=
    let digestStr := frToDecimal digest
    match format with
    | .json | .ndjson =>
      s!"\{\"digest\": \"{digestStr}\"}\n"
    | .pretty | .plain =>
      let hashHex := bytes32ToHex programHash
      let doc := buildDigestDoc hashHex digestStr caps
      renderPlain doc

  /-- Build Doc for digest output. -/
  buildDigestDoc (programHash : String) (digest : String) (caps : Caps) : Doc :=
    let icons := selectIcons caps
    Doc.vcat [
      Doc.headerBar "Jolt Oracle" (some "digest"),
      Doc.line,
      Doc.keyValue [
        Doc.kvStr "Program Hash" (truncateHex programHash 40),
        Doc.kv "Digest" (Doc.crypto digest)
      ],
      Doc.line,
      Doc.status icons true "Computed successfully"
    ]

/-- Main entry point for digest command. -/
def digestMain (args : List String) : IO UInt32 := do
  match args with
  | [filePath] =>
    let (code, output) ← runDigest filePath .plain Caps.plain
    IO.print output
    return code.toUInt32
  | _ =>
    IO.println "Usage: oracle digest <state.json>"
    return 4

end CLI.Commands
