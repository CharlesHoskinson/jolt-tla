import Jolt.Oracle
import CLI.Schema.StateInput
import CLI.Schema.ChainInput
import CLI.Report.Types
import CLI.Format.Json

/-!
# Generate Command

Generate conformance test vectors from input files.

## Usage
```
oracle generate <type> <input.json> [-o <output.json>]
oracle generate state_digest <state.json>
oracle generate chain <chain.json>
```

## Supported Types
- `state_digest`: Generate digest test vector from state input
- `chain`: Generate chain verification test vector

## Output
Produces a test vector JSON that can be used with `oracle verify vectors`.

```json
{
  "vectors": [
    {
      "name": "<filename>",
      "type": "state_digest",
      "input": { ... },
      "expected": "<computed result>"
    }
  ]
}
```
-/

namespace CLI.Commands

open Jolt
open CLI.Report
open CLI.Schema
open CLI.Format

/-- Convert Fr to decimal string for generate output. -/
private def frToDecimalGen (f : Fr) : String := toString f.val

/-- Escape a string for JSON output. -/
private def escapeJsonString (s : String) : String := Id.run do
  let mut result := ""
  for c in s.toList do
    if c == '"' then result := result ++ "\\\""
    else if c == '\\' then result := result ++ "\\\\"
    else if c == '\n' then result := result ++ "\\n"
    else if c == '\r' then result := result ++ "\\r"
    else if c == '\t' then result := result ++ "\\t"
    else result := result.push c
  result

/-- Convert Bytes32 to canonical hex string. -/
private def bytes32ToHexGen (b : Bytes32) : String := Id.run do
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

/-- Convert ByteArray to hex string. -/
private def bytesToHexGen (bytes : ByteArray) : String := Id.run do
  let mut result := "0x"
  for i in [:bytes.size] do
    let byte := bytes.data[i]!.toNat
    let hi := if byte / 16 < 10 then Char.ofNat ('0'.toNat + byte / 16)
              else Char.ofNat ('a'.toNat + byte / 16 - 10)
    let lo := if byte % 16 < 10 then Char.ofNat ('0'.toNat + byte % 16)
              else Char.ofNat ('a'.toNat + byte % 16 - 10)
    result := result.push hi
    result := result.push lo
  result

/-- Serialize VMStateV1 to JSON string. -/
private def serializeVMState (state : Jolt.State.VMStateV1) : String :=
  let regsStr := "[" ++ String.intercalate ", " (state.regs.toList.map toString) ++ "]"
  let configTagsStr := if state.configTags.isEmpty then "[]"
    else
      let tags := state.configTags.toList.map fun tag =>
        jsonObject [
          ("name", jsonString (bytesToHexGen tag.name)),
          ("value", jsonString (bytesToHexGen tag.value))
        ]
      "[" ++ String.intercalate ", " tags ++ "]"
  jsonObject [
    ("pc", jsonNat state.pc.toNat),
    ("regs", regsStr),
    ("step_counter", jsonNat state.stepCounter.toNat),
    ("rw_mem_root", jsonString (bytes32ToHexGen state.rwMemRoot)),
    ("io_root", jsonString (bytes32ToHexGen state.ioRoot)),
    ("halted", jsonNat state.halted.toNat),
    ("exit_code", jsonNat state.exitCode.toNat),
    ("config_tags", configTagsStr)
  ]

/-- Serialize DigestInput to JSON string. -/
private def serializeDigestInput (input : DigestInput) : String :=
  jsonObject [
    ("program_hash", jsonString (bytes32ToHexGen input.programHash)),
    ("state", serializeVMState input.state)
  ]

/-- Serialize Chunk to JSON string. -/
private def serializeChunk (chunk : Chunk) : String :=
  jsonObject [
    ("index", jsonNat chunk.index),
    ("start_state", serializeVMState chunk.startState),
    ("end_state", serializeVMState chunk.endState),
    ("start_digest", jsonString (frToDecimalGen chunk.startDigest)),
    ("end_digest", jsonString (frToDecimalGen chunk.endDigest))
  ]

/-- Serialize Chain to JSON string. -/
private def serializeChain (chain : Chain) : String :=
  let chunksStr := "[" ++ String.intercalate ", " (chain.chunks.toList.map serializeChunk) ++ "]"
  jsonObject [
    ("program_hash", jsonString (bytes32ToHexGen chain.programHash)),
    ("chunks", chunksStr)
  ]

/-- Extract base name from file path. -/
private def baseName (path : String) : String :=
  let parts := path.splitOn "/"
  let lastPart := parts.getLast!
  let winParts := lastPart.splitOn "\\"
  let fileName := winParts.getLast!
  -- Remove extension
  let dotParts := fileName.splitOn "."
  if dotParts.length > 1 then
    String.intercalate "." (dotParts.dropLast)
  else
    fileName

/-- Generate a state_digest test vector. -/
def generateStateDigest (filePath : String) : IO (ExitCode × String) := do
  -- Read input file
  let bytes ← try
    IO.FS.readBinFile filePath
  catch _ =>
    return (.ioError, formatGenError "E900_FileNotFound" s!"Cannot read file: {filePath}")

  -- Parse input
  let input ← match parseDigestInputBytes bytes with
    | .ok i => pure i
    | .error e =>
      let report := ErrorReport.fromCode e
      return (exitCodeForError e, formatGenError report.codeString report.message)

  -- Compute digest
  let cfg := Oracle.init
  let digest ← match Oracle.computeStateDigest cfg input.programHash input.state with
    | .ok d => pure d
    | .error e =>
      let report := ErrorReport.fromCode e
      return (exitCodeForError e, formatGenError report.codeString report.message)

  -- Build test vector output
  let vectorName := baseName filePath
  let vector := jsonObject [
    ("name", jsonString vectorName),
    ("type", jsonString "state_digest"),
    ("input", serializeDigestInput input),
    ("expected", jsonString (frToDecimalGen digest))
  ]

  let output := jsonObject [("vectors", "[" ++ vector ++ "]")] ++ "\n"
  return (.success, output)

where
  formatGenError (code : String) (message : String) : String :=
    jsonObject [
      ("status", jsonString "ERROR"),
      ("error", jsonString code),
      ("message", jsonString message)
    ] ++ "\n"

/-- Generate a chain test vector. -/
def generateChain (filePath : String) : IO (ExitCode × String) := do
  -- Read input file
  let bytes ← try
    IO.FS.readBinFile filePath
  catch _ =>
    return (.ioError, formatGenError "E900_FileNotFound" s!"Cannot read file: {filePath}")

  -- Parse chain
  let chain ← match parseChainBytes bytes with
    | .ok c => pure c
    | .error e =>
      let report := ErrorReport.fromCode e
      return (exitCodeForError e, formatGenError report.codeString report.message)

  -- Verify chain to get result
  let cfg := Oracle.init
  let expectedStatus := match Oracle.verifyChain cfg chain with
    | .ok () => "VERIFIED"
    | .error _ => "MISMATCH"

  -- Build test vector output
  let vectorName := baseName filePath
  let vector := jsonObject [
    ("name", jsonString vectorName),
    ("type", jsonString "chain"),
    ("input", serializeChain chain),
    ("expected", jsonString expectedStatus)
  ]

  let output := jsonObject [("vectors", "[" ++ vector ++ "]")] ++ "\n"
  return (.success, output)

where
  formatGenError (code : String) (message : String) : String :=
    jsonObject [
      ("status", jsonString "ERROR"),
      ("error", jsonString code),
      ("message", jsonString message)
    ] ++ "\n"

/-- Run the generate command.

Returns (ExitCode, output string). -/
def runGenerate (vectorType : String) (inputPath : String)
    (outputPath : Option String) : IO (ExitCode × String) := do
  let (code, output) ← match vectorType with
    | "state_digest" => generateStateDigest inputPath
    | "chain" => generateChain inputPath
    | _ =>
      pure (.invalid, jsonObject [
        ("status", jsonString "ERROR"),
        ("error", jsonString "E106_UnexpectedType"),
        ("message", jsonString s!"Unknown vector type: {vectorType}. Supported: state_digest, chain")
      ] ++ "\n")

  -- Write to file if output path specified
  match outputPath with
  | some path =>
    if code == .success then
      try
        IO.FS.writeFile path output
        pure (code, s!"Generated test vector written to: {path}\n")
      catch _ =>
        pure (.ioError, s!"Error: Cannot write to file: {path}\n")
    else
      pure (code, output)
  | none =>
    pure (code, output)

/-- Main entry point for generate command. -/
def generateMain (args : List String) : IO UInt32 := do
  match args with
  | [vectorType, inputPath] =>
    let (code, output) ← runGenerate vectorType inputPath none
    IO.print output
    return code.toUInt32
  | [vectorType, inputPath, "-o", outputPath] =>
    let (code, output) ← runGenerate vectorType inputPath (some outputPath)
    IO.print output
    return code.toUInt32
  | _ =>
    IO.println "Usage: oracle generate <type> <input.json> [-o <output.json>]"
    IO.println ""
    IO.println "Types:"
    IO.println "  state_digest  Generate digest test vector from state input"
    IO.println "  chain         Generate chain verification test vector"
    IO.println ""
    IO.println "Examples:"
    IO.println "  oracle generate state_digest state.json"
    IO.println "  oracle generate state_digest state.json -o vector.json"
    return 4

end CLI.Commands
