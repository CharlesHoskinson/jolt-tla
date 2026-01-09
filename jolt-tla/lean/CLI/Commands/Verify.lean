import Jolt.Oracle
import CLI.Schema.ChainInput
import CLI.Report.Types
import CLI.Terminal.Doc
import CLI.Terminal.RenderPlain
import CLI.Format.Json

/-!
# Verify Command

Verify continuation chain integrity.

## Usage
```
oracle verify chain <chain.json>
```

## Input JSON Schema
```json
{
  "program_hash": "0x<64 hex>",
  "chunks": [
    {
      "index": 0,
      "start_state": { ... },
      "end_state": { ... },
      "start_digest": "<decimal>",
      "end_digest": "<decimal>"
    }
  ]
}
```

## Output (--format=json)
Success:
```json
{"status": "VERIFIED", "chunks_verified": 3}
```

Error:
```json
{"status": "MISMATCH", "error": "E501_DigestMismatch", "chunk_index": 1}
```
-/

namespace CLI.Commands

open Jolt
open CLI.Report
open CLI.Schema
open CLI.Terminal
open CLI.Format

/-- Convert Bytes32 to 0x-prefixed lowercase hex. -/
private def bytes32ToHexVerify (b : Bytes32) : String := Id.run do
  let mut hex := "0x"
  for i in [:32] do
    let byte := if i < b.data.size then b.data.data[i]!.toNat else 0
    let hi := if byte / 16 < 10 then Char.ofNat ('0'.toNat + byte / 16)
              else Char.ofNat ('a'.toNat + byte / 16 - 10)
    let lo := if byte % 16 < 10 then Char.ofNat ('0'.toNat + byte % 16)
              else Char.ofNat ('a'.toNat + byte % 16 - 10)
    hex := hex.push hi
    hex := hex.push lo
  hex

/-- Truncate hex for display. -/
private def truncateHexVerify (s : String) (maxLen : Nat := 20) : String :=
  if s.length <= maxLen then s
  else
    let prefixPart := s.take 12
    let suffixPart := s.drop (s.length - 4)
    prefixPart ++ "..." ++ suffixPart

/-- Run the verify chain command.

Returns (ExitCode, output string). -/
def runVerifyChain (filePath : String) (format : OutputFormat := .pretty)
    (caps : Caps := Caps.plain) : IO (ExitCode × String) := do
  -- Read input file
  let bytes ← try
    let content ← IO.FS.readBinFile filePath
    pure content
  catch _ =>
    return (.ioError, formatVerifyError format "E900_FileNotFound"
      s!"Cannot read file: {filePath}" none none)

  -- Parse JSON and extract chain
  let chain ← match parseChainBytes bytes with
    | .ok c => pure c
    | .error e =>
      let report := ErrorReport.fromCode e
      return (exitCodeForError e, formatVerifyError format report.codeString
        report.message none none)

  -- Verify chain
  let cfg := Oracle.init
  match Oracle.verifyChain cfg chain with
  | .ok () =>
    let output := formatVerifySuccess format chain.programHash chain.chunks.size caps
    return (.success, output)
  | .error e =>
    let report := ErrorReport.fromCode e
    let chunkIdx := extractChunkIndex e
    return (exitCodeForError e, formatVerifyError format report.codeString
      report.message chunkIdx (some chain.chunks.size))

where
  /-- Extract chunk index from error code if applicable. -/
  extractChunkIndex (e : ErrorCode) : Option Nat :=
    match e with
    | .E500_ChainBreak i => some i
    | .E501_DigestMismatch i => some i
    | _ => none

  /-- Format error output based on format. -/
  formatVerifyError (format : OutputFormat) (code : String) (message : String)
      (chunkIdx : Option Nat) (totalChunks : Option Nat) : String :=
    match format with
    | .json | .ndjson =>
      let basePairs := [
        ("status", jsonString "MISMATCH"),
        ("error", jsonString code),
        ("message", jsonString message)
      ]
      let idxPairs := match chunkIdx with
        | some i => [("chunk_index", jsonNat i)]
        | none => []
      let totalPairs := match totalChunks with
        | some n => [("total_chunks", jsonNat n)]
        | none => []
      jsonObject (basePairs ++ idxPairs ++ totalPairs) ++ "\n"
    | .pretty | .plain =>
      let idxLine := match chunkIdx with
        | some i => s!"\n  at chunk: {i}"
        | none => ""
      s!"Error: {code}\n  {message}{idxLine}\n"

  /-- Format success output based on format. -/
  formatVerifySuccess (format : OutputFormat) (programHash : Bytes32)
      (chunksVerified : Nat) (caps : Caps) : String :=
    match format with
    | .json | .ndjson =>
      jsonObject [
        ("status", jsonString "VERIFIED"),
        ("chunks_verified", jsonNat chunksVerified)
      ] ++ "\n"
    | .pretty | .plain =>
      let hashHex := bytes32ToHexVerify programHash
      let doc := buildVerifyDoc hashHex chunksVerified caps
      renderPlain doc

  /-- Build Doc for verify output. -/
  buildVerifyDoc (programHash : String) (chunksVerified : Nat) (caps : Caps) : Doc :=
    let icons := selectIcons caps
    Doc.vcat [
      Doc.headerBar "Jolt Oracle" (some "verify chain"),
      Doc.line,
      Doc.keyValue [
        Doc.kvStr "Program Hash" (truncateHexVerify programHash 40),
        Doc.kvStr "Chunks Verified" (toString chunksVerified),
        Doc.kv "Status" (Doc.healthy "VERIFIED")
      ],
      Doc.line,
      Doc.status icons true "Chain verification passed"
    ]

/-- Run verify chain from raw JSON content (for REPL variable support). -/
def runVerifyChainFromContent (content : String) (format : OutputFormat := .pretty)
    (caps : Caps := Caps.plain) : IO (ExitCode × String) := do
  let bytes := content.toUTF8

  -- Parse JSON and extract chain
  let chain ← match parseChainBytes bytes with
    | .ok c => pure c
    | .error e =>
      let report := ErrorReport.fromCode e
      return (exitCodeForError e, formatErrorContent format report.codeString report.message none none)

  -- Verify chain
  let cfg := Oracle.init
  match Oracle.verifyChain cfg chain with
  | .ok () =>
    let output := formatSuccessContent format chain.programHash chain.chunks.size caps
    return (.success, output)
  | .error e =>
    let report := ErrorReport.fromCode e
    let chunkIdx := extractChunkIdx e
    return (exitCodeForError e, formatErrorContent format report.codeString
      report.message chunkIdx (some chain.chunks.size))

where
  extractChunkIdx (e : ErrorCode) : Option Nat :=
    match e with
    | .E500_ChainBreak i => some i
    | .E501_DigestMismatch i => some i
    | _ => none

  formatErrorContent (format : OutputFormat) (code : String) (message : String)
      (chunkIdx : Option Nat) (totalChunks : Option Nat) : String :=
    match format with
    | .json | .ndjson =>
      let basePairs := [
        ("status", jsonString "MISMATCH"),
        ("error", jsonString code),
        ("message", jsonString message)
      ]
      let idxPairs := match chunkIdx with
        | some i => [("chunk_index", jsonNat i)]
        | none => []
      let totalPairs := match totalChunks with
        | some n => [("total_chunks", jsonNat n)]
        | none => []
      jsonObject (basePairs ++ idxPairs ++ totalPairs) ++ "\n"
    | .pretty | .plain =>
      let idxLine := match chunkIdx with
        | some i => s!"\n  at chunk: {i}"
        | none => ""
      s!"Error: {code}\n  {message}{idxLine}\n"

  formatSuccessContent (format : OutputFormat) (programHash : Bytes32)
      (chunksVerified : Nat) (caps : Caps) : String :=
    match format with
    | .json | .ndjson =>
      jsonObject [
        ("status", jsonString "VERIFIED"),
        ("chunks_verified", jsonNat chunksVerified)
      ] ++ "\n"
    | .pretty | .plain =>
      let hashHex := bytes32ToHexVerify programHash
      let icons := selectIcons caps
      let doc := Doc.vcat [
        Doc.headerBar "Jolt Oracle" (some "verify chain"),
        Doc.line,
        Doc.keyValue [
          Doc.kvStr "Program Hash" (truncateHexVerify hashHex 40),
          Doc.kvStr "Chunks Verified" (toString chunksVerified),
          Doc.kv "Status" (Doc.healthy "VERIFIED")
        ],
        Doc.line,
        Doc.status icons true "Chain verification passed"
      ]
      renderPlain doc

/-- Main entry point for verify chain command. -/
def verifyChainMain (args : List String) : IO UInt32 := do
  match args with
  | [filePath] =>
    let (code, output) ← runVerifyChain filePath .plain Caps.plain
    IO.print output
    return code.toUInt32
  | _ =>
    IO.println "Usage: oracle verify chain <chain.json>"
    return 4

end CLI.Commands
