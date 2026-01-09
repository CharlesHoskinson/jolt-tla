import Jolt.Oracle
import CLI.Schema.StateInput

/-!
# Chain Input Schema

JSON deserialization for continuation chains.

## Expected JSON Schema
```json
{
  "program_hash": "0x<64 hex chars>",
  "chunks": [
    {
      "index": 0,
      "start_state": { ... VMStateV1 ... },
      "end_state": { ... VMStateV1 ... },
      "start_digest": "<decimal Fr string>",
      "end_digest": "<decimal Fr string>"
    }
  ]
}
```
-/

namespace CLI.Schema

open Jolt
open Jolt.JSON
open Jolt.State

/-- Parse Fr from JSON value (string containing decimal). -/
def parseFrField (v : JsonValue) (field : String) : OracleResult Fr := do
  match v.asStr? with
  | some s => parseFr s
  | none =>
    -- Also accept integer for small values
    match v.asInt? with
    | some i =>
      if i < 0 then throw (ErrorCode.E300_NonCanonicalFr (toString i))
      pure (Fr.ofNat i.toNat)
    | none => throw (ErrorCode.E106_UnexpectedType s!"string or integer for {field}")

/-- Parse a single chunk from JSON object.

Expected schema:
```json
{
  "index": 0,
  "start_state": { ... },
  "end_state": { ... },
  "start_digest": "<decimal>",
  "end_digest": "<decimal>"
}
```
-/
def parseChunk (v : JsonValue) : OracleResult Chunk := do
  let indexVal ← getRequiredField v "index"
  let startStateVal ← getRequiredField v "start_state"
  let endStateVal ← getRequiredField v "end_state"
  let startDigestVal ← getRequiredField v "start_digest"
  let endDigestVal ← getRequiredField v "end_digest"

  let index ← match indexVal.asInt? with
    | some i =>
      if i < 0 then throw (ErrorCode.E402_OutOfRange "index")
      pure i.toNat
    | none => throw (ErrorCode.E106_UnexpectedType "integer for index")

  let startState ← parseVMStateV1 startStateVal
  let endState ← parseVMStateV1 endStateVal
  let startDigest ← parseFrField startDigestVal "start_digest"
  let endDigest ← parseFrField endDigestVal "end_digest"

  pure {
    index := index
    startState := startState
    endState := endState
    startDigest := startDigest
    endDigest := endDigest
  }

/-- Parse chunks array. -/
def parseChunks (v : JsonValue) : OracleResult (Array Chunk) := do
  match v.asArr? with
  | some arr =>
    let mut chunks : Array Chunk := #[]
    for item in arr do
      let chunk ← parseChunk item
      chunks := chunks.push chunk
    pure chunks
  | none => throw (ErrorCode.E106_UnexpectedType "array for chunks")

/-- Parse chain input from JSON.

Expected schema:
```json
{
  "program_hash": "0x<64 hex>",
  "chunks": [ ... ]
}
```
-/
def parseChain (v : JsonValue) : OracleResult Chain := do
  let hashVal ← getRequiredField v "program_hash"
  let chunksVal ← getRequiredField v "chunks"

  let programHash ← parseBytes32Field hashVal "program_hash"
  let chunks ← parseChunks chunksVal

  pure {
    programHash := programHash
    chunks := chunks
  }

/-- Parse chain input from JSON bytes. -/
def parseChainBytes (bytes : ByteArray) : OracleResult Chain := do
  let json ← parseJSONBytes bytes
  parseChain json

end CLI.Schema
