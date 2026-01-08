import Jolt.Oracle
import CLI.Schema.StateInput
import CLI.Schema.ChainInput

/-!
# Test Vector Schema

JSON deserialization for conformance test vectors.

## Expected JSON Schema
```json
{
  "vectors": [
    {
      "name": "basic_state_digest",
      "type": "state_digest",
      "input": { "program_hash": "...", "state": {...} },
      "expected": "<decimal Fr>"
    },
    {
      "name": "chain_verification",
      "type": "chain",
      "input": { "program_hash": "...", "chunks": [...] },
      "expected": "VERIFIED"
    }
  ]
}
```

## Supported Vector Types
- `state_digest`: Compute StateDigestV1, compare Fr output
- `chain`: Verify continuation chain, compare status
-/

namespace CLI.Schema

open Jolt
open Jolt.JSON
open Jolt.State

/-- Type of test vector. -/
inductive VectorType
  | stateDigest  -- Compute state digest
  | chain        -- Verify chain
  deriving Repr, BEq

/-- Input for a test vector (variant based on type). -/
inductive VectorInput
  | digestInput (input : DigestInput)
  | chainInput (chain : Chain)
  deriving Repr

/-- Expected result for a test vector. -/
inductive VectorExpected
  | fr (value : Fr)           -- For digest tests
  | status (verified : Bool)  -- For chain tests (VERIFIED or MISMATCH)
  deriving Repr

/-- A single test vector. -/
structure TestVector where
  name : String
  vectorType : VectorType
  input : VectorInput
  expected : VectorExpected
  deriving Repr

/-- Result of running a single test vector. -/
structure VectorResult where
  name : String
  pass : Bool
  expected : Option String := none
  got : Option String := none
  deriving Repr

/-- Collection of test vectors. -/
structure TestVectorFile where
  vectors : Array TestVector
  deriving Repr

/-- Parse vector type from string. -/
def parseVectorType (s : String) : OracleResult VectorType := do
  match s with
  | "state_digest" => pure .stateDigest
  | "chain" => pure .chain
  | _ => throw (ErrorCode.E106_UnexpectedType s!"unknown vector type: {s}")

/-- Parse expected value based on vector type. -/
def parseExpected (v : JsonValue) (vtype : VectorType) : OracleResult VectorExpected := do
  match vtype with
  | .stateDigest =>
    match v.asStr? with
    | some s =>
      let fr ← parseFr s
      pure (.fr fr)
    | none => throw (ErrorCode.E106_UnexpectedType "string for expected Fr")
  | .chain =>
    match v.asStr? with
    | some s =>
      match s with
      | "VERIFIED" => pure (.status true)
      | "MISMATCH" => pure (.status false)
      | _ => throw (ErrorCode.E106_UnexpectedType s!"expected VERIFIED or MISMATCH, got {s}")
    | none => throw (ErrorCode.E106_UnexpectedType "string for expected status")

/-- Parse input based on vector type. -/
def parseVectorInput (v : JsonValue) (vtype : VectorType) : OracleResult VectorInput := do
  match vtype with
  | .stateDigest =>
    let input ← parseDigestInput v
    pure (.digestInput input)
  | .chain =>
    let chain ← parseChain v
    pure (.chainInput chain)

/-- Parse a single test vector. -/
def parseTestVector (v : JsonValue) : OracleResult TestVector := do
  let nameVal ← getRequiredField v "name"
  let typeVal ← getRequiredField v "type"
  let inputVal ← getRequiredField v "input"
  let expectedVal ← getRequiredField v "expected"

  let name ← match nameVal.asStr? with
    | some s => pure s
    | none => throw (ErrorCode.E106_UnexpectedType "string for name")

  let typeStr ← match typeVal.asStr? with
    | some s => pure s
    | none => throw (ErrorCode.E106_UnexpectedType "string for type")

  let vtype ← parseVectorType typeStr
  let input ← parseVectorInput inputVal vtype
  let expected ← parseExpected expectedVal vtype

  pure {
    name := name
    vectorType := vtype
    input := input
    expected := expected
  }

/-- Parse array of test vectors. -/
def parseTestVectors (v : JsonValue) : OracleResult (Array TestVector) := do
  match v.asArr? with
  | some arr =>
    let mut vectors : Array TestVector := #[]
    for item in arr do
      let vec ← parseTestVector item
      vectors := vectors.push vec
    pure vectors
  | none => throw (ErrorCode.E106_UnexpectedType "array for vectors")

/-- Parse test vector file from JSON. -/
def parseTestVectorFile (v : JsonValue) : OracleResult TestVectorFile := do
  let vectorsVal ← getRequiredField v "vectors"
  let vectors ← parseTestVectors vectorsVal
  pure { vectors := vectors }

/-- Parse test vector file from bytes. -/
def parseTestVectorBytes (bytes : ByteArray) : OracleResult TestVectorFile := do
  let json ← parseJSONBytes bytes
  parseTestVectorFile json

end CLI.Schema
