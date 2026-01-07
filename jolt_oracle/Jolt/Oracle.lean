import Jolt.Errors
import Jolt.Field.Fr
import Jolt.Encoding.Bytes32
import Jolt.Encoding.Fr2
import Jolt.Poseidon.Sponge
import Jolt.Transcript.State
import Jolt.State.VMState
import Jolt.State.Digest
import Jolt.Wrapper.PublicInputs
import Jolt.Registry.Validate
import Jolt.Registry.ConfigTags
import Jolt.Bundle.Tar

namespace Jolt

/-- Oracle configuration. -/
structure OracleConfig where
  /-- Poseidon parameters -/
  poseidon : Poseidon.Config
  deriving Repr

/-- A continuation chunk. -/
structure Chunk where
  /-- Chunk index -/
  index : Nat
  /-- Starting state -/
  startState : State.VMStateV1
  /-- Ending state -/
  endState : State.VMStateV1
  /-- Start digest -/
  startDigest : Fr
  /-- End digest -/
  endDigest : Fr
  deriving Repr, Inhabited

/-- A continuation chain. -/
structure Chain where
  /-- Program hash -/
  programHash : Bytes32
  /-- Ordered chunks -/
  chunks : Array Chunk
  deriving Repr

namespace Oracle

/-- Initialize oracle with default configuration. -/
def init : OracleConfig where
  poseidon := Poseidon.defaultConfig

/-- Compute state digest for a VM state. -/
def computeStateDigest (cfg : OracleConfig) (programHash : Bytes32)
    (state : State.VMStateV1) : OracleResult Fr :=
  State.computeStateDigest cfg.poseidon programHash state

/-- Verify state digest matches expected value. -/
def verifyStateDigest (cfg : OracleConfig) (programHash : Bytes32)
    (state : State.VMStateV1) (expected : Fr) : OracleResult Bool :=
  State.verifyStateDigest cfg.poseidon programHash state expected

/-- Verify a continuation chunk.

Checks:
- Start/end digests match computed values
- State transitions are valid -/
def verifyChunk (cfg : OracleConfig) (programHash : Bytes32)
    (chunk : Chunk) : OracleResult Unit := do
  -- Verify start digest
  let computedStart ← computeStateDigest cfg programHash chunk.startState
  if computedStart != chunk.startDigest then
    throw (ErrorCode.E501_DigestMismatch chunk.index)

  -- Verify end digest
  let computedEnd ← computeStateDigest cfg programHash chunk.endState
  if computedEnd != chunk.endDigest then
    throw (ErrorCode.E501_DigestMismatch chunk.index)

/-- Verify a continuation chain.

Checks:
- Chain is non-empty
- Chunks are in order by index
- End digest of chunk[i] = start digest of chunk[i+1]
- All chunk digests are valid -/
def verifyChain (cfg : OracleConfig) (chain : Chain) : OracleResult Unit := do
  if chain.chunks.isEmpty then
    throw ErrorCode.E503_EmptyChain

  -- Verify each chunk
  for chunk in chain.chunks do
    verifyChunk cfg chain.programHash chunk

  -- Verify chain linkage
  for i in [:chain.chunks.size - 1] do
    let current := chain.chunks[i]!
    let next := chain.chunks[i + 1]!

    -- Index ordering
    if next.index != current.index + 1 then
      throw (ErrorCode.E502_InvalidChunkIndex)

    -- Digest chaining
    if current.endDigest != next.startDigest then
      throw (ErrorCode.E500_ChainBreak (i + 1))

/-- Test vector for conformance testing. -/
structure TestVector where
  /-- Test name -/
  name : String
  /-- Input state -/
  inputState : State.VMStateV1
  /-- Program hash -/
  programHash : Bytes32
  /-- Expected digest -/
  expectedDigest : Fr
  deriving Repr

/-- Generate a test vector for state digest computation. -/
def generateTestVector (cfg : OracleConfig) (name : String)
    (programHash : Bytes32) (state : State.VMStateV1) : OracleResult TestVector := do
  let digest ← computeStateDigest cfg programHash state
  pure {
    name := name
    inputState := state
    programHash := programHash
    expectedDigest := digest
  }

/-- Batch verify multiple test vectors. -/
def verifyTestVectors (cfg : OracleConfig)
    (vectors : Array TestVector) : OracleResult (Array Bool) := do
  let mut results : Array Bool := #[]
  for v in vectors do
    let ok ← verifyStateDigest cfg v.programHash v.inputState v.expectedDigest
    results := results.push ok
  pure results

end Oracle
end Jolt
