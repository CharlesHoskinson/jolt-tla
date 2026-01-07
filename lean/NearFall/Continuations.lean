import NearFall.TLATypes
import NearFall.VMState
import NearFall.Transcript

/-!
# Continuation Mechanics

Chunked execution and StateDigest chaining for continuations, matching jolt-tla.

## Main Definitions

* `StateDigest` - Single-field commitment to VM state
* `ChunkRecord` - Input/output state for a single chunk
* `ExecutionTrace` - Complete execution as sequence of chunks
* `ContinuationState` - Progression through chunks

## References

* jolt-tla/tla/Continuations.tla
* Jolt Spec §10 (Continuations, snapshots, StateDigest)
-/

namespace NearFall.Continuations

open TLATypes VMState Transcript

/-! ### Protocol Constants -/

/-- Maximum steps per chunk (from spec). -/
def CHUNK_MAX_STEPS : Nat := 1 <<< 20  -- 2^20 = 1,048,576

/-! ### StateDigest (J.10.10) -/

/-- StateDigest is a single Fr element.

This is the output of a 14-step Poseidon transcript computation over:
- program_hash
- pc, registers
- step_counter
- memory roots
- halted, exit_code
- config_tags

**TLA+ equivalent**: `StateDigest == Fr` -/
abbrev StateDigest := Fr

/-! ### StateDigest Computation -/

/-- Serialize VMState fields for hashing.

Per J.10.10, the serialization includes:
1. program_hash_bytes32
2. pc
3. registers[0..31]
4. step_counter
5. rw_mem_root_bytes32
6. io_root_bytes32
7. halted
8. exit_code
9. config_tags (with domain tag)

We model this abstractly; production uses Poseidon transcript. -/
structure StateDigestInput where
  /-- Program identity. -/
  programHash : Bytes32
  /-- VM state to digest. -/
  state : VMStateV1
  deriving DecidableEq

/-- Compute StateDigest from program hash and VMState.

This is an AXIOMATIZED function - in production, it's a 14-step
Poseidon transcript computation.

**TLA+ equivalent**: `ComputeStateDigest(program_hash_bytes32, state)` -/
opaque computeStateDigest (programHash : Bytes32) (state : VMStateV1) : StateDigest

/-- **AXIOM 6**: StateDigest is deterministic.

Same inputs always produce the same digest. -/
axiom state_digest_deterministic :
  ∀ (ph : Bytes32) (s : VMStateV1),
    computeStateDigest ph s = computeStateDigest ph s

/-- **AXIOM 7**: StateDigest is collision-resistant.

Different (programHash, state) pairs produce different digests.
This is the core security assumption for continuation chaining. -/
axiom state_digest_collision_resistant :
  ∀ (ph1 ph2 : Bytes32) (s1 s2 : VMStateV1),
    computeStateDigest ph1 s1 = computeStateDigest ph2 s2 →
    ph1 = ph2 ∧ s1 = s2

/-! ### ChunkRecord -/

/-- Chunk record capturing input/output state for a single chunk.

**TLA+ equivalent**: ChunkRecord with all 8 fields -/
structure ChunkRecord where
  /-- Program identity (binds chunk to program). -/
  programHashBytes32 : Bytes32
  /-- Chunk index (0-based). -/
  chunkIndex : ChunkIndex
  /-- Input state (at chunk start). -/
  stateIn : VMStateV1
  /-- Input state digest. -/
  digestIn : StateDigest
  /-- Output state (at chunk end). -/
  stateOut : VMStateV1
  /-- Output state digest. -/
  digestOut : StateDigest
  /-- Steps executed in this chunk. -/
  stepsExecuted : Nat
  /-- Is this the final chunk? -/
  isFinal : Bool
  deriving DecidableEq

namespace ChunkRecord

/-- Construct a chunk record from execution. -/
def make (programHash : Bytes32) (idx : ChunkIndex)
         (stateIn stateOut : VMStateV1) : ChunkRecord := {
  programHashBytes32 := programHash
  chunkIndex := idx
  stateIn := stateIn
  digestIn := computeStateDigest programHash stateIn
  stateOut := stateOut
  digestOut := computeStateDigest programHash stateOut
  stepsExecuted := stateOut.step_counter - stateIn.step_counter
  isFinal := stateOut.isHalted
}

/-! ### Chunk Execution Rules (J.10.6) -/

/-- Expected step counter at chunk start. -/
def expectedChunkStartStep (chunkIdx : ChunkIndex) : Nat :=
  chunkIdx * CHUNK_MAX_STEPS

/-- Check if chunk input state has correct step counter. -/
def inputStepValid (chunk : ChunkRecord) : Bool :=
  chunk.stateIn.step_counter == expectedChunkStartStep chunk.chunkIndex

/-- Check if non-final chunk executed correct number of steps. -/
def nonFinalStepsValid (chunk : ChunkRecord) : Bool :=
  chunk.isFinal || chunk.stepsExecuted == CHUNK_MAX_STEPS

/-- Check if non-final chunk has halted = 0. -/
def nonFinalNotHalted (chunk : ChunkRecord) : Bool :=
  chunk.isFinal || !chunk.stateOut.isHalted

/-- Check if final chunk has halted = 1. -/
def finalChunkHalted (chunk : ChunkRecord) : Bool :=
  !chunk.isFinal || chunk.stateOut.isHalted

/-- Check if final chunk has valid steps (1 to CHUNK_MAX_STEPS). -/
def finalStepsValid (chunk : ChunkRecord) : Bool :=
  !chunk.isFinal || (chunk.stepsExecuted ≥ 1 && chunk.stepsExecuted ≤ CHUNK_MAX_STEPS)

/-- Check if digest consistency holds. -/
def digestsConsistent (chunk : ChunkRecord) : Bool :=
  chunk.digestIn == computeStateDigest chunk.programHashBytes32 chunk.stateIn &&
  chunk.digestOut == computeStateDigest chunk.programHashBytes32 chunk.stateOut

/-- Security fix: check stepsExecuted matches step_counter delta.
Attack prevented: Forged stepsExecuted bypassing step count bounds checks. -/
def stepsExecutedConsistent (chunk : ChunkRecord) : Bool :=
  chunk.stepsExecuted == chunk.stateOut.step_counter - chunk.stateIn.step_counter

/-- A chunk is valid if it follows all execution rules.

Security fix: Added stepsExecutedConsistent check. -/
def isValid (chunk : ChunkRecord) : Bool :=
  chunk.inputStepValid &&
  chunk.nonFinalStepsValid &&
  chunk.nonFinalNotHalted &&
  chunk.finalChunkHalted &&
  chunk.finalStepsValid &&
  chunk.digestsConsistent &&
  chunk.stepsExecutedConsistent  -- Security fix: bind stepsExecuted to step_counter

end ChunkRecord

/-! ### Chunk Chaining (J.10.4) -/

/-- Two chunks are properly chained if output of first = input of second.

This is THE core invariant for continuation soundness. -/
def chunksChained (chunk1 chunk2 : ChunkRecord) : Bool :=
  chunk1.chunkIndex + 1 == chunk2.chunkIndex &&
  chunk1.digestOut == chunk2.digestIn

/-- Continuity invariant for a sequence of chunks.

J.10.4: "output digest of chunk i equals the input digest of chunk i+1" -/
def continuityInvariant (chunks : List ChunkRecord) : Bool :=
  match chunks with
  | [] => true
  | [_] => true
  | c1 :: c2 :: rest => chunksChained c1 c2 && continuityInvariant (c2 :: rest)

/-! ### Execution Trace -/

/-- Execution trace as sequence of chunks.

**TLA+ equivalent**: `ExecutionTrace == Seq(ChunkRecord)` -/
abbrev ExecutionTrace := List ChunkRecord

namespace ExecutionTrace

/-- A valid execution trace satisfies all chunk and chaining rules.

Security fix: was checking rest.dropLast, now trace.dropLast.
Attack prevented: Post-halt chunk execution (chunks after halted chunk accepted). -/
def isValid (trace : ExecutionTrace) : Bool :=
  match trace with
  | [] => false  -- Must have at least one chunk
  | first :: _ =>
    -- First chunk starts at index 0
    first.chunkIndex == 0 &&
    -- All chunks are individually valid
    trace.all ChunkRecord.isValid &&
    -- Chunks are properly chained
    continuityInvariant trace &&
    -- Last chunk is final
    trace.getLast?.map (·.isFinal) == some true &&
    -- Security fix: Check ALL chunks except last are non-final (was rest.dropLast)
    trace.dropLast.all (!·.isFinal)

/-- Get the initial state of an execution trace. -/
def initialState (trace : ExecutionTrace) : Option VMStateV1 :=
  trace.head?.map (·.stateIn)

/-- Get the final state of an execution trace. -/
def finalState (trace : ExecutionTrace) : Option VMStateV1 :=
  trace.getLast?.map (·.stateOut)

/-- Get the initial digest of an execution trace. -/
def initialDigest (trace : ExecutionTrace) : Option StateDigest :=
  trace.head?.map (·.digestIn)

/-- Get the final digest of an execution trace. -/
def finalDigest (trace : ExecutionTrace) : Option StateDigest :=
  trace.getLast?.map (·.digestOut)

/-- Get the program hash (should be same for all chunks). -/
def programHash (trace : ExecutionTrace) : Option Bytes32 :=
  trace.head?.map (·.programHashBytes32)

end ExecutionTrace

/-! ### Config Consistency -/

/-- All chunks in a trace must have the same config_tags. -/
def configConsistentAcrossChunks (trace : ExecutionTrace) : Bool :=
  match trace.head? with
  | none => true
  | some first =>
    trace.all (fun c => c.stateIn.config_tags == first.stateIn.config_tags)

/-- Config tags are preserved through execution within a chunk. -/
def configPreservedInChunk (chunk : ChunkRecord) : Bool :=
  chunk.stateIn.config_tags == chunk.stateOut.config_tags

/-! ### ContinuationState -/

/-- Continuation state record modeling progression through chunks.

**TLA+ equivalent**: ContinuationState with 6 fields -/
structure ContinuationState where
  /-- Program identity. -/
  programHashBytes32 : Bytes32
  /-- Current chunk index. -/
  currentChunk : ChunkIndex
  /-- Accumulated chunks. -/
  chunks : ExecutionTrace
  /-- Is execution complete? -/
  complete : Bool
  /-- Initial state digest. -/
  initialDigest : StateDigest
  /-- Final state digest (valid when complete). -/
  finalDigest : StateDigest
  deriving DecidableEq

namespace ContinuationState

/-- Initial continuation state (before any chunks executed). -/
def init (programHash : Bytes32) (initialState : VMStateV1) : ContinuationState := {
  programHashBytes32 := programHash
  currentChunk := 0
  chunks := []
  complete := false
  initialDigest := computeStateDigest programHash initialState
  finalDigest := Fr.zero  -- Not yet known
}

/-- Execute a chunk and record it. -/
def executeChunk (cont : ContinuationState) (stateIn stateOut : VMStateV1) : ContinuationState :=
  let chunk := ChunkRecord.make cont.programHashBytes32 cont.currentChunk stateIn stateOut
  let isComplete := chunk.isFinal
  { cont with
    currentChunk := cont.currentChunk + 1
    chunks := cont.chunks ++ [chunk]
    complete := isComplete
    finalDigest := if isComplete then chunk.digestOut else cont.finalDigest
  }

/-- Is continuation complete? -/
def isComplete (cont : ContinuationState) : Bool := cont.complete

/-- Is ready for next chunk? -/
def readyForNextChunk (cont : ContinuationState) : Bool := !cont.complete

end ContinuationState

instance : Inhabited ContinuationState where
  default := {
    programHashBytes32 := Bytes32.zero
    currentChunk := 0
    chunks := []
    complete := false
    initialDigest := Fr.zero
    finalDigest := Fr.zero
  }

/-! ### Attack Prevention Properties (J.10.3) -/

/-- Attack 1 Prevention: Cannot skip chunks.

Chunks must be consecutive starting at index 0. -/
def noSkippedChunks (trace : ExecutionTrace) : Bool :=
  (trace.zip (List.range trace.length)).all (fun (c, i) => c.chunkIndex == i)

/-- Attack 2 Prevention: Same initial digest + same config → same final digest.

This follows from determinism and StateDigest collision resistance. -/
def noSplicedExecutionsProperty (t1 t2 : ExecutionTrace) : Prop :=
  t1.isValid = true ∧ t2.isValid = true ∧
  t1.initialDigest = t2.initialDigest ∧
  configConsistentAcrossChunks t1 = true ∧ configConsistentAcrossChunks t2 = true →
  t1.finalDigest = t2.finalDigest

/-- Attack 3 Prevention: Different config_tags → different StateDigest.

Config is included in the digest computation. -/
def noCrossConfigSplice (chunk1 chunk2 : ChunkRecord) : Prop :=
  chunk1.stateOut.config_tags ≠ chunk2.stateIn.config_tags →
  chunk1.digestOut ≠ chunk2.digestIn

/-! ### Wrapper Integration Helpers -/

/-- Extract old state root from initial state. -/
def oldStateRoot (trace : ExecutionTrace) : Option Bytes32 :=
  trace.initialState.map (·.rw_mem_root_bytes32)

/-- Extract new state root from final state. -/
def newStateRoot (trace : ExecutionTrace) : Option Bytes32 :=
  trace.finalState.map (·.rw_mem_root_bytes32)

/-- Extract exit status from final state. -/
def finalExitStatus (trace : ExecutionTrace) : Option StatusCode :=
  trace.finalState.map (·.exit_code)

/-! ### Type Invariants -/

/-- ChunkRecord type invariant. -/
def chunkRecordTypeOK (chunk : ChunkRecord) : Prop :=
  bytes32_well_formed chunk.programHashBytes32 ∧
  vmStateTypeOK chunk.stateIn ∧
  vmStateTypeOK chunk.stateOut

/-- ContinuationState type invariant. -/
def continuationStateTypeOK (cont : ContinuationState) : Prop :=
  bytes32_well_formed cont.programHashBytes32 ∧
  cont.currentChunk ≤ cont.chunks.length + 1 ∧
  ∀ c ∈ cont.chunks, chunkRecordTypeOK c

/-! ### Theorems -/

/-- Continuity of single chunk is trivially true. -/
theorem single_chunk_continuity (c : ChunkRecord) :
    continuityInvariant [c] = true := by
  simp [continuityInvariant]

/-- Empty trace has no skipped chunks. -/
theorem empty_trace_no_skips : noSkippedChunks [] = true := by
  rfl

/-- Initial continuation is not complete. -/
theorem init_not_complete (ph : Bytes32) (s : VMStateV1) :
    (ContinuationState.init ph s).isComplete = false := by
  simp [ContinuationState.init, ContinuationState.isComplete]

/-- Chunk made from halted state is final. -/
theorem halted_chunk_is_final (ph : Bytes32) (idx : ChunkIndex)
    (sIn sOut : VMStateV1) (h : sOut.isHalted = true) :
    (ChunkRecord.make ph idx sIn sOut).isFinal = true := by
  simp [ChunkRecord.make, h]

end NearFall.Continuations
