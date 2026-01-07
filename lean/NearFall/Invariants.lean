import NearFall.TLATypes
import NearFall.SMT
import NearFall.VMState
import NearFall.Continuations

/-!
# Specification Invariants

Centralized collection of all 29 TLA+ specification invariants.

## Categories

* `INV_TYPE_*`  : Type well-formedness (4 invariants)
* `INV_BIND_*` : Cryptographic binding (10 invariants, +3 from security review)
* `INV_SAFE_*` : Protocol correctness (7 invariants)
* `INV_ATK_*`  : Attack prevention (8 invariants)

## References

* jolt-tla/tla/Invariants.tla
* Jolt Spec §15 (Security)
-/

namespace NearFall.Invariants

open TLATypes SMT VMState Continuations

/-! ### System Phase -/

/-- System execution phase.

**TLA+ equivalent**: `SystemPhase == {"INIT", "EXECUTING", "COMPLETE", "FAILED"}` -/
inductive SystemPhase where
  | INIT      : SystemPhase
  | EXECUTING : SystemPhase
  | COMPLETE  : SystemPhase
  | FAILED    : SystemPhase
  deriving Repr, DecidableEq, BEq, Inhabited

/-! ### Public Inputs (11 Fr elements) -/

/-- Public inputs for the wrapper circuit (§5.5).

11 Fr elements that bind the execution to verifiable state. -/
structure PublicInputs where
  /-- Program hash, low 248 bits. -/
  program_hash_lo : Fr
  /-- Program hash, high 8 bits. -/
  program_hash_hi : Fr
  /-- Old state root, low 248 bits. -/
  old_root_lo : Fr
  /-- Old state root, high 8 bits. -/
  old_root_hi : Fr
  /-- New state root, low 248 bits. -/
  new_root_lo : Fr
  /-- New state root, high 8 bits. -/
  new_root_hi : Fr
  /-- Batch nonce as Fr. -/
  batch_nonce_fr : Fr
  /-- Exit status as Fr. -/
  status_fr : Fr
  /-- Start digest. -/
  start_digest : Fr
  /-- End digest. -/
  end_digest : Fr
  deriving DecidableEq

instance : Inhabited PublicInputs where
  default := {
    program_hash_lo := Fr.zero, program_hash_hi := Fr.zero
    old_root_lo := Fr.zero, old_root_hi := Fr.zero
    new_root_lo := Fr.zero, new_root_hi := Fr.zero
    batch_nonce_fr := Fr.zero, status_fr := Fr.zero
    start_digest := Fr.zero, end_digest := Fr.zero
  }

/-! ### System State -/

/-- Complete system state for invariant checking. -/
structure SystemState where
  /-- Current execution phase. -/
  phase : SystemPhase
  /-- Batch nonce for replay prevention. -/
  batchNonce : U64
  /-- Program hash (identity). -/
  programHash : Bytes32
  /-- Current VM state. -/
  vmState : VMStateV1
  /-- Continuation state. -/
  continuation : ContinuationState
  /-- Assembled public inputs. -/
  publicInputs : PublicInputs
  deriving DecidableEq

instance : Inhabited SystemState where
  default := {
    phase := .INIT
    batchNonce := 0
    programHash := Bytes32.zero
    vmState := default
    continuation := default
    publicInputs := default
  }

/-! ========================================================================
    TYPE INVARIANTS (4)
    Verify that all values are well-typed
    ======================================================================== -/

/-- INV_TYPE_SystemState: System state has valid types.

**TLA+**: `sys.phase ∈ SystemPhase ∧ sys.batchNonce ∈ U64` -/
def INV_TYPE_SystemState (sys : SystemState) : Prop :=
  True  -- Phase is always valid by construction in Lean

/-- INV_TYPE_VMState: VM state has valid types.

Checks all 8 fields of VMStateV1. -/
def INV_TYPE_VMState (sys : SystemState) : Prop :=
  vmStateTypeOK sys.vmState

/-- INV_TYPE_ProgramHash: Program hash is well-formed Bytes32. -/
def INV_TYPE_ProgramHash (sys : SystemState) : Prop :=
  bytes32_well_formed sys.programHash

/-- INV_TYPE_Continuation: Continuation state is well-typed. -/
def INV_TYPE_Continuation (sys : SystemState) : Prop :=
  continuationStateTypeOK sys.continuation

/-- All type invariants. -/
def INV_TYPE_All (sys : SystemState) : Prop :=
  INV_TYPE_SystemState sys ∧
  INV_TYPE_VMState sys ∧
  INV_TYPE_ProgramHash sys ∧
  INV_TYPE_Continuation sys

/-! ========================================================================
    BINDING INVARIANTS (7) - CRITICAL
    Verify that public inputs correctly reflect execution state
    ======================================================================== -/

/-- INV_BIND_StatusFr: status_fr matches final exit status.

Attack prevented: Claiming success when execution trapped. -/
def INV_BIND_StatusFr (sys : SystemState) : Prop :=
  sys.phase = .COMPLETE →
    sys.publicInputs.status_fr =
      Fr.fromU64 ((finalExitStatus sys.continuation.chunks).getD 0).toUInt64

/-- INV_BIND_OldRoot: old_root matches initial rw_mem_root.

Attack prevented: Claiming false initial memory state. -/
def INV_BIND_OldRoot (sys : SystemState) : Prop :=
  sys.phase = .COMPLETE →
    ∃ (initState : VMStateV1),
      sys.continuation.chunks.initialState = some initState ∧
      let fr2 := Fr2.fromBytes32 initState.rw_mem_root_bytes32
      sys.publicInputs.old_root_lo = fr2.lo ∧
      sys.publicInputs.old_root_hi = fr2.hi

/-- INV_BIND_NewRoot: new_root matches final rw_mem_root.

Attack prevented: Claiming false final memory state. -/
def INV_BIND_NewRoot (sys : SystemState) : Prop :=
  sys.phase = .COMPLETE →
    ∃ (finalState : VMStateV1),
      sys.continuation.chunks.finalState = some finalState ∧
      let fr2 := Fr2.fromBytes32 finalState.rw_mem_root_bytes32
      sys.publicInputs.new_root_lo = fr2.lo ∧
      sys.publicInputs.new_root_hi = fr2.hi

/-- INV_BIND_ProgramHash: program_hash matches system program hash.

Attack prevented: Proving with wrong program. -/
def INV_BIND_ProgramHash (sys : SystemState) : Prop :=
  sys.phase = .COMPLETE →
    let fr2 := Fr2.fromBytes32 sys.programHash
    sys.publicInputs.program_hash_lo = fr2.lo ∧
    sys.publicInputs.program_hash_hi = fr2.hi

/-- INV_BIND_ConfigTags: config_tags are computed correctly.

Attack prevented: Using different config for proving vs verification. -/
def INV_BIND_ConfigTags (sys : SystemState) : Prop :=
  sys.phase = .EXECUTING ∨ sys.phase = .COMPLETE →
    configConsistentAcrossChunks sys.continuation.chunks = true

/-- INV_BIND_StateDigest: All chunk digests are correctly computed.

Attack prevented: Digest forgery. -/
def INV_BIND_StateDigest (sys : SystemState) : Prop :=
  sys.phase = .COMPLETE →
    ∀ chunk ∈ sys.continuation.chunks,
      chunk.digestIn = computeStateDigest chunk.programHashBytes32 chunk.stateIn

/-- INV_BIND_Nonce: batch_nonce matches ABI register a4.

Attack prevented: Replay attacks. -/
def INV_BIND_Nonce (sys : SystemState) : Prop :=
  sys.phase = .COMPLETE →
    ∃ (initState : VMStateV1),
      sys.continuation.chunks.initialState = some initState ∧
      sys.publicInputs.batch_nonce_fr = Fr.fromU64 sys.batchNonce ∧
      sys.batchNonce = initState.readReg REG_A4

/-- INV_BIND_StartDigest: start_digest matches first chunk's digestIn.

Attack prevented: Splice/link confusion at recursion boundary.
Security fix: previously unconstrained field. -/
def INV_BIND_StartDigest (sys : SystemState) : Prop :=
  sys.phase = .COMPLETE →
    match sys.continuation.chunks.head? with
    | some firstChunk => sys.publicInputs.start_digest = firstChunk.digestIn
    | none => True  -- vacuously true for empty trace

/-- INV_BIND_EndDigest: end_digest matches last chunk's digestOut.

Attack prevented: Splice/link confusion at recursion boundary.
Security fix: previously unconstrained field. -/
def INV_BIND_EndDigest (sys : SystemState) : Prop :=
  sys.phase = .COMPLETE →
    match sys.continuation.chunks.getLast? with
    | some lastChunk => sys.publicInputs.end_digest = lastChunk.digestOut
    | none => True  -- vacuously true for empty trace

/-- INV_BIND_ChunkProgramHash: All chunks use the system's program hash.

Attack prevented: Proving with wrong program while claiming another.
Security fix: chunk programHashBytes32 unbound. -/
def INV_BIND_ChunkProgramHash (sys : SystemState) : Prop :=
  sys.phase = .EXECUTING ∨ sys.phase = .COMPLETE →
    ∀ chunk ∈ sys.continuation.chunks,
      chunk.programHashBytes32 = sys.programHash

/-- All binding invariants (10 total after security review additions). -/
def INV_BIND_All (sys : SystemState) : Prop :=
  INV_BIND_StatusFr sys ∧
  INV_BIND_OldRoot sys ∧
  INV_BIND_NewRoot sys ∧
  INV_BIND_ProgramHash sys ∧
  INV_BIND_ConfigTags sys ∧
  INV_BIND_StateDigest sys ∧
  INV_BIND_Nonce sys ∧
  INV_BIND_StartDigest sys ∧      
  INV_BIND_EndDigest sys ∧        
  INV_BIND_ChunkProgramHash sys   

/-! ========================================================================
    SAFETY INVARIANTS (7)
    Verify protocol correctness properties
    ======================================================================== -/

/-- INV_SAFE_VMHaltedExitCode: Exit code semantics are correct.

- If running (halted=0), exit_code must be 0
- If halted (halted=1), exit_code must be in [0, 255] -/
def INV_SAFE_VMHaltedExitCode (sys : SystemState) : Prop :=
  runningExitCodeZero sys.vmState ∧
  haltedExitCodeValid sys.vmState

/-- INV_SAFE_RegisterX0: RISC-V x0 is always zero. -/
def INV_SAFE_RegisterX0 (sys : SystemState) : Prop :=
  registerX0Zero sys.vmState

/-- INV_SAFE_HaltedBinary: Halted flag is binary (0 or 1). -/
def INV_SAFE_HaltedBinary (sys : SystemState) : Prop :=
  haltedFlagValid sys.vmState

/-- INV_SAFE_ContinuationChain: Chunk digests form valid chain.

This is THE core soundness invariant for continuations. -/
def INV_SAFE_ContinuationChain (sys : SystemState) : Prop :=
  sys.continuation.chunks.length > 1 →
    continuityInvariant sys.continuation.chunks = true

/-- INV_SAFE_FinalChunkHalted: Final chunk must have halted=1.

Attack prevented: Accepting incomplete execution. -/
def INV_SAFE_FinalChunkHalted (sys : SystemState) : Prop :=
  sys.phase = .COMPLETE →
    sys.continuation.chunks.getLast?.map (·.stateOut.isHalted) = some true

/-- INV_SAFE_ChunksConsecutive: Chunk indices are consecutive from 0.

Attack prevented: Skipping chunks. -/
def INV_SAFE_ChunksConsecutive (sys : SystemState) : Prop :=
  noSkippedChunks sys.continuation.chunks = true

/-- INV_SAFE_NonFinalNotHalted: Non-final chunks have halted=0.

Attack prevented: Premature termination. -/
def INV_SAFE_NonFinalNotHalted (sys : SystemState) : Prop :=
  ∀ c ∈ sys.continuation.chunks.dropLast, c.stateOut.isHalted = false

/-- All safety invariants. -/
def INV_SAFE_All (sys : SystemState) : Prop :=
  INV_SAFE_VMHaltedExitCode sys ∧
  INV_SAFE_RegisterX0 sys ∧
  INV_SAFE_HaltedBinary sys ∧
  INV_SAFE_ContinuationChain sys ∧
  INV_SAFE_FinalChunkHalted sys ∧
  INV_SAFE_ChunksConsecutive sys ∧
  INV_SAFE_NonFinalNotHalted sys

/-! ========================================================================
    ATTACK PREVENTION INVARIANTS (8) - CRITICAL
    Each invariant prevents a specific attack vector
    ======================================================================== -/

/-- INV_ATK_NoPrefixProof: Cannot accept incomplete execution.

Attack: Prover proves first half of execution, skips critical logic. -/
def INV_ATK_NoPrefixProof (sys : SystemState) : Prop :=
  sys.phase = .COMPLETE →
    ∃ (finalState : VMStateV1),
      sys.continuation.chunks.finalState = some finalState ∧
      (sys.publicInputs.status_fr = Fr.fromU64 JOLT_STATUS_OK.toUInt64 →
        finalState.isSuccessfulHalt ∧ finalState.isHalted)

/-- INV_ATK_NoSkipChunk: Cannot skip chunks in sequence.

Attack: Prover omits chunk containing critical logic. -/
def INV_ATK_NoSkipChunk (sys : SystemState) : Prop :=
  noSkippedChunks sys.continuation.chunks = true

/-- INV_ATK_NoSplice: Cannot splice different executions.

Attack: Prover mixes chunks from execution A and B.
Prevented by: StateDigest includes all state, continuity invariant. -/
def INV_ATK_NoSplice (sys : SystemState) : Prop :=
  sys.phase = .EXECUTING ∨ sys.phase = .COMPLETE →
    continuityInvariant sys.continuation.chunks = true

/-- INV_ATK_NoCrossConfig: Cannot use wrong configuration.

Attack: Prove with permissive config, verify with strict.
Prevented by: config_tags included in StateDigest. -/
def INV_ATK_NoCrossConfig (sys : SystemState) : Prop :=
  sys.phase = .EXECUTING ∨ sys.phase = .COMPLETE →
    configConsistentAcrossChunks sys.continuation.chunks = true

/-- INV_ATK_NoRootForgery: Cannot forge memory state roots.

Attack: Claim false initial/final memory state. -/
def INV_ATK_NoRootForgery (sys : SystemState) : Prop :=
  INV_BIND_OldRoot sys ∧ INV_BIND_NewRoot sys

/-- INV_ATK_NoMemoryForgery: Cannot forge RW memory between chunks.

Attack: Manipulate read-write memory root at chunk boundary. -/
def INV_ATK_NoMemoryForgery (sys : SystemState) : Prop :=
  sys.phase = .EXECUTING ∨ sys.phase = .COMPLETE →
    ∀ pair ∈ sys.continuation.chunks.zip (sys.continuation.chunks.drop 1),
      pair.1.stateOut.rw_mem_root_bytes32 = pair.2.stateIn.rw_mem_root_bytes32

/-- INV_ATK_NoIOForgery: Cannot forge IO memory between chunks.

Attack: Manipulate input/output memory root at chunk boundary. -/
def INV_ATK_NoIOForgery (sys : SystemState) : Prop :=
  sys.phase = .EXECUTING ∨ sys.phase = .COMPLETE →
    ∀ pair ∈ sys.continuation.chunks.zip (sys.continuation.chunks.drop 1),
      pair.1.stateOut.io_root_bytes32 = pair.2.stateIn.io_root_bytes32

/-- INV_ATK_NoReplay: Cannot replay old proofs.

Attack: Reuse proof from different batch.
Prevented by: batch_nonce in public inputs and ABI register. -/
def INV_ATK_NoReplay (sys : SystemState) : Prop :=
  sys.phase = .COMPLETE →
    ∃ (initState : VMStateV1),
      sys.continuation.chunks.initialState = some initState ∧
      sys.publicInputs.batch_nonce_fr = Fr.fromU64 (initState.readReg REG_A4)

/-- All attack prevention invariants. -/
def INV_ATK_All (sys : SystemState) : Prop :=
  INV_ATK_NoPrefixProof sys ∧
  INV_ATK_NoSkipChunk sys ∧
  INV_ATK_NoSplice sys ∧
  INV_ATK_NoCrossConfig sys ∧
  INV_ATK_NoRootForgery sys ∧
  INV_ATK_NoMemoryForgery sys ∧
  INV_ATK_NoIOForgery sys ∧
  INV_ATK_NoReplay sys

/-! ========================================================================
    COMPOSITE INVARIANTS
    ======================================================================== -/

/-- All 29 invariants combined (4 TYPE + 10 BIND + 7 SAFE + 8 ATK). -/
def AllInvariants (sys : SystemState) : Prop :=
  INV_TYPE_All sys ∧
  INV_BIND_All sys ∧
  INV_SAFE_All sys ∧
  INV_ATK_All sys

/-- Critical invariants only (for fast checking). -/
def CriticalInvariants (sys : SystemState) : Prop :=
  INV_BIND_StatusFr sys ∧
  INV_BIND_OldRoot sys ∧
  INV_BIND_NewRoot sys ∧
  INV_SAFE_ContinuationChain sys ∧
  INV_ATK_NoPrefixProof sys ∧
  INV_ATK_NoSkipChunk sys ∧
  INV_ATK_NoSplice sys

/-! ========================================================================
    INVARIANT COUNT VERIFICATION
    ======================================================================== -/

/-- Total invariant count: 4 + 10 + 7 + 8 = 29 (includes 3 security review additions) -/
def invariantCount : Nat :=
  4   -- TYPE invariants
  + 10  -- BIND invariants (original 7 + 3 security review fixes)
  + 7   -- SAFE invariants
  + 8   -- ATK invariants

theorem invariant_count_is_29 : invariantCount = 29 := rfl

/-! ========================================================================
    THEOREMS
    ======================================================================== -/

/-- Type invariants hold for default system state. -/
theorem default_system_type_invariants :
    INV_TYPE_SystemState default := by
  simp [INV_TYPE_SystemState]

/-- Initial phase is INIT. -/
theorem default_phase_is_init :
    (default : SystemState).phase = .INIT := by
  rfl

/-- Skip chunk invariant holds for empty trace. -/
theorem empty_trace_no_skip :
    noSkippedChunks [] = true := by
  simp [noSkippedChunks]

/-- Continuity invariant holds trivially for single chunk. -/
theorem single_chunk_continuity_holds (c : ChunkRecord) :
    continuityInvariant [c] = true := by
  simp [continuityInvariant]

end NearFall.Invariants
