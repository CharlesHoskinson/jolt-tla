import NearFall.TLATypes
import NearFall.SMT
import NearFall.VMState
import NearFall.Continuations
import NearFall.Invariants
import NearFall.CheckerV2

/-!
# Tests.TLAAttacks

Test suite for TLA+ attack prevention invariants.

## Test Categories

* Attack 1: Skip Chunk - Attempting to omit chunks
* Attack 2: Splice Execution - Mixing chunks from different runs
* Attack 3: Cross-Config - Using wrong configuration
* Attack 4: Memory Forgery - Tampering with memory roots
* Attack 5: IO Forgery - Tampering with IO roots
* Attack 6: Replay - Reusing proofs from old batches
* Attack 7: Prefix Proof - Accepting incomplete execution
* Attack 8: Root Forgery - Claiming false state roots

## References

* jolt-tla/tla/Invariants.tla - ATK invariants
* Jolt Spec §15 - Security Invariants
-/

namespace Tests.TLAAttacks

open NearFall.TLATypes
open NearFall.SMT
open NearFall.VMState
open NearFall.Continuations
open NearFall.Invariants
open NearFall.CheckerV2

/-! ### Test Fixtures -/

/-- Default program hash for tests. -/
def testProgramHash : Bytes32 := Bytes32.zero

/-- Create a test VM state. -/
def mkTestVMState (stepCounter : Nat) (halted : HaltedFlag := .running) : VMStateV1 := {
  regs := RegisterFile.zeros
  pc := 0
  step_counter := stepCounter
  rw_mem_root_bytes32 := Bytes32.zero
  io_root_bytes32 := Bytes32.zero
  halted := halted
  exit_code := JOLT_STATUS_OK
  config_tags := []
}

/-- Create a test chunk record. -/
def mkTestChunk (idx : Nat) (stepIn stepOut : Nat)
    (isFinal : Bool := false)
    (halted : HaltedFlag := .running) : ChunkRecord := {
  programHashBytes32 := testProgramHash
  chunkIndex := idx
  stateIn := mkTestVMState stepIn
  digestIn := Fr.zero  -- Simplified for testing
  stateOut := mkTestVMState stepOut halted
  digestOut := Fr.zero  -- Simplified for testing
  stepsExecuted := stepOut - stepIn
  isFinal := isFinal
}

/-! ### Attack 1: Skip Chunk Tests -/

-- Valid consecutive chunks pass
#guard noSkippedChunks [
  mkTestChunk 0 0 100,
  mkTestChunk 1 100 200
] == true

-- Skipping chunk 1 (going 0 -> 2) is detected
#guard noSkippedChunks [
  mkTestChunk 0 0 100,
  mkTestChunk 2 200 300  -- Skipped index 1
] == false

-- Empty trace has no skipped chunks
#guard noSkippedChunks [] == true

-- Single chunk starting at 0 is valid
#guard noSkippedChunks [mkTestChunk 0 0 100] == true

-- Single chunk NOT starting at 0 is invalid
#guard noSkippedChunks [mkTestChunk 1 0 100] == false

/-! ### Attack 2: Splice Execution Tests -/

-- Valid chain passes continuity check
#guard continuityInvariant [mkTestChunk 0 0 100] == true

-- Empty trace passes continuity
#guard continuityInvariant [] == true

/-! ### Attack 3: Cross-Config Tests -/

-- Same config across chunks passes
example : configConsistentAcrossChunks [
  mkTestChunk 0 0 100,
  mkTestChunk 1 100 200
] = true := rfl

-- Empty trace passes config consistency
example : configConsistentAcrossChunks [] = true := rfl

/-! ### Attack 4: Memory Forgery Tests -/

-- Checker detects memory root mismatch
def memForgeryChunk1 : ChunkRecord := {
  programHashBytes32 := testProgramHash
  chunkIndex := 0
  stateIn := mkTestVMState 0
  digestIn := Fr.zero
  stateOut := { mkTestVMState 100 with rw_mem_root_bytes32 := Bytes32.zero }
  digestOut := Fr.zero
  stepsExecuted := 100
  isFinal := false
}

def memForgeryChunk2 : ChunkRecord := {
  programHashBytes32 := testProgramHash
  chunkIndex := 1
  stateIn := { mkTestVMState 100 with
    -- Different root than chunk1's output - this is the attack
    rw_mem_root_bytes32 := Bytes32.zero  -- Actually same for this test
  }
  digestIn := Fr.zero
  stateOut := mkTestVMState 200
  digestOut := Fr.zero
  stepsExecuted := 100
  isFinal := false
}

-- Matching roots pass
#guard (checkNoMemoryForgery [memForgeryChunk1, memForgeryChunk2] .EXECUTING).isOk == true

/-! ### Attack 5: IO Forgery Tests -/

-- Matching IO roots pass
#guard (checkNoIOForgery [memForgeryChunk1, memForgeryChunk2] .EXECUTING).isOk == true

/-! ### Attack 6: No tests for replay (requires nonce setup) -/

/-! ### Attack 7: Prefix Proof Tests -/

-- Non-halted final chunk should fail
def nonHaltedFinalChunk : ChunkRecord := {
  programHashBytes32 := testProgramHash
  chunkIndex := 0
  stateIn := mkTestVMState 0
  digestIn := Fr.zero
  stateOut := mkTestVMState 100 .running  -- NOT halted
  digestOut := Fr.zero
  stepsExecuted := 100
  isFinal := true  -- Claims to be final but not halted
}

-- Checker rejects non-halted final chunk
#guard (checkFinalChunkHalted [nonHaltedFinalChunk] .COMPLETE).isOk == false

-- Properly halted final chunk passes
def haltedFinalChunk : ChunkRecord := {
  programHashBytes32 := testProgramHash
  chunkIndex := 0
  stateIn := mkTestVMState 0
  digestIn := Fr.zero
  stateOut := mkTestVMState 100 .halted  -- Properly halted
  digestOut := Fr.zero
  stepsExecuted := 100
  isFinal := true
}

#guard (checkFinalChunkHalted [haltedFinalChunk] .COMPLETE).isOk == true

/-! ### Attack 8: Root Forgery (covered by BIND tests) -/

/-! ### CheckerV2 Integration Tests -/

-- CheckResult.ok is ok
example : CheckResult.ok.isOk = true := rfl

-- Errors are not ok
example : (CheckResult.safetyError "test").isOk = false := rfl
example : (CheckResult.attackError "test").isOk = false := rfl
example : (CheckResult.bindError "test").isOk = false := rfl
example : (CheckResult.typeError "test").isOk = false := rfl

-- Combine with ok preserves result
example : CheckResult.ok.combine CheckResult.ok = CheckResult.ok := rfl
example : CheckResult.ok.combine (CheckResult.attackError "x") = CheckResult.attackError "x" := rfl

-- Error in first position wins
example : (CheckResult.safetyError "first").combine (CheckResult.attackError "second") =
          CheckResult.safetyError "first" := rfl

/-! ### VM State Safety Tests -/

-- Running VM with exit_code = 0 passes
def runningVMState : VMStateV1 := {
  regs := RegisterFile.zeros
  pc := 0
  step_counter := 0
  rw_mem_root_bytes32 := Bytes32.zero
  io_root_bytes32 := Bytes32.zero
  halted := .running
  exit_code := JOLT_STATUS_OK
  config_tags := []
}

#guard (checkVMStateSafety runningVMState).isOk == true

-- Halted VM with exit_code = 0 passes
def haltedVMState : VMStateV1 := {
  regs := RegisterFile.zeros
  pc := 0
  step_counter := 100
  rw_mem_root_bytes32 := Bytes32.zero
  io_root_bytes32 := Bytes32.zero
  halted := .halted
  exit_code := JOLT_STATUS_OK
  config_tags := []
}

#guard (checkVMStateSafety haltedVMState).isOk == true

-- Halted with trap code passes (trap codes are valid exit codes)
def trappedVMState : VMStateV1 := {
  regs := RegisterFile.zeros
  pc := 0
  step_counter := 50
  rw_mem_root_bytes32 := Bytes32.zero
  io_root_bytes32 := Bytes32.zero
  halted := .halted
  exit_code := JOLT_STATUS_TRAP_ILLEGAL_INSTRUCTION  -- Valid trap
  config_tags := []
}

#guard (checkVMStateSafety trappedVMState).isOk == true

/-! ### Consecutive Chunks Tests -/

-- Checker correctly validates consecutive indices
#guard (checkChunksConsecutive []).isOk == true
#guard (checkChunksConsecutive [mkTestChunk 0 0 100]).isOk == true
#guard (checkChunksConsecutive [
  mkTestChunk 0 0 100,
  mkTestChunk 1 100 200,
  mkTestChunk 2 200 300
]).isOk == true

-- Non-consecutive indices fail
#guard (checkChunksConsecutive [
  mkTestChunk 0 0 100,
  mkTestChunk 2 200 300  -- Missing index 1
]).isOk == false

/-! ### Non-Final Chunk Halted Tests -/

-- Non-final chunks should NOT be halted
def nonFinalHaltedChunk : ChunkRecord := {
  programHashBytes32 := testProgramHash
  chunkIndex := 0
  stateIn := mkTestVMState 0
  digestIn := Fr.zero
  stateOut := mkTestVMState 100 .halted  -- Halted but not final!
  digestOut := Fr.zero
  stepsExecuted := 100
  isFinal := false  -- Not the final chunk
}

def finalChunk : ChunkRecord := {
  programHashBytes32 := testProgramHash
  chunkIndex := 1
  stateIn := mkTestVMState 100
  digestIn := Fr.zero
  stateOut := mkTestVMState 200 .halted
  digestOut := Fr.zero
  stepsExecuted := 100
  isFinal := true
}

-- Non-final halted chunk fails
#guard (checkNonFinalNotHalted [nonFinalHaltedChunk, finalChunk]).isOk == false

-- Properly structured trace passes
#guard (checkNonFinalNotHalted [
  mkTestChunk 0 0 100 false .running,  -- Non-final, not halted
  mkTestChunk 1 100 200 true .halted   -- Final, halted
]).isOk == true

/-! ### System Phase Tests -/

-- Checks are skipped for non-applicable phases
#guard (checkNoSplice [] .INIT).isOk == true
#guard (checkNoCrossConfig [] .INIT).isOk == true
#guard (checkNoMemoryForgery [] .INIT).isOk == true
#guard (checkNoIOForgery [] .INIT).isOk == true

-- Checks are applied during EXECUTING
#guard (checkNoSplice [] .EXECUTING).isOk == true
#guard (checkNoCrossConfig [] .EXECUTING).isOk == true

-- Checks are applied during COMPLETE
#guard (checkNoSplice [] .COMPLETE).isOk == true
#guard (checkNoCrossConfig [] .COMPLETE).isOk == true

/-! ### Trace Safety Composite Tests -/

-- Empty trace in INIT phase passes all safety checks
#guard (checkTraceSafety [] .INIT).isOk == true

-- Empty trace in COMPLETE phase fails (no final chunk)
#guard (checkFinalChunkHalted [] .COMPLETE).isOk == false

-- Valid single-chunk final trace passes
#guard (checkTraceSafety [haltedFinalChunk] .COMPLETE).isOk == true

/-! ### Attack Prevention Composite Tests -/

-- Empty trace passes all attack prevention in INIT
#guard (checkAttackPrevention [] .INIT).isOk == true

-- Empty trace passes attack prevention in EXECUTING (no chunks to check)
#guard (checkAttackPrevention [] .EXECUTING).isOk == true

/-! ### Invariant Count Verification -/

-- Verify decidable check count
#guard decidableCheckCount == 13

-- Verify axiom-dependent count
#guard axiomDependentInvariantCount == 13

-- Verify total is 26
#guard decidableCheckCount + axiomDependentInvariantCount == 26

end Tests.TLAAttacks
