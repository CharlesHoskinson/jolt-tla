import Jolt.Types
import Jolt.Encoding
import Jolt.Transcript
import Jolt.ConfigTags

/-!
# Jolt Kernel State Digest

Implements S11.10: StateDigestV1 14-step absorption algorithm.

## Main Definitions

* `VMStateV1` - VM state fields needed for digest computation
* `stateDigestV1` - The 14-step StateDigestV1 algorithm
* `HaltedFlag` - Running/Halted status

## References

* Jolt Spec S11.10 (StateDigestV1 algorithm)
* Jolt Spec S11.5 (VMStateV1 structure)
-/

namespace Jolt.StateDigest

open Jolt Encoding Transcript ConfigTags

/-! ### Halted Flag -/

/-- VM halted status.

A VM is either running or halted. Halted VMs have an exit code. -/
inductive HaltedFlag where
  /-- VM is still running. -/
  | running
  /-- VM has halted. -/
  | halted
  deriving DecidableEq, Repr, Inhabited

namespace HaltedFlag

/-- Convert to Fr (0 for running, 1 for halted). -/
def toFr (h : HaltedFlag) : Fr :=
  match h with
  | running => Fr.zero
  | halted => Fr.one

/-- Convert to Bool. -/
def toBool (h : HaltedFlag) : Bool :=
  match h with
  | running => false
  | halted => true

/-- BEq instance. -/
instance : BEq HaltedFlag := ⟨fun a b =>
  match a, b with
  | running, running => true
  | halted, halted => true
  | _, _ => false⟩

end HaltedFlag

/-! ### Exit Code -/

/-- Exit code for halted VM (8-bit unsigned). -/
abbrev ExitCode := UInt8

/-- Standard exit codes. -/
def EXIT_SUCCESS : ExitCode := 0
def EXIT_FAILURE : ExitCode := 1

/-! ### VM State Structure -/

/-- VM state fields needed for digest computation.

Per spec S11.5 (VMStateV1), contains all consensus-critical state. -/
structure VMStateV1 where
  /-- Register file (32 registers, x0 hardwired to zero). -/
  regs : RegFile
  /-- Program counter. -/
  pc : U64
  /-- Step counter (instructions executed). -/
  stepCounter : U64
  /-- RW memory Merkle root (32 bytes). -/
  rwRoot : Bytes32
  /-- IO memory Merkle root (32 bytes). -/
  ioRoot : Bytes32
  /-- Halted flag. -/
  halted : HaltedFlag
  /-- Exit code (meaningful only when halted). -/
  exitCode : ExitCode
  /-- Configuration tags (sorted and unique). -/
  configTags : ConfigTags
  deriving Repr, DecidableEq

namespace VMStateV1

/-- Initial VM state (all zeros, not halted). -/
def initial : VMStateV1 := {
  regs := RegFile.initial
  pc := 0
  stepCounter := 0
  rwRoot := Bytes32.zero
  ioRoot := Bytes32.zero
  halted := HaltedFlag.running
  exitCode := 0
  configTags := []
}

/-- Check if VM is halted. -/
def isHalted (s : VMStateV1) : Bool := s.halted.toBool

/-- Check if VM exited successfully. -/
def isSuccessfulHalt (s : VMStateV1) : Bool :=
  s.isHalted && s.exitCode == EXIT_SUCCESS

/-- Read a register (x0 always returns zero). -/
def readReg (s : VMStateV1) (i : Fin 32) : Fr :=
  if i.val = 0 then Fr.zero else s.regs.read i

/-- BEq for VMStateV1 (derived from DecidableEq for LawfulBEq). -/
instance : BEq VMStateV1 := ⟨fun a b => decide (a = b)⟩

/-- LawfulBEq for VMStateV1. -/
instance : LawfulBEq VMStateV1 where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-- Inhabited instance. -/
instance : Inhabited VMStateV1 := ⟨VMStateV1.initial⟩

end VMStateV1

/-! ### StateDigestV1 Algorithm -/

/-- Domain separator for StateDigestV1. -/
def STATE_DIGEST_DOMAIN : String := "StateDigestV1"

/-- Absorb a Bytes32 as Fr2 (lo, hi) into transcript.

Returns the (possibly unchanged) transcript if encoding fails. -/
noncomputable def absorbBytes32AsFr2 (ts : TranscriptState) (b : Bytes32) : TranscriptState :=
  match Bytes32ToFr2 b with
  | some fr2 => ts.absorbFr fr2.lo |>.absorbFr fr2.hi
  | none => ts  -- Should not happen for valid Bytes32

/-- Helper to absorb registers. -/
noncomputable def absorbRegs (ts : TranscriptState) (regs : RegFile) : TranscriptState :=
  let indices : List (Fin 32) := List.finRange 32
  indices.foldl (fun ts i => ts.absorbFr (regs.get i)) ts

/-- StateDigestV1: 14-step absorption algorithm.

Per spec S11.10, this computes a cryptographic commitment to the
entire VM state by absorbing all state fields into a Poseidon transcript. -/
noncomputable def stateDigestV1 (programHash : Bytes32) (state : VMStateV1) : Fr :=
  let ts := TranscriptState.init

  -- Step 1: Domain separator
  let ts := ts.absorbString STATE_DIGEST_DOMAIN

  -- Step 2: Program hash (as Fr2)
  let ts := absorbBytes32AsFr2 ts programHash

  -- Step 3: Registers (32 Fr elements)
  let ts := absorbRegs ts state.regs

  -- Step 4: PC
  let ts := ts.absorbU64 state.pc

  -- Step 5: Step counter
  let ts := ts.absorbU64 state.stepCounter

  -- Step 6: RW root (as Fr2)
  let ts := absorbBytes32AsFr2 ts state.rwRoot

  -- Step 7: IO root (as Fr2)
  let ts := absorbBytes32AsFr2 ts state.ioRoot

  -- Step 8: Halted flag
  let ts := ts.absorbFr state.halted.toFr

  -- Step 9: Exit code
  let ts := ts.absorbFr (Fr.ofNat state.exitCode.toNat)

  -- Steps 10-12: Config tags (count, names, values)
  let ts := absorbIntoTranscript ts state.configTags

  -- Steps 13-14: Final squeeze
  (ts.squeezeFr).1

/-! ### Collision Resistance Axiom -/

/-- Axiom: StateDigest is collision resistant.

If two (programHash, state) pairs produce the same digest,
then the pairs are equal.

This is the key security property that enables continuation security.
It follows from the collision resistance of PoseidonPermute. -/
axiom stateDigest_collision_resistant :
  ∀ (ph1 ph2 : Bytes32) (s1 s2 : VMStateV1),
    stateDigestV1 ph1 s1 = stateDigestV1 ph2 s2 →
    ph1 = ph2 ∧ s1 = s2

/-! ### Specification Predicates -/

/-- Specification: StateDigest is deterministic. -/
def SpecDeterministic : Prop :=
  ∀ ph1 ph2 s1 s2,
    ph1 = ph2 → s1 = s2 →
    stateDigestV1 ph1 s1 = stateDigestV1 ph2 s2

/-- Specification: StateDigest binds program hash. -/
def SpecBindsProgramHash (programHash1 programHash2 : Bytes32) (state : VMStateV1) : Prop :=
  programHash1 ≠ programHash2 →
  stateDigestV1 programHash1 state ≠ stateDigestV1 programHash2 state

/-- Specification: StateDigest binds state. -/
def SpecBindsState (programHash : Bytes32) (state1 state2 : VMStateV1) : Prop :=
  state1 ≠ state2 →
  stateDigestV1 programHash state1 ≠ stateDigestV1 programHash state2

/-! ### Soundness Theorems -/

/-- THEOREM: StateDigest is deterministic. -/
theorem stateDigest_deterministic : SpecDeterministic := by
  intro ph1 ph2 s1 s2 hph hs
  rw [hph, hs]

/-- THEOREM: StateDigest binds program hash. -/
theorem stateDigest_binds_programHash (programHash1 programHash2 : Bytes32) (state : VMStateV1) :
    SpecBindsProgramHash programHash1 programHash2 state := by
  intro hne heq
  have ⟨hph, _⟩ := stateDigest_collision_resistant programHash1 programHash2 state state heq
  exact hne hph

/-- THEOREM: StateDigest binds state. -/
theorem stateDigest_binds_state (programHash : Bytes32) (state1 state2 : VMStateV1) :
    SpecBindsState programHash state1 state2 := by
  intro hne heq
  have ⟨_, hs⟩ := stateDigest_collision_resistant programHash programHash state1 state2 heq
  exact hne hs

/-! ### Derived Properties -/

/-- Different programs yield different digests. -/
theorem different_programs_different_digests (ph1 ph2 : Bytes32) (s : VMStateV1)
    (h : ph1 ≠ ph2) :
    stateDigestV1 ph1 s ≠ stateDigestV1 ph2 s := by
  intro heq
  have ⟨hph, _⟩ := stateDigest_collision_resistant ph1 ph2 s s heq
  exact h hph

/-- Different states yield different digests. -/
theorem different_states_different_digests (ph : Bytes32) (s1 s2 : VMStateV1)
    (h : s1 ≠ s2) :
    stateDigestV1 ph s1 ≠ stateDigestV1 ph s2 := by
  intro heq
  have ⟨_, hs⟩ := stateDigest_collision_resistant ph ph s1 s2 heq
  exact h hs

end Jolt.StateDigest
