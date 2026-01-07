import Jolt.Types
import Jolt.Encoding
import Jolt.StateDigest

/-!
# Jolt Kernel Wrapper

Implements S5.2: PublicInputsV1 (11 Fr elements) and S5.6: Wrapper binding constraints.

## Main Definitions

* `PublicInputsV1` - The 11 Fr elements exposed to the on-chain verifier
* `checkWrapper` - Validate wrapper binding constraints
* `assemblePublicInputs` - Construct public inputs from execution state

## Public Inputs Layout (S5.2)

| Index | Field | Range Constraint |
|-------|-------|------------------|
| 0 | programHashLo | < 2^248 |
| 1 | programHashHi | < 256 |
| 2 | digestIn | (full Fr) |
| 3 | digestOut | (full Fr) |
| 4 | batchCommitmentLo | < 2^248 |
| 5 | batchCommitmentHi | < 256 |
| 6 | statusFr | < 256 |
| 7 | batchNonceFr | < 2^64 |
| 8 | reserved1 | = 0 |
| 9 | reserved2 | = 0 |
| 10 | reserved3 | = 0 |

## Implementation Notes

The wrapper circuit verifies that:
1. Range constraints are satisfied
2. Digests match StateDigestV1 computation
3. Program hash encoding is correct

## References

* Jolt Spec S5.2 (PublicInputsV1)
* Jolt Spec S5.6 (Wrapper binding constraints)
-/

namespace Jolt.Wrapper

open Jolt Encoding StateDigest

/-! ### Status Codes -/

/-- Jolt status codes for public inputs. -/
def JOLT_STATUS_OK : UInt8 := 0
def JOLT_STATUS_PANIC : UInt8 := 1
def JOLT_STATUS_TIMEOUT : UInt8 := 2
def JOLT_STATUS_UNFINISHED : UInt8 := 3

/-! ### PublicInputsV1 Structure -/

/-- PublicInputsV1: exactly 11 Fr elements exposed to on-chain verifier.

Per spec S5.2, these are the only values visible to the verifier.
All security guarantees must be derived from verifying these values. -/
structure PublicInputsV1 where
  /-- Program hash low part (< 2^248). -/
  programHashLo : Fr
  /-- Program hash high part (< 256). -/
  programHashHi : Fr
  /-- Digest of initial state. -/
  digestIn : Fr
  /-- Digest of final state. -/
  digestOut : Fr
  /-- Batch commitment low part (< 2^248). -/
  batchCommitmentLo : Fr
  /-- Batch commitment high part (< 256). -/
  batchCommitmentHi : Fr
  /-- Status (< 256). -/
  statusFr : Fr
  /-- Batch nonce (< 2^64). -/
  batchNonceFr : Fr
  /-- Reserved field 1 (must be 0). -/
  reserved1 : Fr
  /-- Reserved field 2 (must be 0). -/
  reserved2 : Fr
  /-- Reserved field 3 (must be 0). -/
  reserved3 : Fr
  deriving DecidableEq, Repr

namespace PublicInputsV1

/-- Number of public inputs. -/
def count : Nat := 11

/-- Zero public inputs (for testing). -/
def zero : PublicInputsV1 := {
  programHashLo := Fr.zero
  programHashHi := Fr.zero
  digestIn := Fr.zero
  digestOut := Fr.zero
  batchCommitmentLo := Fr.zero
  batchCommitmentHi := Fr.zero
  statusFr := Fr.zero
  batchNonceFr := Fr.zero
  reserved1 := Fr.zero
  reserved2 := Fr.zero
  reserved3 := Fr.zero
}

/-- Convert to list of Fr elements. -/
def toList (pi : PublicInputsV1) : List Fr :=
  [pi.programHashLo, pi.programHashHi,
   pi.digestIn, pi.digestOut,
   pi.batchCommitmentLo, pi.batchCommitmentHi,
   pi.statusFr, pi.batchNonceFr,
   pi.reserved1, pi.reserved2, pi.reserved3]

/-- Create from list of Fr elements. -/
def fromList? (xs : List Fr) : Option PublicInputsV1 :=
  if h : xs.length = 11 then
    some {
      programHashLo := xs.get ⟨0, by omega⟩
      programHashHi := xs.get ⟨1, by omega⟩
      digestIn := xs.get ⟨2, by omega⟩
      digestOut := xs.get ⟨3, by omega⟩
      batchCommitmentLo := xs.get ⟨4, by omega⟩
      batchCommitmentHi := xs.get ⟨5, by omega⟩
      statusFr := xs.get ⟨6, by omega⟩
      batchNonceFr := xs.get ⟨7, by omega⟩
      reserved1 := xs.get ⟨8, by omega⟩
      reserved2 := xs.get ⟨9, by omega⟩
      reserved3 := xs.get ⟨10, by omega⟩
    }
  else none

/-- Theorem: toList has length 11. -/
theorem toList_length (pi : PublicInputsV1) : pi.toList.length = 11 := rfl

/-- BEq instance. -/
instance : BEq PublicInputsV1 := ⟨fun a b =>
  a.programHashLo == b.programHashLo &&
  a.programHashHi == b.programHashHi &&
  a.digestIn == b.digestIn &&
  a.digestOut == b.digestOut &&
  a.batchCommitmentLo == b.batchCommitmentLo &&
  a.batchCommitmentHi == b.batchCommitmentHi &&
  a.statusFr == b.statusFr &&
  a.batchNonceFr == b.batchNonceFr &&
  a.reserved1 == b.reserved1 &&
  a.reserved2 == b.reserved2 &&
  a.reserved3 == b.reserved3⟩

/-- Inhabited instance. -/
instance : Inhabited PublicInputsV1 := ⟨PublicInputsV1.zero⟩

end PublicInputsV1

/-! ### Specification Predicates -/

/-- Specification: Range constraints on public inputs.

Per S5.2, certain fields have range constraints. -/
def SpecRanges (pi : PublicInputsV1) : Prop :=
  pi.programHashLo.val < 2^248 ∧
  pi.programHashHi.val < 256 ∧
  pi.batchCommitmentLo.val < 2^248 ∧
  pi.batchCommitmentHi.val < 256 ∧
  pi.statusFr.val < 256 ∧
  pi.batchNonceFr.val < 2^64 ∧
  pi.reserved1 = Fr.zero ∧
  pi.reserved2 = Fr.zero ∧
  pi.reserved3 = Fr.zero

/-- Specification: Binding to program hash.

The public input program hash must match the actual program hash.
This requires range constraints to hold, which are checked separately via SpecRanges. -/
def SpecProgramHashBinding (pi : PublicInputsV1) (programHash : Bytes32) : Prop :=
  ∃ fr2 : Fr2, Bytes32ToFr2 programHash = some fr2 ∧
    fr2.lo = pi.programHashLo ∧ fr2.hi = pi.programHashHi

/-- Specification: Binding to VM states via digest.

digestIn must be StateDigestV1 of initial state.
digestOut must be StateDigestV1 of final state. -/
def SpecDigestBinding (pi : PublicInputsV1) (programHash : Bytes32)
    (stateIn stateOut : VMStateV1) : Prop :=
  stateDigestV1 programHash stateIn = pi.digestIn ∧
  stateDigestV1 programHash stateOut = pi.digestOut

/-- Combined specification for wrapper validity. -/
def SpecWrapper (pi : PublicInputsV1) (programHash : Bytes32)
    (stateIn stateOut : VMStateV1) : Prop :=
  SpecRanges pi ∧
  SpecProgramHashBinding pi programHash ∧
  SpecDigestBinding pi programHash stateIn stateOut

/-! ### Checker Functions -/

/-- Check range constraints on public inputs. -/
def checkRanges (pi : PublicInputsV1) : Bool :=
  pi.programHashLo.val < 2^248 &&
  pi.programHashHi.val < 256 &&
  pi.batchCommitmentLo.val < 2^248 &&
  pi.batchCommitmentHi.val < 256 &&
  pi.statusFr.val < 256 &&
  pi.batchNonceFr.val < 2^64 &&
  pi.reserved1 == Fr.zero &&
  pi.reserved2 == Fr.zero &&
  pi.reserved3 == Fr.zero

/-- Check digest binding (requires computing StateDigestV1). -/
noncomputable def checkDigestBinding (pi : PublicInputsV1) (programHash : Bytes32)
    (stateIn stateOut : VMStateV1) : Bool :=
  stateDigestV1 programHash stateIn == pi.digestIn &&
  stateDigestV1 programHash stateOut == pi.digestOut

/-- Check program hash binding. -/
def checkProgramHashBinding (pi : PublicInputsV1) (programHash : Bytes32) : Bool :=
  match Bytes32ToFr2 programHash with
  | some fr2 => fr2.lo == pi.programHashLo && fr2.hi == pi.programHashHi
  | none => false

/-- Combined wrapper checker. -/
noncomputable def checkWrapper (pi : PublicInputsV1) (programHash : Bytes32)
    (stateIn stateOut : VMStateV1) : Bool :=
  checkRanges pi &&
  checkProgramHashBinding pi programHash &&
  checkDigestBinding pi programHash stateIn stateOut

/-! ### Soundness Theorems -/

/-- THEOREM: checkRanges soundness.

If checkRanges passes, range constraints hold. -/
theorem checkRanges_sound (pi : PublicInputsV1) :
    checkRanges pi = true → SpecRanges pi := by
  intro h
  simp only [checkRanges, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [SpecRanges]
  constructor; exact h.1.1.1.1.1.1.1.1
  constructor; exact h.1.1.1.1.1.1.1.2
  constructor; exact h.1.1.1.1.1.1.2
  constructor; exact h.1.1.1.1.1.2
  constructor; exact h.1.1.1.1.2
  constructor; exact h.1.1.1.2
  constructor
  · have h1 := h.1.1.2
    simp only [beq_iff_eq] at h1
    exact h1
  constructor
  · have h2 := h.1.2
    simp only [beq_iff_eq] at h2
    exact h2
  · have h3 := h.2
    simp only [beq_iff_eq] at h3
    exact h3

/-- THEOREM: checkProgramHashBinding soundness.

If checkProgramHashBinding passes, program hash binding holds. -/
theorem checkProgramHashBinding_sound (pi : PublicInputsV1) (programHash : Bytes32) :
    checkProgramHashBinding pi programHash = true →
    SpecProgramHashBinding pi programHash := by
  intro h
  simp only [checkProgramHashBinding] at h
  simp only [SpecProgramHashBinding]
  cases henc : Bytes32ToFr2 programHash with
  | none =>
    simp only [henc] at h
    exact absurd h (by decide)
  | some fr2 =>
    simp only [henc, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨fr2, rfl, h.1, h.2⟩

/-- THEOREM: checkDigestBinding soundness.

If checkDigestBinding passes, digest binding holds. -/
theorem checkDigestBinding_sound (pi : PublicInputsV1) (programHash : Bytes32)
    (stateIn stateOut : VMStateV1) :
    checkDigestBinding pi programHash stateIn stateOut = true →
    SpecDigestBinding pi programHash stateIn stateOut := by
  intro h
  simp only [checkDigestBinding, Bool.and_eq_true, beq_iff_eq] at h
  simp only [SpecDigestBinding]
  exact ⟨h.1, h.2⟩

/-- THEOREM: checkWrapper soundness.

If checkWrapper passes, wrapper specification holds. -/
theorem checkWrapper_sound (pi : PublicInputsV1) (programHash : Bytes32)
    (stateIn stateOut : VMStateV1) :
    checkWrapper pi programHash stateIn stateOut = true →
    SpecWrapper pi programHash stateIn stateOut := by
  intro h
  simp only [checkWrapper, Bool.and_eq_true] at h
  obtain ⟨⟨hr, hph⟩, hd⟩ := h
  simp only [SpecWrapper]
  constructor
  · exact checkRanges_sound pi hr
  constructor
  · exact checkProgramHashBinding_sound pi programHash hph
  · exact checkDigestBinding_sound pi programHash stateIn stateOut hd

/-! ### Public Input Assembly -/

/-- Assemble public inputs from execution result.

Creates PublicInputsV1 from:
- programHash: The program being executed
- stateIn: Initial VM state
- stateOut: Final VM state
- batchCommitment: Commitment to the batch manifest
- batchNonce: Unique nonce for this batch -/
noncomputable def assemblePublicInputs (programHash : Bytes32)
    (stateIn stateOut : VMStateV1)
    (batchCommitment : Bytes32)
    (batchNonce : U64) : Option PublicInputsV1 :=
  -- Encode program hash as Fr2
  match Bytes32ToFr2 programHash with
  | none => none
  | some phFr2 =>
    -- Encode batch commitment as Fr2
    match Bytes32ToFr2 batchCommitment with
    | none => none
    | some bcFr2 =>
      -- Compute digests
      let digestIn := stateDigestV1 programHash stateIn
      let digestOut := stateDigestV1 programHash stateOut
      -- Determine status
      let status : UInt8 :=
        if stateOut.isHalted then
          if stateOut.exitCode == EXIT_SUCCESS then JOLT_STATUS_OK
          else JOLT_STATUS_PANIC
        else JOLT_STATUS_UNFINISHED
      some {
        programHashLo := phFr2.lo
        programHashHi := phFr2.hi
        digestIn := digestIn
        digestOut := digestOut
        batchCommitmentLo := bcFr2.lo
        batchCommitmentHi := bcFr2.hi
        statusFr := Fr.ofNat status.toNat
        batchNonceFr := U64.toFr batchNonce
        reserved1 := Fr.zero
        reserved2 := Fr.zero
        reserved3 := Fr.zero
      }

/-- Assembled public inputs satisfy range constraints. -/
theorem assemblePublicInputs_ranges (programHash batchCommitment : Bytes32)
    (stateIn stateOut : VMStateV1) (batchNonce : U64) :
    match assemblePublicInputs programHash stateIn stateOut batchCommitment batchNonce with
    | some pi => SpecRanges pi
    | none => True := by
  unfold assemblePublicInputs
  cases h1 : Bytes32ToFr2 programHash with
  | none => trivial
  | some phFr2 =>
    cases h2 : Bytes32ToFr2 batchCommitment with
    | none => trivial
    | some bcFr2 =>
      unfold SpecRanges
      -- Goal is now the 9-fold conjunction
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact phFr2.lo_bound  -- programHashLo < 2^248
      · exact phFr2.hi_bound  -- programHashHi < 256
      · exact bcFr2.lo_bound  -- batchCommitmentLo < 2^248
      · exact bcFr2.hi_bound  -- batchCommitmentHi < 256
      · -- statusFr < 256
        simp only [Fr.ofNat]
        have hstat : ∀ b1 b2 : Bool,
            (if b1 then if b2 then JOLT_STATUS_OK else JOLT_STATUS_PANIC
             else JOLT_STATUS_UNFINISHED).toNat < 256 := by
          intro b1 b2; cases b1 <;> cases b2 <;> native_decide
        have hbound := hstat stateOut.isHalted (stateOut.exitCode == EXIT_SUCCESS)
        have h256 : (256 : Nat) ≤ Fr.modulus := by native_decide
        have hsmall : (if stateOut.isHalted then
            if stateOut.exitCode == EXIT_SUCCESS then JOLT_STATUS_OK else JOLT_STATUS_PANIC
           else JOLT_STATUS_UNFINISHED).toNat < Fr.modulus := Nat.lt_of_lt_of_le hbound h256
        simp only [Nat.mod_eq_of_lt hsmall]
        exact hbound
      · -- batchNonceFr < 2^64
        simp only [U64.toFr]
        have h264 : (2 : Nat)^64 < Fr.modulus := by native_decide
        have hbn : batchNonce.toNat < 2^64 := batchNonce.toBitVec.isLt
        omega
      · rfl  -- reserved1 = Fr.zero
      · rfl  -- reserved2 = Fr.zero
      · rfl  -- reserved3 = Fr.zero

end Jolt.Wrapper
