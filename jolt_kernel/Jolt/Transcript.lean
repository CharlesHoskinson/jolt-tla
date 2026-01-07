import Jolt.Types
import Jolt.Encoding

/-!
# Jolt Kernel Transcript

Implements S8: Poseidon-based transcript with typed absorption.

## Main Definitions

* `PoseidonPermute` - The permutation function (TRUSTED COMPUTING BASE)
* `TranscriptState` - Sponge state machine
* `absorbFr` - Absorb a single field element
* `absorbTag` - Absorb tag bytes (31-byte chunking)
* `squeezeFr` - Squeeze a challenge field element
* `PoseidonHashV1` - Hash helper for domain-separated hashing

## References

* Jolt Spec S8 (Transcript specification)
-/

namespace Jolt.Transcript

open Jolt Encoding

/-! ### Constants -/

/-- Poseidon state width (t parameter). -/
def stateWidth : Nat := 12

/-- Sponge rate (elements absorbed before permutation). -/
def rate : Nat := 11

/-- Sponge capacity (state width - rate). -/
def capacity : Nat := 1

/-- Proof that rate + capacity = stateWidth. -/
theorem rate_capacity_sum : rate + capacity = stateWidth := rfl

/-- Proof that rate < stateWidth. -/
theorem rate_lt_stateWidth : rate < stateWidth := by decide

/-! ### Poseidon Permutation (TRUSTED COMPUTING BASE) -/

/-- Poseidon permutation function.

**TRUSTED COMPUTING BASE** - This is the ONLY axiomatized cryptographic primitive.

The permutation takes a state vector of `stateWidth` Fr elements
and produces a permuted state vector.

All security properties of the transcript depend on this being
a cryptographically secure permutation. -/
axiom PoseidonPermute : Vec Fr stateWidth → Vec Fr stateWidth

/-! ### Sponge Mode -/

/-- Sponge mode determines valid operations.

- Absorb: Can absorb more data, cannot squeeze yet
- Squeeze: Can squeeze challenges, cannot absorb more -/
inductive Mode where
  /-- Absorbing data into the sponge. -/
  | Absorb
  /-- Squeezing challenges from the sponge. -/
  | Squeeze
  deriving DecidableEq, Repr, Inhabited

/-! ### Transcript State -/

/-- Transcript state for Fiat-Shamir transformation.

Implements a Poseidon sponge construction with:
- state: The internal sponge state vector
- pos: Current position in the rate portion
- mode: Whether we're absorbing or squeezing -/
structure TranscriptState where
  /-- Internal sponge state. -/
  state : Vec Fr stateWidth
  /-- Current position in rate portion (0 to rate-1). -/
  pos : Nat
  /-- Current mode (Absorb or Squeeze). -/
  mode : Mode
  deriving Repr

namespace TranscriptState

/-- Initial transcript state (all zeros, position 0, absorb mode). -/
def init : TranscriptState :=
  ⟨Vec.replicate stateWidth Fr.zero, 0, Mode.Absorb⟩

/-- Zero state vector. -/
def zeroState : Vec Fr stateWidth := Vec.replicate stateWidth Fr.zero

/-- Helper to get an index proof for rate-bounded positions. -/
private def posIdx (pos : Nat) (h : pos < rate) : Fin stateWidth :=
  ⟨pos, Nat.lt_trans h rate_lt_stateWidth⟩

/-- Absorb a single Fr element into the transcript (absorb mode only).

If state is full (pos >= rate), permute first.
XORs the element into the state at current position. -/
noncomputable def absorbFrAbsorb (state : Vec Fr stateWidth) (pos : Nat) (x : Fr) : TranscriptState :=
  if h : pos < rate then
    -- XOR into current position
    let newState := state.set (posIdx pos h) x
    ⟨newState, pos + 1, Mode.Absorb⟩
  else
    -- State full, permute first
    let permuted := PoseidonPermute state
    let newState := permuted.set ⟨0, by decide⟩ x
    ⟨newState, 1, Mode.Absorb⟩

/-- Absorb a single Fr element into the transcript.

If in Squeeze mode, reinitializes first (though this should be caught by checker). -/
noncomputable def absorbFr (ts : TranscriptState) (x : Fr) : TranscriptState :=
  match ts.mode with
  | Mode.Squeeze =>
    -- Cannot absorb after squeezing - reinitialize and absorb
    absorbFrAbsorb (Vec.replicate stateWidth Fr.zero) 0 x
  | Mode.Absorb =>
    absorbFrAbsorb ts.state ts.pos x

/-- Absorb a U64 value (converted to Fr). -/
noncomputable def absorbU64 (ts : TranscriptState) (x : U64) : TranscriptState :=
  ts.absorbFr (U64.toFr x)

/-- Absorb a list of Fr elements. -/
noncomputable def absorbFrs (ts : TranscriptState) (xs : List Fr) : TranscriptState :=
  xs.foldl absorbFr ts

/-- Chunk bytes into 31-byte segments.

Per spec S8.6: Tags are chunked into 31-byte pieces for absorption. -/
def chunkBytes31 (arr : List UInt8) : List (List UInt8) :=
  if arr.length <= 31 then [arr]
  else arr.take 31 :: chunkBytes31 (arr.drop 31)
termination_by arr.length

/-- Convert up to 31 bytes to Fr (little-endian). -/
def bytesToFr (bytes : List UInt8) : Fr :=
  let n := bytesToNatLE bytes
  Fr.ofNat n

/-- Absorb tag bytes per S8.6 (31-byte chunking). -/
noncomputable def absorbTag (ts : TranscriptState) (tag : List UInt8) : TranscriptState :=
  let chunks := chunkBytes31 tag
  let frs := chunks.map bytesToFr
  ts.absorbFrs frs

/-- Absorb a string as tag bytes. -/
noncomputable def absorbString (ts : TranscriptState) (s : String) : TranscriptState :=
  ts.absorbTag s.toUTF8.toList

/-- Finalize absorption (pad and permute).

Called before first squeeze operation. -/
noncomputable def finishAbsorb (ts : TranscriptState) : TranscriptState :=
  match ts.mode with
  | Mode.Squeeze => ts  -- Already finished
  | Mode.Absorb =>
    -- Add padding (1) at current position if not full
    let paddedState := if h : ts.pos < rate then
      ts.state.set (posIdx ts.pos h) Fr.one
    else ts.state
    let permuted := PoseidonPermute paddedState
    ⟨permuted, 0, Mode.Squeeze⟩

/-- Squeeze a challenge Fr element from the transcript.

If in Absorb mode, finishes absorption first.
Returns the squeezed element and updated state. -/
noncomputable def squeezeFr (ts : TranscriptState) : Fr × TranscriptState :=
  let ts' := match ts.mode with
    | Mode.Absorb => ts.finishAbsorb
    | Mode.Squeeze => ts
  if h : ts'.pos < rate then
    let output := ts'.state.get (posIdx ts'.pos h)
    (output, ⟨ts'.state, ts'.pos + 1, Mode.Squeeze⟩)
  else
    -- Need more output, permute
    let permuted := PoseidonPermute ts'.state
    let output := permuted.get ⟨0, by decide⟩
    (output, ⟨permuted, 1, Mode.Squeeze⟩)

/-- Squeeze multiple challenges. -/
noncomputable def squeezeFrs (ts : TranscriptState) (n : Nat) : List Fr × TranscriptState :=
  match n with
  | 0 => ([], ts)
  | n + 1 =>
    let (fr, ts') := ts.squeezeFr
    let (frs, ts'') := ts'.squeezeFrs n
    (fr :: frs, ts'')

end TranscriptState

/-! ### PoseidonHashV1 Helper -/

/-- PoseidonHashV1: domain-separated hash.

Per spec S8.7:
1. Initialize transcript
2. Absorb domain separator tag
3. Absorb data bytes
4. Squeeze one Fr challenge -/
noncomputable def PoseidonHashV1 (domain : List UInt8) (data : List UInt8) : Fr :=
  let ts := TranscriptState.init
  let ts := ts.absorbTag domain
  let ts := ts.absorbTag data
  (ts.squeezeFr).1

/-- PoseidonHashV1 with string domain. -/
noncomputable def PoseidonHashV1' (domain : String) (data : List UInt8) : Fr :=
  PoseidonHashV1 domain.toUTF8.toList data

/-! ### Specification Predicates -/

/-- Specification: transcript state is valid. -/
def SpecTranscriptValid (ts : TranscriptState) : Prop :=
  ts.pos < stateWidth

/-- Specification: absorb mode allows absorption. -/
def SpecCanAbsorb (ts : TranscriptState) : Prop :=
  ts.mode = Mode.Absorb

/-- Specification: squeeze mode after finalization. -/
def SpecCanSqueeze (ts : TranscriptState) : Prop :=
  ts.mode = Mode.Squeeze

/-! ### Checker Functions -/

/-- Check transcript state validity. -/
def checkTranscriptValid (ts : TranscriptState) : Bool :=
  ts.pos < stateWidth

/-- Check if transcript is in absorb mode. -/
def checkCanAbsorb (ts : TranscriptState) : Bool :=
  ts.mode == Mode.Absorb

/-- Check if transcript is in squeeze mode. -/
def checkCanSqueeze (ts : TranscriptState) : Bool :=
  ts.mode == Mode.Squeeze

/-! ### Soundness Theorems -/

/-- Initial transcript is valid. -/
theorem init_valid : SpecTranscriptValid TranscriptState.init := by
  simp only [SpecTranscriptValid, TranscriptState.init]
  decide

/-- Initial transcript is in absorb mode. -/
theorem init_can_absorb : SpecCanAbsorb TranscriptState.init := by
  simp only [SpecCanAbsorb, TranscriptState.init]

/-- finishAbsorb produces squeeze mode. -/
theorem finishAbsorb_squeeze (ts : TranscriptState) :
    (ts.finishAbsorb).mode = Mode.Squeeze := by
  unfold TranscriptState.finishAbsorb
  cases hm : ts.mode <;> simp [hm]

/-- squeezeFr produces a valid Fr. -/
theorem squeezeFr_produces_valid_fr (ts : TranscriptState) :
    let (fr, _) := ts.squeezeFr
    fr.val < Fr.modulus := by
  exact (ts.squeezeFr).1.isLt

end Jolt.Transcript
