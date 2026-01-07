import Jolt.Types
import Jolt.StateDigest

/-!
# Jolt Kernel Continuations

Chunk chaining validation for continuation proofs.

## Main Definitions

* `ChunkRecord` - A single chunk's execution record
* `ExecutionTrace` - Sequence of chunks forming a continuation
* `checkContinuationChain` - Validate digest chaining

## Continuation Security Model

The key invariant is: digest_out[i] = digest_in[i+1]

This ensures:
1. No chunk skipping (consecutive indices)
2. No chunk splicing (digests must match)
3. No cross-config attacks (config in digest)
4. Execution integrity (each chunk proves its transition)

## References

* Jolt Spec S11 (Continuations)
* Jolt Spec S11.10 (StateDigest linking)
-/

namespace Jolt.Continuations

open Jolt StateDigest

/-! ### Chunk Record -/

/-- A single chunk's execution record.

Contains all information needed to verify one chunk of a continuation:
- Program hash (must match across all chunks)
- Input/output digests (for chaining)
- Input/output states (for verification)
- Chunk index (must be consecutive)
- Steps executed (bounded by CHUNK_MAX_STEPS) -/
structure ChunkRecord where
  /-- Program hash (must match ExecutionTrace.programHash). -/
  programHash : Bytes32
  /-- StateDigest of input state. -/
  digestIn : Fr
  /-- StateDigest of output state. -/
  digestOut : Fr
  /-- Input VM state. -/
  stateIn : VMStateV1
  /-- Output VM state. -/
  stateOut : VMStateV1
  /-- Chunk index (0-based). -/
  chunkIndex : Nat
  /-- Steps executed in this chunk. -/
  stepsInChunk : U64
  deriving Repr

namespace ChunkRecord

/-- Check if digests are consistent with states.

digestIn should equal stateDigestV1(programHash, stateIn)
digestOut should equal stateDigestV1(programHash, stateOut) -/
noncomputable def digestsConsistent (c : ChunkRecord) : Bool :=
  c.digestIn == stateDigestV1 c.programHash c.stateIn &&
  c.digestOut == stateDigestV1 c.programHash c.stateOut

/-- BEq instance. -/
instance : BEq ChunkRecord := ⟨fun a b =>
  a.programHash == b.programHash &&
  a.digestIn == b.digestIn &&
  a.digestOut == b.digestOut &&
  a.chunkIndex == b.chunkIndex &&
  a.stepsInChunk == b.stepsInChunk⟩

/-- Inhabited instance. -/
instance : Inhabited ChunkRecord := ⟨{
  programHash := Bytes32.zero
  digestIn := Fr.zero
  digestOut := Fr.zero
  stateIn := VMStateV1.initial
  stateOut := VMStateV1.initial
  chunkIndex := 0
  stepsInChunk := 0
}⟩

end ChunkRecord

/-! ### Execution Trace -/

/-- Execution trace: sequence of chunks forming a continuation.

All chunks must have the same program hash.
Digests must chain: chunk[i].digestOut = chunk[i+1].digestIn -/
structure ExecutionTrace where
  /-- Program hash (same for all chunks). -/
  programHash : Bytes32
  /-- Sequence of chunk records. -/
  chunks : List ChunkRecord
  /-- Initial state (stateIn of first chunk). -/
  initialState : VMStateV1
  /-- Final state (stateOut of last chunk). -/
  finalState : VMStateV1
  deriving Repr

namespace ExecutionTrace

/-- Empty trace. -/
def empty : ExecutionTrace := {
  programHash := Bytes32.zero
  chunks := []
  initialState := VMStateV1.initial
  finalState := VMStateV1.initial
}

/-- Number of chunks. -/
def length (t : ExecutionTrace) : Nat := t.chunks.length

/-- First chunk (if any). -/
def firstChunk (t : ExecutionTrace) : Option ChunkRecord := t.chunks.head?

/-- Last chunk (if any). -/
def lastChunk (t : ExecutionTrace) : Option ChunkRecord := t.chunks.getLast?

/-- Get chunk by index. -/
def getChunk? (t : ExecutionTrace) (i : Nat) : Option ChunkRecord := t.chunks[i]?

/-- BEq instance. -/
instance : BEq ExecutionTrace := ⟨fun a b =>
  a.programHash == b.programHash && a.chunks == b.chunks⟩

/-- Inhabited instance. -/
instance : Inhabited ExecutionTrace := ⟨ExecutionTrace.empty⟩

end ExecutionTrace

/-! ### Specification Predicates -/

/-- Specification: Adjacent chunks have matching digests.

This is the core chaining invariant. -/
def SpecChainContinuity (trace : ExecutionTrace) : Prop :=
  ∀ i, i + 1 < trace.chunks.length →
    match trace.chunks[i]?, trace.chunks[i + 1]? with
    | some c1, some c2 => c1.digestOut = c2.digestIn
    | _, _ => True

/-- Specification: First chunk starts from initial state. -/
def SpecInitialBinding (trace : ExecutionTrace) : Prop :=
  match trace.chunks.head? with
  | some first =>
    first.digestIn = stateDigestV1 trace.programHash trace.initialState ∧
    first.stateIn = trace.initialState
  | none => True

/-- Specification: Last chunk ends at final state. -/
def SpecFinalBinding (trace : ExecutionTrace) : Prop :=
  match trace.chunks.getLast? with
  | some last =>
    last.digestOut = stateDigestV1 trace.programHash trace.finalState ∧
    last.stateOut = trace.finalState
  | none => True

/-- Specification: Chunk indices are consecutive starting from 0. -/
def SpecConsecutiveIndices (trace : ExecutionTrace) : Prop :=
  ∀ i, i < trace.chunks.length →
    match trace.chunks[i]? with
    | some c => c.chunkIndex = i
    | none => True

/-- Specification: All chunks have same program hash. -/
def SpecSameProgramHash (trace : ExecutionTrace) : Prop :=
  ∀ c ∈ trace.chunks, c.programHash = trace.programHash

/-- Specification: All chunk digests are consistent with states. -/
def SpecDigestsConsistent (trace : ExecutionTrace) : Prop :=
  ∀ c ∈ trace.chunks, c.digestsConsistent = true

/-- Specification: Config tags are preserved during execution.

This captures the invariant that configTags are immutable: a chunk's
stateOut has the same configTags as its stateIn. -/
def SpecConfigTagsPreserved (trace : ExecutionTrace) : Prop :=
  ∀ c ∈ trace.chunks, c.stateOut.configTags = c.stateIn.configTags

/-- Combined specification for valid continuation. -/
def SpecContinuations (trace : ExecutionTrace) : Prop :=
  SpecChainContinuity trace ∧
  SpecInitialBinding trace ∧
  SpecFinalBinding trace ∧
  SpecConsecutiveIndices trace ∧
  SpecSameProgramHash trace ∧
  SpecDigestsConsistent trace ∧
  SpecConfigTagsPreserved trace

/-! ### Checker Functions -/

/-- Check chain continuity: each chunk's digestOut = next chunk's digestIn. -/
def checkChainContinuity (chunks : List ChunkRecord) : Bool :=
  match chunks with
  | [] => true
  | [_] => true
  | c1 :: c2 :: rest => c1.digestOut == c2.digestIn && checkChainContinuity (c2 :: rest)

/-- Check initial binding. -/
noncomputable def checkInitialBinding (trace : ExecutionTrace) : Bool :=
  match trace.chunks.head? with
  | some first =>
    first.digestIn == stateDigestV1 trace.programHash trace.initialState &&
    first.stateIn == trace.initialState
  | none => true

/-- Check final binding. -/
noncomputable def checkFinalBinding (trace : ExecutionTrace) : Bool :=
  match trace.chunks.getLast? with
  | some last =>
    last.digestOut == stateDigestV1 trace.programHash trace.finalState &&
    last.stateOut == trace.finalState
  | none => true

/-- Check consecutive chunk indices.

Each chunk at position i should have chunkIndex = i. -/
def checkConsecutiveIndices (chunks : List ChunkRecord) : Bool :=
  let indexed := chunks.zip (List.range chunks.length)
  indexed.all (fun (c, i) => c.chunkIndex == i)

/-- Check all chunks have same program hash. -/
def checkSameProgramHash (trace : ExecutionTrace) : Bool :=
  trace.chunks.all (fun c => c.programHash == trace.programHash)

/-- Check all chunk digests are consistent. -/
noncomputable def checkDigestsConsistent (chunks : List ChunkRecord) : Bool :=
  chunks.all ChunkRecord.digestsConsistent

/-- Check config tags are preserved (stateOut.configTags = stateIn.configTags). -/
def checkConfigTagsPreserved (chunks : List ChunkRecord) : Bool :=
  chunks.all (fun c => c.stateOut.configTags == c.stateIn.configTags)

/-- Combined continuation chain checker. -/
noncomputable def checkContinuationChain (trace : ExecutionTrace) : Bool :=
  checkChainContinuity trace.chunks &&
  checkInitialBinding trace &&
  checkFinalBinding trace &&
  checkConsecutiveIndices trace.chunks &&
  checkSameProgramHash trace &&
  checkDigestsConsistent trace.chunks &&
  checkConfigTagsPreserved trace.chunks

/-! ### Soundness Theorems -/

/-- THEOREM: checkChainContinuity soundness. -/
theorem checkChainContinuity_sound (chunks : List ChunkRecord) :
    checkChainContinuity chunks = true →
    ∀ i, i + 1 < chunks.length →
      match chunks[i]?, chunks[i + 1]? with
      | some c1, some c2 => c1.digestOut = c2.digestIn
      | _, _ => True := by
  intro h i hi
  induction chunks generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp only [List.length_singleton] at hi
      omega
    | cons hd2 tl2 =>
      simp only [checkChainContinuity, Bool.and_eq_true] at h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero]
        exact eq_of_beq h.1
      | succ j =>
        -- Need to show: match (hd :: hd2 :: tl2)[j+1]?, (hd :: hd2 :: tl2)[j+2]? with ...
        -- Which is: match (hd2 :: tl2)[j]?, (hd2 :: tl2)[j+1]? with ...
        have hj1 : j + 1 < (hd2 :: tl2).length := by simp only [List.length_cons] at hi ⊢; omega
        have ih_result := ih h.2 j hj1
        -- Rewrite both sides to match
        simp only [List.getElem?_cons_succ] at ih_result ⊢
        exact ih_result

/-- Helper: Extract checkInitialBinding result. -/
theorem checkInitialBinding_sound (trace : ExecutionTrace) :
    checkInitialBinding trace = true → SpecInitialBinding trace := by
  intro h
  simp only [SpecInitialBinding]
  simp only [checkInitialBinding] at h
  cases hhead : trace.chunks.head? with
  | none => trivial
  | some first =>
    rw [hhead] at h
    simp only [Bool.and_eq_true] at h
    constructor
    · exact eq_of_beq h.1
    · exact eq_of_beq h.2

/-- Helper: Extract checkFinalBinding result. -/
theorem checkFinalBinding_sound (trace : ExecutionTrace) :
    checkFinalBinding trace = true → SpecFinalBinding trace := by
  intro h
  simp only [SpecFinalBinding]
  simp only [checkFinalBinding] at h
  cases hlast : trace.chunks.getLast? with
  | none => trivial
  | some last =>
    rw [hlast] at h
    simp only [Bool.and_eq_true] at h
    constructor
    · exact eq_of_beq h.1
    · exact eq_of_beq h.2

/-- Helper: List.all extraction at index. -/
theorem list_all_get {α : Type} (l : List α) (p : α → Bool) (i : Nat) (hi : i < l.length)
    (h : l.all p = true) : p (l.get ⟨i, hi⟩) = true := by
  induction l generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases i with
    | zero => exact h.1
    | succ j =>
      simp only [List.get_cons_succ]
      exact ih j (Nat.lt_of_succ_lt_succ hi) h.2

/-- Helper: List.all implies property for members. -/
theorem list_all_mem {α : Type} (l : List α) (p : α → Bool)
    (h : l.all p = true) : ∀ x ∈ l, p x = true := by
  intro x hx
  induction l with
  | nil => simp at hx
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases hx with
    | head => exact h.1
    | tail _ hx' => exact ih h.2 hx'

/-- Helper: Check indices from offset (simpler form). -/
def checkIndicesFrom (chunks : List ChunkRecord) (offset : Nat) : Bool :=
  match chunks with
  | [] => true
  | c :: rest => c.chunkIndex == offset && checkIndicesFrom rest (offset + 1)

/-- Helper: checkIndicesFrom soundness. -/
theorem checkIndicesFrom_sound (chunks : List ChunkRecord) (offset : Nat) :
    checkIndicesFrom chunks offset = true →
    ∀ i (hi : i < chunks.length), (chunks.get ⟨i, hi⟩).chunkIndex = offset + i := by
  intro h i hi
  induction chunks generalizing i offset with
  | nil => simp at hi
  | cons hd tl ih =>
    simp only [checkIndicesFrom, Bool.and_eq_true, beq_iff_eq] at h
    cases i with
    | zero =>
      simp only [List.get_cons_zero, Nat.add_zero]
      exact h.1
    | succ j =>
      simp only [List.get_cons_succ, List.length_cons] at hi ⊢
      have hj : j < tl.length := Nat.lt_of_succ_lt_succ hi
      have := ih (offset + 1) h.2 j hj
      omega

/-- Helper: zip/range all to checkIndicesFrom. -/
theorem zipRangeAll_to_checkFrom (chunks : List ChunkRecord) (offset : Nat) :
    (chunks.zip (List.range chunks.length)).all
      (fun p => p.1.chunkIndex == p.2 + offset) = true →
    checkIndicesFrom chunks offset = true := by
  intro h
  induction chunks generalizing offset with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.zip_cons_cons,
               List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [checkIndicesFrom, Bool.and_eq_true, beq_iff_eq]
    constructor
    · simp only [Nat.zero_add] at h; exact h.1
    · simp only [List.zip_map_right, List.all_map] at h
      apply ih (offset + 1)
      simp only [List.all_eq_true]
      intro p hp
      have h2 := h.2
      simp only [List.all_eq_true] at h2
      specialize h2 p hp
      simp only [Function.comp_apply, id_eq] at h2
      simp only [beq_iff_eq] at h2 ⊢
      -- h2 : (Prod.map id Nat.succ p).1.chunkIndex = (Prod.map id Nat.succ p).2 + offset
      -- Unfold Prod.map in h2
      unfold Prod.map at h2
      simp only [id_eq] at h2
      -- Now h2 should be: p.1.chunkIndex = (p.2 + 1) + offset
      -- goal : p.1.chunkIndex = p.2 + (offset + 1)
      omega

/-- Helper: checkConsecutiveIndices implies checkIndicesFrom 0. -/
theorem checkConsecutiveIndices_implies_from (chunks : List ChunkRecord) :
    checkConsecutiveIndices chunks = true → checkIndicesFrom chunks 0 = true := by
  intro h
  simp only [checkConsecutiveIndices] at h
  -- h : (chunks.zip (range chunks.length)).all (fun p => p.1.chunkIndex == p.2) = true
  -- Need: checkIndicesFrom chunks 0 = true
  have h' : (chunks.zip (List.range chunks.length)).all
      (fun p => p.1.chunkIndex == p.2 + 0) = true := by
    simp only [Nat.add_zero]
    exact h
  exact zipRangeAll_to_checkFrom chunks 0 h'

/-- Helper: Extract checkConsecutiveIndices result. -/
theorem checkConsecutiveIndices_sound (chunks : List ChunkRecord) :
    checkConsecutiveIndices chunks = true →
    ∀ i, i < chunks.length →
      match chunks[i]? with
      | some c => c.chunkIndex = i
      | none => True := by
  intro h i hi
  have hget : chunks[i]? = some (chunks.get ⟨i, hi⟩) := by simp [hi]
  simp only [hget]
  have hfrom := checkConsecutiveIndices_implies_from chunks h
  have := checkIndicesFrom_sound chunks 0 hfrom i hi
  simp only [Nat.zero_add] at this
  exact this

/-- Helper: Extract checkSameProgramHash result. -/
theorem checkSameProgramHash_sound (trace : ExecutionTrace) :
    checkSameProgramHash trace = true → SpecSameProgramHash trace := by
  intro h
  simp only [SpecSameProgramHash, checkSameProgramHash] at *
  intro c hc
  have := list_all_mem trace.chunks (fun c => c.programHash == trace.programHash) h c hc
  exact eq_of_beq this

/-- Helper: Extract checkDigestsConsistent result. -/
theorem checkDigestsConsistent_sound (chunks : List ChunkRecord) :
    checkDigestsConsistent chunks = true →
    ∀ c ∈ chunks, c.digestsConsistent = true := by
  intro h c hc
  simp only [checkDigestsConsistent] at h
  exact list_all_mem chunks ChunkRecord.digestsConsistent h c hc

/-- Helper: Extract checkConfigTagsPreserved result. -/
theorem checkConfigTagsPreserved_sound (chunks : List ChunkRecord) :
    checkConfigTagsPreserved chunks = true →
    ∀ c ∈ chunks, c.stateOut.configTags = c.stateIn.configTags := by
  intro h c hc
  simp only [checkConfigTagsPreserved] at h
  have := list_all_mem chunks (fun c => c.stateOut.configTags == c.stateIn.configTags) h c hc
  simp only [beq_iff_eq] at this
  exact this

/-- THEOREM: checkContinuationChain soundness.

If checkContinuationChain passes, continuation specification holds. -/
theorem checkContinuationChain_sound (trace : ExecutionTrace) :
    checkContinuationChain trace = true → SpecContinuations trace := by
  intro h
  simp only [checkContinuationChain, Bool.and_eq_true] at h
  simp only [SpecContinuations]
  -- Extract individual checks (7 conjuncts)
  have h_chain := h.1.1.1.1.1.1
  have h_init := h.1.1.1.1.1.2
  have h_final := h.1.1.1.1.2
  have h_consec := h.1.1.1.2
  have h_same := h.1.1.2
  have h_digest := h.1.2
  have h_config := h.2
  constructor
  · -- ChainContinuity
    simp only [SpecChainContinuity]
    intro i hi
    exact checkChainContinuity_sound trace.chunks h_chain i hi
  constructor
  · -- InitialBinding
    exact checkInitialBinding_sound trace h_init
  constructor
  · -- FinalBinding
    exact checkFinalBinding_sound trace h_final
  constructor
  · -- ConsecutiveIndices
    simp only [SpecConsecutiveIndices]
    exact checkConsecutiveIndices_sound trace.chunks h_consec
  constructor
  · -- SameProgramHash
    exact checkSameProgramHash_sound trace h_same
  constructor
  · -- DigestsConsistent
    simp only [SpecDigestsConsistent]
    exact checkDigestsConsistent_sound trace.chunks h_digest
  · -- ConfigTagsPreserved
    simp only [SpecConfigTagsPreserved]
    exact checkConfigTagsPreserved_sound trace.chunks h_config

/-! ### Attack Prevention -/

/-- Helper: Get chunk at index when index is valid. -/
theorem get_chunk_some (chunks : List ChunkRecord) (i : Nat) (hi : i < chunks.length) :
    chunks[i]? = some (chunks.get ⟨i, hi⟩) := by simp [hi]

/-- Helper: digestsConsistent implies digestOut = stateDigestV1 ph stateOut. -/
theorem digestsConsistent_out (c : ChunkRecord) (h : c.digestsConsistent = true) :
    c.digestOut = stateDigestV1 c.programHash c.stateOut := by
  simp only [ChunkRecord.digestsConsistent, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- Helper: digestsConsistent implies digestIn = stateDigestV1 ph stateIn. -/
theorem digestsConsistent_in (c : ChunkRecord) (h : c.digestsConsistent = true) :
    c.digestIn = stateDigestV1 c.programHash c.stateIn := by
  simp only [ChunkRecord.digestsConsistent, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- Splice attack: Cannot splice chunks from different executions.

If c1.digestOut = c2.digestIn and both chunks have consistent digests,
then by StateDigest collision resistance, c1.stateOut = c2.stateIn
(assuming same program hash). -/
theorem splice_attack_prevented (trace : ExecutionTrace)
    (h_chain : SpecChainContinuity trace)
    (h_digest : SpecDigestsConsistent trace)
    (h_same_ph : SpecSameProgramHash trace)
    (i : Nat) (hi : i + 1 < trace.chunks.length) :
    match trace.chunks[i]?, trace.chunks[i + 1]? with
    | some c1, some c2 =>
      c1.digestOut = c2.digestIn →
      c1.stateOut = c2.stateIn
    | _, _ => True := by
  -- Get the chunks
  have hi1 : i < trace.chunks.length := Nat.lt_of_succ_lt hi
  have hi2 : i + 1 < trace.chunks.length := hi
  rw [get_chunk_some trace.chunks i hi1, get_chunk_some trace.chunks (i+1) hi2]
  intro h_eq
  -- Get the chunks
  let c1 := trace.chunks.get ⟨i, hi1⟩
  let c2 := trace.chunks.get ⟨i + 1, hi2⟩
  -- Both chunks have consistent digests
  have hc1_mem : c1 ∈ trace.chunks := List.get_mem trace.chunks ⟨i, hi1⟩
  have hc2_mem : c2 ∈ trace.chunks := List.get_mem trace.chunks ⟨i+1, hi2⟩
  have hc1_cons := h_digest c1 hc1_mem
  have hc2_cons := h_digest c2 hc2_mem
  -- Both chunks have same program hash
  have hc1_ph := h_same_ph c1 hc1_mem
  have hc2_ph := h_same_ph c2 hc2_mem
  -- c1.digestOut = stateDigestV1 c1.programHash c1.stateOut
  --              = stateDigestV1 trace.programHash c1.stateOut
  have h_out := digestsConsistent_out c1 hc1_cons
  -- c2.digestIn = stateDigestV1 c2.programHash c2.stateIn
  --             = stateDigestV1 trace.programHash c2.stateIn
  have h_in := digestsConsistent_in c2 hc2_cons
  -- From h_eq: c1.digestOut = c2.digestIn
  -- So: stateDigestV1 trace.programHash c1.stateOut = stateDigestV1 trace.programHash c2.stateIn
  rw [hc1_ph] at h_out
  rw [hc2_ph] at h_in
  have h_digest_eq : stateDigestV1 trace.programHash c1.stateOut =
                     stateDigestV1 trace.programHash c2.stateIn := by
    rw [← h_out, ← h_in, h_eq]
  -- By collision resistance, c1.stateOut = c2.stateIn
  have ⟨_, h_state⟩ := stateDigest_collision_resistant trace.programHash trace.programHash
    c1.stateOut c2.stateIn h_digest_eq
  exact h_state

/-- Skip attack: Cannot skip chunks.

Consecutive indices prevent gaps in the execution. -/
theorem skip_attack_prevented (trace : ExecutionTrace)
    (h_indices : SpecConsecutiveIndices trace) :
    ∀ i, i < trace.chunks.length →
      match trace.chunks[i]? with
      | some c => c.chunkIndex = i
      | none => True := by
  exact h_indices

/-- Helper: All chunks in a valid trace have configTags equal to initial state.

This is the key lemma for cross-config attack prevention. It uses:
1. First chunk binds to initial state (SpecInitialBinding)
2. Config tags preserved within chunks (SpecConfigTagsPreserved)
3. Adjacent chunks chain via splice prevention (states match at boundaries) -/
theorem all_chunks_same_configTags (trace : ExecutionTrace)
    (h_digest : SpecDigestsConsistent trace)
    (h_chain : SpecChainContinuity trace)
    (h_same_ph : SpecSameProgramHash trace)
    (h_init : SpecInitialBinding trace)
    (h_preserved : SpecConfigTagsPreserved trace)
    (c : ChunkRecord) (hc : c ∈ trace.chunks)
    (i : Nat) (hi : i < trace.chunks.length)
    (hci : trace.chunks.get ⟨i, hi⟩ = c) :
    c.stateIn.configTags = trace.initialState.configTags := by
  induction i generalizing c with
  | zero =>
    -- First chunk: stateIn = initialState by SpecInitialBinding
    simp only [SpecInitialBinding] at h_init
    -- Get the first chunk - use membership to get head
    cases htrace : trace.chunks with
    | nil =>
      -- Empty list contradicts hi
      simp only [htrace, List.length_nil] at hi
      omega
    | cons first rest =>
      -- h_init is about trace.chunks.head?
      rw [htrace] at h_init
      simp only [List.head?_cons] at h_init
      -- We need to show c = first
      -- After the match, hci : trace.chunks.get ⟨0, hi⟩ = c
      -- And trace.chunks = first :: rest
      -- So (first :: rest).get ⟨0, hi⟩ = c, and get at 0 is first
      have hfirst : first = c := by
        -- Since htrace : trace.chunks = first :: rest
        -- and hci : trace.chunks.get ⟨0, hi⟩ = c
        -- The 0th element of first :: rest is first
        -- Use decidability: first and trace.chunks.get ⟨0, hi⟩ are the same value
        have : (first :: rest)[0] = first := rfl
        -- trace.chunks = first :: rest, so trace.chunks[0] = first
        have h0 : trace.chunks[0] = first := by simp only [htrace]; rfl
        -- trace.chunks.get ⟨0, hi⟩ = trace.chunks[0] for valid index
        have heq : trace.chunks.get ⟨0, hi⟩ = trace.chunks[0] := rfl
        rw [heq, h0] at hci
        exact hci
      rw [← hfirst]
      exact congrArg (·.configTags) h_init.2
  | succ j ih =>
    -- Inductive step: use chaining and config preservation
    have hj : j < trace.chunks.length := Nat.lt_of_succ_lt hi
    let cj := trace.chunks.get ⟨j, hj⟩
    -- By IH: cj.stateIn.configTags = initial.configTags
    have hcj_mem : cj ∈ trace.chunks := List.get_mem trace.chunks ⟨j, hj⟩
    have h_cj_cfg := ih cj hcj_mem hj rfl
    -- cj preserves config: cj.stateOut.configTags = cj.stateIn.configTags
    have h_cj_preserved := h_preserved cj hcj_mem
    -- Chain continuity: cj.digestOut = c.digestIn
    have h_chain_jc := h_chain j hi
    -- Convert from getElem? to get
    have heq_j : trace.chunks[j]? = some (trace.chunks.get ⟨j, hj⟩) := by simp [hj]
    have heq_j1 : trace.chunks[j + 1]? = some (trace.chunks.get ⟨j + 1, hi⟩) := by simp [hi]
    rw [heq_j, heq_j1, hci] at h_chain_jc
    -- Use collision resistance to show cj.stateOut = c.stateIn
    have hcj_cons := h_digest cj hcj_mem
    have hc_cons := h_digest c hc
    have hcj_ph := h_same_ph cj hcj_mem
    have hc_ph := h_same_ph c hc
    have h_out := digestsConsistent_out cj hcj_cons
    have h_in := digestsConsistent_in c hc_cons
    rw [hcj_ph] at h_out
    rw [hc_ph] at h_in
    have h_digest_eq : stateDigestV1 trace.programHash cj.stateOut =
                       stateDigestV1 trace.programHash c.stateIn := by
      rw [← h_out, ← h_in, h_chain_jc]
    have ⟨_, h_state⟩ := stateDigest_collision_resistant trace.programHash trace.programHash
      cj.stateOut c.stateIn h_digest_eq
    -- h_state : cj.stateOut = c.stateIn
    calc c.stateIn.configTags
        = cj.stateOut.configTags := congrArg (·.configTags) h_state.symm
      _ = cj.stateIn.configTags := h_cj_preserved
      _ = trace.initialState.configTags := h_cj_cfg

/-- Helper: Get index from membership. -/
theorem mem_get_index {α : Type} (l : List α) (x : α) (hx : x ∈ l) :
    ∃ (i : Nat) (hi : i < l.length), l.get ⟨i, hi⟩ = x := by
  induction l with
  | nil => simp at hx
  | cons hd tl ih =>
    cases hx with
    | head => exact ⟨0, Nat.zero_lt_succ _, rfl⟩
    | tail _ hx' =>
      have ⟨i, hi, hget⟩ := ih hx'
      exact ⟨i + 1, Nat.succ_lt_succ hi, by simp only [List.get_cons_succ]; exact hget⟩

/-- Cross-config attack: Cannot use different configs.

If chunks are chained, have consistent digests, same program hash,
and config tags are preserved, then all chunks have the same configTags. -/
theorem cross_config_attack_prevented (trace : ExecutionTrace)
    (h_digest : SpecDigestsConsistent trace)
    (h_chain : SpecChainContinuity trace)
    (h_same_ph : SpecSameProgramHash trace)
    (h_init : SpecInitialBinding trace)
    (h_preserved : SpecConfigTagsPreserved trace)
    (c1 c2 : ChunkRecord) (hc1 : c1 ∈ trace.chunks) (hc2 : c2 ∈ trace.chunks) :
    c1.stateIn.configTags = c2.stateIn.configTags := by
  -- Get indices for c1 and c2
  have ⟨i1, hi1, hci1⟩ := mem_get_index trace.chunks c1 hc1
  have ⟨i2, hi2, hci2⟩ := mem_get_index trace.chunks c2 hc2
  have h1 := all_chunks_same_configTags trace h_digest h_chain h_same_ph h_init h_preserved
    c1 hc1 i1 hi1 hci1
  have h2 := all_chunks_same_configTags trace h_digest h_chain h_same_ph h_init h_preserved
    c2 hc2 i2 hi2 hci2
  rw [h1, h2]

end Jolt.Continuations
