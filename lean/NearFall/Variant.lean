import NearFall.Trace
import NearFall.Continuations

/-!
# Termination Variant for Liveness Proofs

Single Nat variant function for termination proofs, matching TLA+ SafetyInduction.tla.

## Main Definitions

* `MAX_CHUNKS` - Maximum number of chunks in an execution
* `CommittedChunks` - Number of chunks committed (alignment with TLA+)
* `RemainingChunks` - Chunks left to execute
* `StepsRemaining` - Steps left in current chunk (boundary-safe)
* `variant` - Single Nat termination measure
* `ProgressStep` - Actions that decrease the variant
* `NonProgressStep` - Actions that don't increase the variant

## Design Rationale

**Single Nat Variant**: Using a single `Nat` instead of a pair `(RemainingChunks, StepsRemaining)`
avoids lexicographic ordering pitfalls and simplifies well-foundedness proofs.

**Boundary-Safe StepsRemaining**: The formula `(CHUNK_MAX_STEPS - 1) - (step_counter % CHUNK_MAX_STEPS)`
reaches 0 at the chunk boundary, then resets to `CHUNK_MAX_STEPS - 1` while `RemainingChunks`
decreases by 1, guaranteeing strict decrease across the boundary.

**Progress Partition**: `Next` decomposes into `ProgressStep ∨ NonProgressStep` where:
- `ProgressStep` strictly decreases the variant
- `NonProgressStep` does not increase the variant

This is a LEMMA (derived from action definitions), not an axiom.

## References

* infinitestate.md Phase 2.4
* TLA+ SafetyInduction.tla (Variant definition)
-/

namespace NearFall.Liveness

open TLATypes VMState Continuations

/-! ### Protocol Constants -/

/-- Maximum number of chunks in an execution.

Note: This is a placeholder. In production, this would be read from configuration.
The proofs are valid for any positive value of MAX_CHUNKS.

**TLA+ equivalent**: `MAX_CHUNKS` constant -/
def MAX_CHUNKS : Nat := 1024

/-! ### Alignment Definitions -/

/-- Number of chunks committed so far.

**Alignment with TLA+**: This matches `CommittedChunks(sys) == Len(sys.continuation.chunks)`
in SafetyInduction.tla. The Lean definition uses `currentChunk` which equals `Len(chunks)`
after each `executeChunk` call.

**ALIGNMENT INVARIANT**: `CommittedChunks_Lean = CommittedChunks_TLA` -/
def CommittedChunks (s : SystemState) : Nat :=
  s.continuation.currentChunk

/-- Alternative definition using chunks list length (for verification). -/
def CommittedChunks' (s : SystemState) : Nat :=
  s.continuation.chunks.length

/-- Alignment theorem: both definitions agree. -/
theorem committedChunks_alignment (s : SystemState)
    (h_inv : s.continuation.currentChunk = s.continuation.chunks.length) :
    CommittedChunks s = CommittedChunks' s := by
  unfold CommittedChunks CommittedChunks'
  exact h_inv

/-! ### Variant Components -/

/-- Chunks remaining to execute.

**TLA+ equivalent**: `RemainingChunks(s) == MAX_CHUNKS - CommittedChunks(s)` -/
def RemainingChunks (s : SystemState) : Nat :=
  MAX_CHUNKS - CommittedChunks s

/-- Steps remaining in the current chunk.

**BOUNDARY-SAFE**: This formula reaches 0 at remainder `CHUNK_MAX_STEPS - 1`,
then resets to `CHUNK_MAX_STEPS - 1` while `RemainingChunks` decreases by 1.
This guarantees strict decrease across chunk boundaries.

**TLA+ equivalent**: `StepsRemaining(s) == (CHUNK_MAX_STEPS - 1) - (s.vmState.step_counter % CHUNK_MAX_STEPS)` -/
def StepsRemaining (s : SystemState) : Nat :=
  (CHUNK_MAX_STEPS - 1) - (s.vmState.step_counter % CHUNK_MAX_STEPS)

/-! ### Variant Function -/

/-- Single Nat termination measure.

The variant is 0 in terminal phases (COMPLETE or FAILED), and otherwise
combines remaining chunks and steps into a single decreasing measure.

**Formula**: `RemainingChunks * CHUNK_MAX_STEPS + StepsRemaining`

This single Nat avoids lexicographic ordering pitfalls.

**TLA+ equivalent**: `Variant(s)` in SafetyInduction.tla -/
def variant (s : SystemState) : Nat :=
  match s.phase with
  | .COMPLETE => 0
  | .FAILED => 0
  | .INIT => RemainingChunks s * CHUNK_MAX_STEPS + StepsRemaining s
  | .EXECUTING => RemainingChunks s * CHUNK_MAX_STEPS + StepsRemaining s

/-- Alternative definition using if-then-else (for verification). -/
def variant' (s : SystemState) : Nat :=
  if s.phase = .COMPLETE ∨ s.phase = .FAILED then 0
  else RemainingChunks s * CHUNK_MAX_STEPS + StepsRemaining s

/-- Both variant definitions agree. -/
theorem variant_eq_variant' (s : SystemState) : variant s = variant' s := by
  unfold variant variant'
  cases s.phase <;> simp [SystemPhase.noConfusion]

/-! ### Type Invariants -/

/-- TypeOK constraint for variant computation. -/
structure VariantTypeOK (s : SystemState) : Prop where
  /-- Committed chunks bounded by MAX_CHUNKS. -/
  chunks_bounded : CommittedChunks s ≤ MAX_CHUNKS
  /-- Step counter is consistent with chunk index. -/
  step_counter_bounded : s.vmState.step_counter ≤ (CommittedChunks s + 1) * CHUNK_MAX_STEPS

/-- Variant is non-negative (trivially true for Nat). -/
theorem variant_nonneg (s : SystemState) : variant s ≥ 0 :=
  Nat.zero_le _

/-- Variant is bounded. -/
theorem variant_bounded (s : SystemState) (h : VariantTypeOK s) :
    variant s ≤ MAX_CHUNKS * CHUNK_MAX_STEPS + (CHUNK_MAX_STEPS - 1) := by
  unfold variant
  cases s.phase <;> simp
  all_goals {
    have h1 : RemainingChunks s ≤ MAX_CHUNKS := by
      unfold RemainingChunks
      have := h.chunks_bounded
      omega
    have h2 : StepsRemaining s ≤ CHUNK_MAX_STEPS - 1 := by
      unfold StepsRemaining
      have := Nat.mod_lt s.vmState.step_counter (by decide : CHUNK_MAX_STEPS > 0)
      omega
    calc RemainingChunks s * CHUNK_MAX_STEPS + StepsRemaining s
        ≤ MAX_CHUNKS * CHUNK_MAX_STEPS + StepsRemaining s := by
          apply Nat.add_le_add_right
          exact Nat.mul_le_mul_right CHUNK_MAX_STEPS h1
      _ ≤ MAX_CHUNKS * CHUNK_MAX_STEPS + (CHUNK_MAX_STEPS - 1) := by
          apply Nat.add_le_add_left h2
  }

/-! ### Progress Partition -/

/-- Progress step: actions that strictly decrease the variant.

These are:
1. `ExecuteChunk` - commits a chunk (increments currentChunk)
2. `CompleteExecution` - transitions to COMPLETE phase (variant → 0)
3. `ExecutionFailed` - transitions to FAILED phase (variant → 0)

**TLA+ equivalent**: `ProgressStep == ExecuteOneChunk \/ CompleteExecution \/ ExecutionFailed` -/
def ProgressStep (s s' : SystemState) : Prop :=
  ExecuteChunk s s' ∨ CompleteExecution s s' ∨ ExecutionFailed s s'

/-- Non-progress step: actions that don't increase the variant.

These are:
1. `StartExecution` - transitions INIT → EXECUTING (no chunk/step change)
2. Stuttering - no state change

**TLA+ equivalent**: `NonProgressStep == StartExecution \/ (UNCHANGED vars)` -/
def NonProgressStep (s s' : SystemState) : Prop :=
  StartExecution s s' ∨ s' = s

/-! ### Decomposition Lemmas -/

/-- Step decomposes into ProgressStep or NonProgressStep (or both are disjoint from Step).

This is a structural lemma showing that every Step action is either a progress step
or (for StartExecution) a non-progress step. -/
theorem step_classification (s s' : SystemState) (h : Step s s') :
    ProgressStep s s' ∨ NonProgressStep s s' := by
  unfold Step at h
  unfold ProgressStep NonProgressStep
  cases h with
  | inl h_start => right; left; exact h_start
  | inr h_rest =>
    cases h_rest with
    | inl h_exec => left; left; exact h_exec
    | inr h_rest2 =>
      cases h_rest2 with
      | inl h_complete => left; right; left; exact h_complete
      | inr h_failed => left; right; right; exact h_failed

/-- StepOrStutter decomposes into ProgressStep, NonProgressStep (stuttering), or StartExecution. -/
theorem stepOrStutter_classification (s s' : SystemState) (h : StepOrStutter s s') :
    ProgressStep s s' ∨ NonProgressStep s s' := by
  cases h with
  | inl h_step => exact step_classification s s' h_step
  | inr h_stutter => right; right; exact h_stutter

/-- Next decomposes into ProgressStep or NonProgressStep.

This is the key partition lemma for variant proofs.

**TLA+ equivalent**: `LEMMA NextDecomposes == Next <=> ProgressStep \/ NonProgressStep` -/
theorem next_decomposes (s s' : SystemState) (h : Step s s') :
    ProgressStep s s' ∨ NonProgressStep s s' :=
  step_classification s s' h

/-! ### Variant Decrease Lemmas -/

/-- ExecuteChunk decreases the variant.

When a chunk is executed, `currentChunk` increases by 1, so `RemainingChunks`
decreases by 1. The variant decreases because:
`variant' = (RemainingChunks - 1) * MAX_STEPS + StepsRemaining' < RemainingChunks * MAX_STEPS + StepsRemaining` -/
theorem variant_decreases_executeChunk (s s' : SystemState)
    (h_step : ExecuteChunk s s')
    (h_inv : VariantTypeOK s)
    (h_chunks_remain : CommittedChunks s < MAX_CHUNKS) :
    variant s' < variant s := by
  -- Extract facts from ExecuteChunk
  have h_phase : s.phase = .EXECUTING := h_step.1
  have h_phase' : s'.phase = .EXECUTING := h_step.2.2.1
  have h_chunk : s'.continuation.currentChunk = s.continuation.currentChunk + 1 := h_step.2.2.2.1
  -- Unfold variant in both states
  unfold variant
  simp only [h_phase, h_phase']
  -- Set up abbreviations for clarity
  let k := s.continuation.currentChunk
  let k' := s'.continuation.currentChunk
  let C := CHUNK_MAX_STEPS
  let M := MAX_CHUNKS
  -- StepsRemaining bounds
  have h_steps_s : StepsRemaining s ≤ C - 1 := by
    unfold StepsRemaining
    have := Nat.mod_lt s.vmState.step_counter (by decide : CHUNK_MAX_STEPS > 0)
    omega
  have h_steps' : StepsRemaining s' ≤ C - 1 := by
    unfold StepsRemaining
    have := Nat.mod_lt s'.vmState.step_counter (by decide : CHUNK_MAX_STEPS > 0)
    omega
  have h_bounded : k ≤ M := h_inv.chunks_bounded
  have h_chunk_eq : k' = k + 1 := h_chunk
  -- Key inequality: (M - k') * C + S' < (M - k) * C + S
  -- where k' = k + 1 and S' ≤ C - 1
  unfold RemainingChunks CommittedChunks
  simp only [h_chunk]
  -- Since k < M (from h_chunks_remain), we have M - (k + 1) + 1 = M - k
  have h_k_lt_M : k < M := h_chunks_remain
  have h_sub : M - (k + 1) + 1 = M - k := by omega
  -- (M - (k+1)) * C + S' < (M - k) * C + S
  -- Since (M - (k+1) + 1) * C = (M - k) * C and S' ≤ C - 1 < C
  have h_C_pos : C > 0 := by decide
  have h_expand : (M - (k + 1) + 1) * C = (M - (k + 1)) * C + C := Nat.succ_mul (M - (k + 1)) C
  calc (M - (k + 1)) * C + StepsRemaining s'
      ≤ (M - (k + 1)) * C + (C - 1) := Nat.add_le_add_left h_steps' _
    _ < (M - (k + 1)) * C + C := by omega
    _ = (M - (k + 1) + 1) * C := h_expand.symm
    _ = (M - k) * C := by simp [h_sub]
    _ ≤ (M - k) * C + StepsRemaining s := Nat.le_add_right _ _

/-- CompleteExecution sets variant to 0. -/
theorem variant_zero_complete (s s' : SystemState)
    (h_step : CompleteExecution s s') :
    variant s' = 0 := by
  unfold variant
  have h_phase : s'.phase = .COMPLETE := h_step.2.2.1
  simp [h_phase]

/-- ExecutionFailed sets variant to 0. -/
theorem variant_zero_failed (s s' : SystemState)
    (h_step : ExecutionFailed s s') :
    variant s' = 0 := by
  unfold variant
  have h_phase : s'.phase = .FAILED := h_step.2.2.1
  simp [h_phase]

/-- Variant is 0 in terminal phases. -/
theorem variant_terminal_zero (s : SystemState)
    (h_term : s.phase = .COMPLETE ∨ s.phase = .FAILED) :
    variant s = 0 := by
  unfold variant
  cases h_term with
  | inl h => simp [h]
  | inr h => simp [h]

/-- Variant is positive in non-terminal phases (given TypeOK). -/
theorem variant_nonterminal_pos (s : SystemState)
    (h_nonterm : s.phase = .INIT ∨ s.phase = .EXECUTING)
    (_h_inv : VariantTypeOK s)
    (h_chunks_pos : CommittedChunks s < MAX_CHUNKS) :
    variant s > 0 := by
  unfold variant
  cases h_nonterm with
  | inl h =>
    simp [h]
    unfold RemainingChunks CommittedChunks
    have h_rem_pos : MAX_CHUNKS - s.continuation.currentChunk > 0 := by
      have := h_chunks_pos
      unfold CommittedChunks at this
      omega
    have h_C_pos : CHUNK_MAX_STEPS > 0 := by decide
    have h_prod_pos : (MAX_CHUNKS - s.continuation.currentChunk) * CHUNK_MAX_STEPS > 0 :=
      Nat.mul_pos h_rem_pos h_C_pos
    omega
  | inr h =>
    simp [h]
    unfold RemainingChunks CommittedChunks
    have h_rem_pos : MAX_CHUNKS - s.continuation.currentChunk > 0 := by
      have := h_chunks_pos
      unfold CommittedChunks at this
      omega
    have h_C_pos : CHUNK_MAX_STEPS > 0 := by decide
    have h_prod_pos : (MAX_CHUNKS - s.continuation.currentChunk) * CHUNK_MAX_STEPS > 0 :=
      Nat.mul_pos h_rem_pos h_C_pos
    omega

/-- Progress step strictly decreases variant.

This is the main theorem for termination under fairness.

**TLA+ equivalent**: `LEMMA VariantDecrease == IndInv /\ ProgressStep => Variant(sys') < Variant(sys)` -/
theorem variant_decreases (s s' : SystemState)
    (h_step : ProgressStep s s')
    (h_inv : VariantTypeOK s)
    (h_nonterminal : s.phase ≠ .COMPLETE ∧ s.phase ≠ .FAILED)
    (h_chunks_remain : CommittedChunks s < MAX_CHUNKS) :
    variant s' < variant s := by
  unfold ProgressStep at h_step
  cases h_step with
  | inl h_exec =>
    exact variant_decreases_executeChunk s s' h_exec h_inv h_chunks_remain
  | inr h_rest =>
    cases h_rest with
    | inl h_complete =>
      have h0 : variant s' = 0 := variant_zero_complete s s' h_complete
      have h_pos : variant s > 0 := variant_nonterminal_pos s
        (by cases h_nonterminal; cases h_s : s.phase <;> simp_all)
        h_inv h_chunks_remain
      omega
    | inr h_failed =>
      have h0 : variant s' = 0 := variant_zero_failed s s' h_failed
      have h_pos : variant s > 0 := variant_nonterminal_pos s
        (by cases h_nonterminal; cases h_s : s.phase <;> simp_all)
        h_inv h_chunks_remain
      omega

/-! ### Variant Non-Increase Lemmas -/

/-- StartExecution doesn't change variant components.

Phase changes from INIT to EXECUTING, but `currentChunk` and `step_counter`
are unchanged, so the variant formula yields the same value. -/
theorem variant_preserved_startExecution (s s' : SystemState)
    (h_step : StartExecution s s') :
    variant s' = variant s := by
  unfold variant
  have h_from : s.phase = .INIT := h_step.1
  have h_to : s'.phase = .EXECUTING := h_step.2.1
  have h_cont : s'.continuation = s.continuation := h_step.2.2.2.1
  have h_vm : s'.vmState = s.vmState := h_step.2.2.1
  simp only [h_from, h_to]
  unfold RemainingChunks CommittedChunks StepsRemaining
  simp [h_cont, h_vm]

/-- Stuttering preserves variant exactly. -/
theorem variant_stutter (s : SystemState) : variant s = variant s := rfl

/-- Non-progress steps don't increase variant.

This is critical for liveness: while waiting for a progress step,
the variant doesn't go up.

**TLA+ equivalent**: `LEMMA VariantNonIncrease == IndInv /\ NonProgressStep => Variant(sys') <= Variant(sys)` -/
theorem variant_nonIncrease (s s' : SystemState)
    (h_step : NonProgressStep s s') :
    variant s' ≤ variant s := by
  unfold NonProgressStep at h_step
  cases h_step with
  | inl h_start =>
    have h_eq := variant_preserved_startExecution s s' h_start
    omega
  | inr h_stutter =>
    rw [h_stutter]
    exact Nat.le_refl _

/-! ### Terminal State Invariants -/

/-! ### Summary Theorems -/

/-- Variant decrease under fair progress: key theorem for termination.

If the system is in a non-terminal state and a progress step occurs,
the variant strictly decreases. Combined with weak fairness on progress
actions, this guarantees eventual termination. -/
theorem fair_progress_terminates (s s' : SystemState)
    (h_step : ProgressStep s s')
    (h_inv : VariantTypeOK s)
    (h_nonterm : s.phase = .INIT ∨ s.phase = .EXECUTING)
    (h_chunks_remain : CommittedChunks s < MAX_CHUNKS) :
    variant s' < variant s := by
  have h : s.phase ≠ .COMPLETE ∧ s.phase ≠ .FAILED := by
    cases h_nonterm <;> simp_all [SystemPhase.noConfusion]
  exact variant_decreases s s' h_step h_inv h h_chunks_remain

end NearFall.Liveness
