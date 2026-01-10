import NearFall.Trace
import NearFall.Variant
import NearFall.Fairness
import NearFall.Liveness

/-!
# Progress and No-Deadlock Lemmas

Proofs that the system cannot deadlock in non-terminal states.

## Main Theorems

* `no_deadlock` - In non-terminal states, at least one action is enabled
* `init_can_progress` - INIT phase can always transition
* `executing_can_progress` - EXECUTING phase can always transition
* `terminal_absorbing` - Terminal phases only allow stuttering

## Design Notes

No-deadlock is a key safety property that complements liveness.
Even without fairness, we can prove that progress is always *possible*.

With fairness (Phase D), we prove progress is *guaranteed*.

## References

* infinitestate.md Phase 2.5
* TLA+ SafetyInduction.tla (no-deadlock invariant)
-/

namespace NearFall.Progress

open TLATypes VMState Continuations Liveness

/-! ### No-Deadlock in INIT -/

/-- In INIT phase, StartExecution is always enabled.

This is immediate since StartExecution only requires phase = INIT. -/
theorem init_can_progress (s : SystemState)
    (h_init : s.phase = .INIT) :
    Enabled StartExecution s :=
  startExecution_enabled s h_init

/-- INIT phase has exactly one enabled action: StartExecution. -/
theorem init_unique_action (s : SystemState)
    (h_init : s.phase = .INIT) :
    Enabled StartExecution s ∧
    ¬Enabled ExecuteChunk s ∧
    ¬Enabled CompleteExecution s ∧
    ¬Enabled ExecutionFailed s := by
  constructor
  · exact startExecution_enabled s h_init
  constructor
  · intro ⟨s', h⟩
    -- ExecuteChunk requires EXECUTING
    have : s.phase = .EXECUTING := h.1
    simp [h_init] at this
  constructor
  · intro ⟨s', h⟩
    -- CompleteExecution requires EXECUTING
    have : s.phase = .EXECUTING := h.1
    simp [h_init] at this
  · intro ⟨s', h⟩
    -- ExecutionFailed requires EXECUTING
    have : s.phase = .EXECUTING := h.1
    simp [h_init] at this

/-! ### No-Deadlock in EXECUTING -/

/-- In EXECUTING phase with incomplete continuation, ExecuteChunk is enabled. -/
theorem executing_incomplete_can_progress (s : SystemState)
    (h_exec : s.phase = .EXECUTING)
    (h_not_complete : ¬s.continuation.isComplete)
    (h_not_trapped : ¬s.vmState.isTrappedHalt) :
    Enabled ExecuteChunk s :=
  executeChunk_enabled s h_exec h_not_complete

/-- In EXECUTING phase with complete continuation, CompleteExecution is enabled. -/
theorem executing_complete_can_progress (s : SystemState)
    (h_exec : s.phase = .EXECUTING)
    (h_complete : s.continuation.isComplete) :
    Enabled CompleteExecution s := by
  unfold Enabled CompleteExecution
  let s' : SystemState := {
    phase := .COMPLETE
    vmState := s.vmState
    continuation := s.continuation
    programHash := s.programHash
  }
  exact ⟨s', h_exec, h_complete, rfl, rfl⟩

/-- In EXECUTING phase with trapped VM, ExecutionFailed is enabled. -/
theorem executing_trapped_can_progress (s : SystemState)
    (h_exec : s.phase = .EXECUTING)
    (h_trapped : s.vmState.isTrappedHalt) :
    Enabled ExecutionFailed s := by
  unfold Enabled ExecutionFailed
  let s' : SystemState := {
    phase := .FAILED
    vmState := s.vmState
    continuation := s.continuation
    programHash := s.programHash
  }
  exact ⟨s', h_exec, h_trapped, rfl, rfl⟩

/-- EXECUTING phase always has at least one enabled action. -/
theorem executing_can_progress (s : SystemState)
    (h_exec : s.phase = .EXECUTING) :
    Enabled ExecuteChunk s ∨
    Enabled CompleteExecution s ∨
    Enabled ExecutionFailed s := by
  by_cases h_complete : s.continuation.isComplete
  · -- Complete: can do CompleteExecution
    right; left
    exact executing_complete_can_progress s h_exec h_complete
  · by_cases h_trapped : s.vmState.isTrappedHalt
    · -- Trapped: can do ExecutionFailed
      right; right
      exact executing_trapped_can_progress s h_exec h_trapped
    · -- Neither: can do ExecuteChunk
      left
      exact executing_incomplete_can_progress s h_exec h_complete h_trapped

/-! ### Terminal States -/

/-- In COMPLETE phase, no non-stuttering action is enabled.

Terminal phases are absorbing: the only valid transition is stuttering. -/
theorem complete_no_progress (s : SystemState)
    (h_complete : s.phase = .COMPLETE) :
    ¬Enabled StartExecution s ∧
    ¬Enabled ExecuteChunk s ∧
    ¬Enabled CompleteExecution s ∧
    ¬Enabled ExecutionFailed s := by
  constructor
  · intro ⟨s', h⟩
    have : s.phase = .INIT := h.1
    simp [h_complete] at this
  constructor
  · intro ⟨s', h⟩
    have : s.phase = .EXECUTING := h.1
    simp [h_complete] at this
  constructor
  · intro ⟨s', h⟩
    have : s.phase = .EXECUTING := h.1
    simp [h_complete] at this
  · intro ⟨s', h⟩
    have : s.phase = .EXECUTING := h.1
    simp [h_complete] at this

/-- In FAILED phase, no non-stuttering action is enabled. -/
theorem failed_no_progress (s : SystemState)
    (h_failed : s.phase = .FAILED) :
    ¬Enabled StartExecution s ∧
    ¬Enabled ExecuteChunk s ∧
    ¬Enabled CompleteExecution s ∧
    ¬Enabled ExecutionFailed s := by
  constructor
  · intro ⟨s', h⟩
    have : s.phase = .INIT := h.1
    simp [h_failed] at this
  constructor
  · intro ⟨s', h⟩
    have : s.phase = .EXECUTING := h.1
    simp [h_failed] at this
  constructor
  · intro ⟨s', h⟩
    have : s.phase = .EXECUTING := h.1
    simp [h_failed] at this
  · intro ⟨s', h⟩
    have : s.phase = .EXECUTING := h.1
    simp [h_failed] at this

/-- Terminal phases only allow stuttering. -/
theorem terminal_only_stutter (s s' : SystemState)
    (h_term : s.phase = .COMPLETE ∨ s.phase = .FAILED)
    (h_step : StepOrStutter s s') :
    s' = s := by
  cases h_step with
  | inl h_next =>
    -- Step requires non-terminal phase
    unfold Step at h_next
    cases h_next with
    | inl h_start =>
      have h_init : s.phase = .INIT := h_start.1
      cases h_term with
      | inl h => rw [h] at h_init; cases h_init
      | inr h => rw [h] at h_init; cases h_init
    | inr h_rest =>
      cases h_rest with
      | inl h_exec =>
        have h_exec_phase : s.phase = .EXECUTING := h_exec.1
        cases h_term with
        | inl h => rw [h] at h_exec_phase; cases h_exec_phase
        | inr h => rw [h] at h_exec_phase; cases h_exec_phase
      | inr h_rest2 =>
        cases h_rest2 with
        | inl h_complete =>
          have h_exec_phase : s.phase = .EXECUTING := h_complete.1
          cases h_term with
          | inl h => rw [h] at h_exec_phase; cases h_exec_phase
          | inr h => rw [h] at h_exec_phase; cases h_exec_phase
        | inr h_failed =>
          have h_exec_phase : s.phase = .EXECUTING := h_failed.1
          cases h_term with
          | inl h => rw [h] at h_exec_phase; cases h_exec_phase
          | inr h => rw [h] at h_exec_phase; cases h_exec_phase
  | inr h_stutter =>
    exact h_stutter

/-! ### Main No-Deadlock Theorem -/

/-- No-deadlock: In non-terminal states, at least one action is enabled.

This is the key progress property. Combined with terminal absorption,
it shows the system can always make progress until termination.

**TLA+ equivalent**: NonTerminal(s) => ENABLED Next -/
theorem no_deadlock (s : SystemState)
    (h_nonterm : s.phase = .INIT ∨ s.phase = .EXECUTING) :
    Enabled StartExecution s ∨
    Enabled ExecuteChunk s ∨
    Enabled CompleteExecution s ∨
    Enabled ExecutionFailed s := by
  cases h_nonterm with
  | inl h_init =>
    left
    exact init_can_progress s h_init
  | inr h_exec =>
    right
    exact executing_can_progress s h_exec

/-- Stronger form: non-terminal implies enabled Step. -/
theorem no_deadlock_step (s : SystemState)
    (h_nonterm : s.phase = .INIT ∨ s.phase = .EXECUTING) :
    ∃ s', Step s s' := by
  have h := no_deadlock s h_nonterm
  cases h with
  | inl h_start =>
    obtain ⟨s', h⟩ := h_start
    exact ⟨s', Or.inl h⟩
  | inr h_rest =>
    cases h_rest with
    | inl h_exec =>
      obtain ⟨s', h⟩ := h_exec
      exact ⟨s', Or.inr (Or.inl h)⟩
    | inr h_rest2 =>
      cases h_rest2 with
      | inl h_complete =>
        obtain ⟨s', h⟩ := h_complete
        exact ⟨s', Or.inr (Or.inr (Or.inl h))⟩
      | inr h_failed =>
        obtain ⟨s', h⟩ := h_failed
        exact ⟨s', Or.inr (Or.inr (Or.inr h))⟩

/-! ### Progress Classification -/

/-- Phase determines which actions are enabled. -/
theorem phase_determines_enabled (s : SystemState) :
    (s.phase = .INIT → Enabled StartExecution s) ∧
    (s.phase = .EXECUTING →
      Enabled ExecuteChunk s ∨
      Enabled CompleteExecution s ∨
      Enabled ExecutionFailed s) ∧
    (s.phase = .COMPLETE → ¬∃ s', Step s s') ∧
    (s.phase = .FAILED → ¬∃ s', Step s s') := by
  constructor
  · exact init_can_progress s
  constructor
  · exact executing_can_progress s
  constructor
  · intro h_complete ⟨s', h_step⟩
    have ⟨h1, h2, h3, h4⟩ := complete_no_progress s h_complete
    unfold Step at h_step
    cases h_step with
    | inl h => exact h1 ⟨s', h⟩
    | inr h =>
      cases h with
      | inl h => exact h2 ⟨s', h⟩
      | inr h =>
        cases h with
        | inl h => exact h3 ⟨s', h⟩
        | inr h => exact h4 ⟨s', h⟩
  · intro h_failed ⟨s', h_step⟩
    have ⟨h1, h2, h3, h4⟩ := failed_no_progress s h_failed
    unfold Step at h_step
    cases h_step with
    | inl h => exact h1 ⟨s', h⟩
    | inr h =>
      cases h with
      | inl h => exact h2 ⟨s', h⟩
      | inr h =>
        cases h with
        | inl h => exact h3 ⟨s', h⟩
        | inr h => exact h4 ⟨s', h⟩

/-! ### Trace Progress -/

/-- A valid trace from non-terminal state eventually has a non-stutter step
    (given no infinite stuttering). -/
theorem trace_eventually_progresses (tr : Liveness.Trace)
    (h_next : TraceNext tr)
    (h_nonterm : (tr 0).phase = .INIT ∨ (tr 0).phase = .EXECUTING)
    (h_no_inf_stutter : ∃ n, tr n ≠ tr (n + 1)) :
    ∃ n, Step (tr n) (tr (n + 1)) := by
  obtain ⟨n, h_diff⟩ := h_no_inf_stutter
  have h_step := h_next n
  cases h_step with
  | inl h_real_step =>
    exact ⟨n, h_real_step⟩
  | inr h_stutter =>
    exact absurd h_stutter.symm h_diff

end NearFall.Progress
