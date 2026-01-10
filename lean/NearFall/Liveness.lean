import NearFall.Trace
import NearFall.Temporal
import NearFall.Fairness
import NearFall.Variant

/-!
# Liveness Theorems under Fairness

Main liveness theorems proving progress and termination properties
under weak fairness assumptions.

## Main Theorems

* `progress_from_init` - INIT phase eventually transitions
* `progress_from_executing` - EXECUTING phase makes progress
* `eventually_terminal` - System eventually reaches terminal phase

## Proof Strategy

All liveness theorems follow the standard pattern:

1. **Variant decrease**: Progress actions strictly decrease the variant
2. **Variant bounded**: Variant is a natural number (well-founded)
3. **Weak fairness**: Progress actions are eventually taken if continuously enabled
4. **No deadlock**: At least one progress action is enabled in non-terminal states

Combined, these guarantee termination.

## References

* infinitestate.md Phase 2.5
* TLA+ LivenessProofs.tla (WF/ENABLED patterns)
-/

namespace NearFall.Liveness

open TLATypes VMState Continuations

/-! ### Fair Specification -/

/-- Fair Jolt specification: Init ∧ □[Next]_vars ∧ WF(StartExecution) ∧ WF(ExecuteChunk). -/
structure JoltFairSpec (tr : Trace) : Prop where
  /-- Trace satisfies Init at position 0. -/
  init : TraceInit tr
  /-- Trace satisfies [Next]_vars between consecutive positions. -/
  next : TraceNext tr
  /-- Weak fairness on StartExecution. -/
  fair_start : WeakFair StartExecution tr
  /-- Weak fairness on ExecuteChunk. -/
  fair_chunk : WeakFair ExecuteChunk tr

/-! ### Enabledness Lemmas -/

/-- StartExecution is enabled in INIT phase. -/
theorem startExecution_enabled (s : SystemState)
    (h_init : s.phase = .INIT) :
    Enabled StartExecution s := by
  unfold Enabled StartExecution
  -- Construct a successor state that satisfies StartExecution
  let s' : SystemState := {
    phase := .EXECUTING
    vmState := s.vmState
    continuation := s.continuation
    programHash := s.programHash
  }
  exact ⟨s', h_init, rfl, rfl, rfl, rfl⟩

/-- ExecuteChunk is enabled in EXECUTING phase when not complete. -/
theorem executeChunk_enabled (s : SystemState)
    (h_exec : s.phase = .EXECUTING)
    (h_not_complete : ¬s.continuation.isComplete) :
    Enabled ExecuteChunk s := by
  unfold Enabled ExecuteChunk
  sorry  -- Red Team target: construct successor state

/-- At least one progress action is enabled in non-terminal states. -/
theorem nonterminal_progress_enabled (s : SystemState)
    (h_nonterm : s.phase = .INIT ∨ s.phase = .EXECUTING) :
    (Enabled StartExecution s) ∨
    (Enabled ExecuteChunk s) ∨
    (Enabled CompleteExecution s) ∨
    (Enabled ExecutionFailed s) := by
  cases h_nonterm with
  | inl h_init =>
    left
    exact startExecution_enabled s h_init
  | inr h_exec =>
    sorry  -- Red Team target: case split on isComplete and halted

/-! ### Leads-To from INIT -/

/-- LIVE_ProgressFromInit: under WF(StartExecution), leaves INIT phase.

If the system starts in INIT and StartExecution is weakly fair,
then eventually the system is not in INIT.

**Proof sketch**:
1. In INIT, StartExecution is enabled (startExecution_enabled)
2. WF(StartExecution) ensures it's eventually taken
3. StartExecution transitions to EXECUTING
4. Therefore, eventually phase ≠ INIT -/
theorem progress_from_init (tr : Trace)
    (h_spec : JoltFairSpec tr) :
    LeadsTo (fun s => s.phase = .INIT) (fun s => s.phase ≠ .INIT) tr := by
  intro n h_init
  -- StartExecution is enabled at position n
  have h_enabled : EnabledAt StartExecution tr n := by
    unfold EnabledAt
    exact startExecution_enabled (tr n) h_init
  -- By weak fairness, StartExecution eventually occurs
  -- We need to show it's continuously enabled until taken
  sorry  -- Red Team target

/-- Alternative formulation using Eventually. -/
theorem eventually_not_init (tr : Trace)
    (h_spec : JoltFairSpec tr)
    (h_start_init : (tr 0).phase = .INIT) :
    Eventually (fun s => s.phase ≠ .INIT) tr := by
  have h_leads := progress_from_init tr h_spec
  have h_at_0 : (fun s => s.phase = .INIT) (tr 0) := h_start_init
  obtain ⟨m, _, h_not_init⟩ := h_leads 0 h_at_0
  exact ⟨m, h_not_init⟩

/-! ### Leads-To from EXECUTING -/

/-- LIVE_ProgressFromExecuting: under WF(ExecuteChunk), makes progress.

In EXECUTING phase, either:
1. Continuation is complete → can transition to COMPLETE
2. VM is halted with trap → can transition to FAILED
3. Otherwise → ExecuteChunk is enabled -/
theorem progress_from_executing (tr : Trace)
    (h_spec : JoltFairSpec tr) :
    LeadsTo (fun s => s.phase = .EXECUTING ∧ ¬s.continuation.isComplete)
            (fun s => s.phase ≠ .EXECUTING ∨ s.continuation.isComplete) tr := by
  intro n ⟨h_exec, h_not_complete⟩
  -- ExecuteChunk is enabled
  have h_enabled : EnabledAt ExecuteChunk tr n := by
    unfold EnabledAt
    exact executeChunk_enabled (tr n) h_exec h_not_complete
  -- By weak fairness, ExecuteChunk eventually occurs
  sorry  -- Red Team target

/-! ### Leads-To Terminal -/

/-- LIVE_EventuallyTerminal: under WF + resource bounds, reaches terminal phase.

This is the main termination theorem. Under weak fairness on both
StartExecution and ExecuteChunk, and bounded chunks, the system
eventually reaches COMPLETE or FAILED.

**Proof sketch**:
1. Variant is bounded (Nat, so well-founded)
2. Progress steps strictly decrease variant
3. Non-progress steps don't increase variant
4. Weak fairness ensures progress steps are taken when enabled
5. At least one progress action is enabled in non-terminal states
6. Therefore, terminal state is eventually reached -/
theorem eventually_terminal (tr : Trace)
    (h_spec : JoltFairSpec tr)
    (h_bounded : ∀ n, CommittedChunks (tr n) ≤ MAX_CHUNKS) :
    Eventually (fun s => s.phase = .COMPLETE ∨ s.phase = .FAILED) tr := by
  -- Use well-founded induction on variant
  sorry  -- Red Team target: main termination proof

/-- Leads-to formulation of termination. -/
theorem leads_to_terminal (tr : Trace)
    (h_spec : JoltFairSpec tr)
    (h_bounded : ∀ n, CommittedChunks (tr n) ≤ MAX_CHUNKS) :
    LeadsTo (fun s => s.phase = .INIT ∨ s.phase = .EXECUTING)
            (fun s => s.phase = .COMPLETE ∨ s.phase = .FAILED) tr := by
  intro n h_nonterm
  -- Need to convert Eventually to LeadsTo form
  -- Eventually gives ∃ m, P(m), LeadsTo needs ∃ m, m ≥ n ∧ P(m)
  sorry  -- Red Team target: convert Eventually to LeadsTo

/-! ### Terminal Absorption -/

/-- Once terminal, always terminal (from Trace.lean). -/
theorem terminal_stable (tr : Trace)
    (h_next : TraceNext tr)
    (n : Nat)
    (h_term : (tr n).phase = .COMPLETE ∨ (tr n).phase = .FAILED) :
    ∀ m, m ≥ n → (tr m).phase = .COMPLETE ∨ (tr m).phase = .FAILED := by
  have h_term' : IsTerminal (tr n) := h_term
  intro m h_ge
  exact terminal_forever tr h_next n h_term' m h_ge

/-! ### Combined Liveness -/

/-- Complete liveness specification: Init leads to Terminal. -/
theorem complete_liveness (tr : Trace)
    (h_spec : JoltFairSpec tr)
    (h_bounded : ∀ n, CommittedChunks (tr n) ≤ MAX_CHUNKS) :
    LeadsTo (fun s => s.phase = .INIT)
            (fun s => s.phase = .COMPLETE ∨ s.phase = .FAILED) tr := by
  -- Compose: INIT ~> EXECUTING and EXECUTING ~> Terminal
  intro n h_init
  -- First, leave INIT
  have h_not_init := progress_from_init tr h_spec
  obtain ⟨m1, h_ge1, h_not_init'⟩ := h_not_init n h_init
  -- Then, reach terminal
  have h_term := leads_to_terminal tr h_spec h_bounded
  -- Need to show we're in INIT or EXECUTING at m1
  sorry  -- Red Team target

/-! ### Variant-Based Termination -/

/-- Well-founded termination via variant.

The variant strictly decreases on progress steps and is bounded below by 0.
Since Nat is well-founded, termination is guaranteed. -/
theorem wf_termination (tr : Trace)
    (h_spec : JoltFairSpec tr)
    (h_inv : ∀ n, VariantTypeOK (tr n))
    (h_bounded : ∀ n, CommittedChunks (tr n) < MAX_CHUNKS ∨
                      (tr n).phase = .COMPLETE ∨ (tr n).phase = .FAILED) :
    ∃ n, (tr n).phase = .COMPLETE ∨ (tr n).phase = .FAILED := by
  -- Use well-founded induction on the variant at each step
  -- The variant is in Nat, which is well-founded
  -- Progress steps decrease it, non-progress steps don't increase it
  -- Weak fairness ensures infinitely many progress steps
  -- Therefore, variant eventually reaches 0, which means terminal state
  sorry  -- Red Team target

/-! ### Progress Measure -/

/-- The variant never increases along the trace. -/
theorem variant_monotone (tr : Trace)
    (h_next : TraceNext tr) :
    ∀ n, variant (tr (n + 1)) ≤ variant (tr n) := by
  intro n
  have h_step := h_next n
  have h_class := stepOrStutter_classification (tr n) (tr (n + 1)) h_step
  cases h_class with
  | inl h_prog =>
    -- Progress step: variant decreases (so certainly ≤)
    sorry  -- Red Team target: use variant_decreases
  | inr h_nonprog =>
    -- Non-progress step: variant doesn't increase
    exact variant_nonIncrease (tr n) (tr (n + 1)) h_nonprog

/-- If variant is positive, a progress step can occur. -/
theorem positive_variant_progress (s : SystemState)
    (h_pos : variant s > 0)
    (h_inv : VariantTypeOK s) :
    (Enabled StartExecution s) ∨
    (Enabled ExecuteChunk s) ∨
    (Enabled CompleteExecution s) ∨
    (Enabled ExecutionFailed s) := by
  -- Variant > 0 implies non-terminal phase
  have h_nonterm : s.phase = .INIT ∨ s.phase = .EXECUTING := by
    unfold variant at h_pos
    cases h_s : s.phase <;> simp [h_s] at h_pos
    · left; rfl
    · right; rfl
  exact nonterminal_progress_enabled s h_nonterm

end NearFall.Liveness
