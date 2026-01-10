import NearFall.VMState
import NearFall.Continuations

/-!
# Infinite Traces for Liveness Verification

Infinite trace semantics matching TLA+ `[Next]_vars` for liveness proofs.

## Main Definitions

* `InfiniteTrace` - Infinite sequence of states (Nat → SystemState)
* `Step` - Explicit Next relation (no stutter)
* `StepOrStutter` - Matches TLA+ `[Next]_vars` exactly
* `TraceInit` - Trace satisfies Init at position 0
* `TraceNext` - Trace satisfies `[Next]_vars` between consecutive positions

## Design Rationale

Liveness properties require **infinite traces** (not `List`):
- `◇P` (eventually P) requires unbounded search
- `□P` (always P) requires checking all future positions
- `P ~> Q` (leads-to) requires unbounded eventual response

This matches TLA+ semantics exactly:
- `StepOrStutter` corresponds to `[Next]_vars`
- Infinite traces correspond to behaviors

## References

* infinitestate.md Phase 2.1
* TLA+ Specifying Systems, Chapter 8 (Temporal Logic)
-/

namespace NearFall.Liveness

open TLATypes VMState Continuations

/-! ### System Phase -/

/-- System execution phases matching TLA+ SystemPhase. -/
inductive SystemPhase where
  | INIT      : SystemPhase  -- Initial state
  | EXECUTING : SystemPhase  -- Executing chunks
  | COMPLETE  : SystemPhase  -- Successful completion
  | FAILED    : SystemPhase  -- Execution failed (trap)
  deriving Repr, DecidableEq, BEq, Inhabited

/-! ### Continuation State -/

/-- Continuation state for chunk tracking. -/
structure ContinuationState where
  /-- List of executed chunks. -/
  chunks : List ChunkRecord
  /-- Current chunk index. -/
  currentChunk : Nat
  /-- Whether execution is complete. -/
  isComplete : Bool
  deriving DecidableEq

instance : Inhabited ContinuationState where
  default := { chunks := [], currentChunk := 0, isComplete := false }

/-! ### System State -/

/-- Complete system state for liveness verification.

This is a simplified version focusing on fields needed for liveness proofs.
Full system state is in JoltSpec.tla. -/
structure SystemState where
  /-- Current execution phase. -/
  phase : SystemPhase
  /-- VM state. -/
  vmState : VMStateV1
  /-- Continuation tracking. -/
  continuation : ContinuationState
  /-- Program hash (binds execution to program). -/
  programHash : Bytes32
  deriving DecidableEq

instance : Inhabited SystemState where
  default := {
    phase := .INIT
    vmState := default
    continuation := default
    programHash := Bytes32.zero
  }

/-! ### Infinite Traces -/

/-- Infinite trace: sequence of states indexed by natural numbers.

This is the fundamental type for liveness proofs. Unlike `List`,
an infinite trace can express properties like "eventually" and "always"
that require examining unbounded future positions.

**TLA+ equivalent**: A behavior is a function from Nat to states. -/
def InfiniteTrace := Nat → SystemState

/-- Type alias for readability in liveness theorems. -/
abbrev Trace := InfiniteTrace

/-! ### State Transitions -/

/-- Predicate: system is in initial state. -/
def Init (s : SystemState) : Prop :=
  s.phase = .INIT ∧
  s.continuation.chunks = [] ∧
  s.continuation.currentChunk = 0

/-- Predicate: StartExecution transition (INIT → EXECUTING). -/
def StartExecution (s s' : SystemState) : Prop :=
  s.phase = .INIT ∧
  s'.phase = .EXECUTING ∧
  s'.vmState = s.vmState ∧
  s'.continuation = s.continuation ∧
  s'.programHash = s.programHash

/-- Predicate: ExecuteChunk transition (add one chunk). -/
def ExecuteChunk (s s' : SystemState) : Prop :=
  s.phase = .EXECUTING ∧
  ¬s.continuation.isComplete ∧
  s'.phase = .EXECUTING ∧
  s'.continuation.currentChunk = s.continuation.currentChunk + 1 ∧
  s'.programHash = s.programHash

/-- Predicate: CompleteExecution transition (EXECUTING → COMPLETE). -/
def CompleteExecution (s s' : SystemState) : Prop :=
  s.phase = .EXECUTING ∧
  s.continuation.isComplete ∧
  s'.phase = .COMPLETE ∧
  s'.programHash = s.programHash

/-- Predicate: ExecutionFailed transition (EXECUTING → FAILED). -/
def ExecutionFailed (s s' : SystemState) : Prop :=
  s.phase = .EXECUTING ∧
  s.vmState.isTrappedHalt ∧
  s'.phase = .FAILED ∧
  s'.programHash = s.programHash

/-- Explicit Next relation: one of the four transitions.

This is the "action" part of `[Next]_vars` - a real state change. -/
def Step (s s' : SystemState) : Prop :=
  StartExecution s s' ∨
  ExecuteChunk s s' ∨
  CompleteExecution s s' ∨
  ExecutionFailed s s'

/-- Alias for Step (matches naming in some contexts). -/
abbrev Next := Step

/-! ### Step or Stutter -/

/-- Step or stutter: matches TLA+ `[Next]_vars` exactly.

In TLA+, `[Next]_vars` means "either Next happens, or all variables
are unchanged (stuttering)". This is essential for refinement and
composition of specifications.

**TLA+ equivalent**: `[Next]_vars ≡ Next ∨ (vars' = vars)` -/
def StepOrStutter (s s' : SystemState) : Prop :=
  Step s s' ∨ s' = s

/-! ### Trace Predicates -/

/-- Trace satisfies Init at position 0.

**TLA+ equivalent**: `Init` holds in the initial state of a behavior. -/
def TraceInit (tr : Trace) : Prop :=
  Init (tr 0)

/-- Trace satisfies `[Next]_vars` between all consecutive positions.

This ensures the trace is a valid behavior of the specification.

**TLA+ equivalent**: `□[Next]_vars` -/
def TraceNext (tr : Trace) : Prop :=
  ∀ n, StepOrStutter (tr n) (tr (n + 1))

/-- A trace is a valid behavior if it satisfies Init and Next.

**TLA+ equivalent**: `Spec ≡ Init ∧ □[Next]_vars` -/
def ValidTrace (tr : Trace) : Prop :=
  TraceInit tr ∧ TraceNext tr

/-! ### Terminal State Predicates -/

/-- State is in a terminal phase (COMPLETE or FAILED). -/
def IsTerminal (s : SystemState) : Prop :=
  s.phase = .COMPLETE ∨ s.phase = .FAILED

/-- State is not in a terminal phase. -/
def IsNonTerminal (s : SystemState) : Prop :=
  s.phase = .INIT ∨ s.phase = .EXECUTING

/-! ### Basic Trace Lemmas -/

/-- Stuttering is a valid StepOrStutter. -/
theorem stutter_valid (s : SystemState) : StepOrStutter s s := by
  right; rfl

/-- Step implies StepOrStutter. -/
theorem step_implies_stepOrStutter (s s' : SystemState) (h : Step s s') :
    StepOrStutter s s' := by
  left; exact h

/-- Terminal phases are absorbing (only stuttering allowed). -/
theorem terminal_absorbing (s s' : SystemState)
    (h_term : IsTerminal s) (h_step : StepOrStutter s s') :
    s' = s ∨ IsTerminal s' := by
  cases h_step with
  | inl h_next =>
    -- If a real step happened, analyze which transition
    cases h_next with
    | inl h_start =>
      -- StartExecution requires INIT phase, but we're in terminal
      have h_init : s.phase = .INIT := h_start.1
      cases h_term with
      | inl hc => rw [hc] at h_init; cases h_init
      | inr hf => rw [hf] at h_init; cases h_init
    | inr h_rest =>
      cases h_rest with
      | inl h_exec =>
        -- ExecuteChunk requires EXECUTING phase
        have h_exec_phase : s.phase = .EXECUTING := h_exec.1
        cases h_term with
        | inl hc => rw [hc] at h_exec_phase; cases h_exec_phase
        | inr hf => rw [hf] at h_exec_phase; cases h_exec_phase
      | inr h_rest2 =>
        cases h_rest2 with
        | inl h_complete =>
          -- CompleteExecution results in COMPLETE (terminal)
          right; left; exact h_complete.2.2.1
        | inr h_failed =>
          -- ExecutionFailed results in FAILED (terminal)
          right; right; exact h_failed.2.2.1
  | inr h_stutter =>
    left; exact h_stutter

/-- Once terminal, always terminal in a valid trace. -/
theorem terminal_forever (tr : Trace) (h_next : TraceNext tr)
    (n : Nat) (h_term : IsTerminal (tr n)) :
    ∀ m, m ≥ n → IsTerminal (tr m) := by
  intro m h_ge
  induction m with
  | zero =>
    have : n = 0 := Nat.le_zero.mp h_ge
    rw [this] at h_term
    exact h_term
  | succ k ih =>
    by_cases h : k ≥ n
    · have h_k_term : IsTerminal (tr k) := ih h
      have h_step : StepOrStutter (tr k) (tr (k + 1)) := h_next k
      cases terminal_absorbing (tr k) (tr (k + 1)) h_k_term h_step with
      | inl h_eq => simp only [h_eq]; exact h_k_term
      | inr h_term' => exact h_term'
    · -- k < n, so k + 1 ≤ n ≤ k + 1 means k + 1 = n and h_ge implies m ≥ n
      have : n = k + 1 := by omega
      rw [this] at h_term
      exact h_term

end NearFall.Liveness
