import NearFall.Trace
import NearFall.Temporal

/-!
# Fairness Definitions for Liveness Proofs

Weak and strong fairness definitions over infinite traces.

## Main Definitions

* `Enabled` - Action A is enabled at state s (∃ s', A s s')
* `EnabledAt` - Action enabled at trace position n
* `OccursAt` - Action occurs between positions n and n+1
* `WeakFair` - Continuously enabled → infinitely often taken (WF)
* `StrongFair` - Infinitely often enabled → infinitely often taken (SF)

## Design Notes

**CRITICAL**: These are CORRECTED definitions matching TLA+ semantics exactly.

TLA+ weak fairness `WF_vars(A)`:
  `□◇¬Enabled(<<A>>_vars) ∨ □◇<<A>>_vars`

Equivalently: if A is continuously enabled from some point,
then A is taken infinitely often.

TLA+ strong fairness `SF_vars(A)`:
  `□◇Enabled(<<A>>_vars) → □◇<<A>>_vars`

Equivalently: if A is enabled infinitely often,
then A is taken infinitely often.

## References

* infinitestate.md Phase 2.3
* TLA+ Specifying Systems, Chapter 8.4
* Manna & Pnueli, "Temporal Logic of Reactive Systems"
-/

namespace NearFall.Liveness

open TLATypes

/-! ### Enabledness -/

/-- Action A is enabled at state s.

An action is enabled if there exists some successor state
that the action can transition to.

**TLA+ equivalent**: `ENABLED <<A>>_vars` -/
def Enabled (A : SystemState → SystemState → Prop) (s : SystemState) : Prop :=
  ∃ s', A s s'

/-- Action A is enabled at trace position n. -/
def EnabledAt (A : SystemState → SystemState → Prop) (tr : Trace) (n : Nat) : Prop :=
  Enabled A (tr n)

/-! ### Action Occurrence -/

/-- Action A occurs between positions n and n+1.

This captures the "stutter-sensitive" occurrence - the action
actually happens as a step in the trace.

**TLA+ equivalent**: `<<A>>_vars` holds at step n -/
def OccursAt (A : SystemState → SystemState → Prop) (tr : Trace) (n : Nat) : Prop :=
  A (tr n) (tr (n + 1))

/-! ### Weak Fairness -/

/-- Weak fairness: continuously enabled from some point → infinitely often taken.

TLA+ `WF_vars(A)` states: if action A is continuously enabled
from some point onward (no gaps in enabledness), then A must be
taken infinitely often.

**TLA+ equivalent**: `WF_vars(A) ≡ □◇¬Enabled(<<A>>_vars) ∨ □◇<<A>>_vars`

**Usable form**: `(∃n. ∀m≥n. Enabled A (tr m)) → □◇(A occurs)` -/
def WeakFair (A : SystemState → SystemState → Prop) (tr : Trace) : Prop :=
  (∃ n, ∀ m, m ≥ n → EnabledAt A tr m) → InfOften (fun k => OccursAt A tr k)

/-- Alternative formulation using InfOftenAt. -/
def WeakFair' (A : SystemState → SystemState → Prop) (tr : Trace) : Prop :=
  (∃ n, ∀ m, m ≥ n → EnabledAt A tr m) →
  ∀ k, ∃ j, j ≥ k ∧ OccursAt A tr j

theorem weakFair_iff_weakFair' (A : SystemState → SystemState → Prop) (tr : Trace) :
    WeakFair A tr ↔ WeakFair' A tr := by
  constructor <;> intro h <;> exact h

/-! ### Strong Fairness -/

/-- Strong fairness: infinitely often enabled → infinitely often taken.

TLA+ `SF_vars(A)` states: if action A is enabled infinitely often
(possibly with gaps), then A must be taken infinitely often.

Strong fairness is stronger than weak fairness: it only requires
*repeated* enabledness, not *continuous* enabledness.

**TLA+ equivalent**: `SF_vars(A) ≡ □◇Enabled(<<A>>_vars) → □◇<<A>>_vars` -/
def StrongFair (A : SystemState → SystemState → Prop) (tr : Trace) : Prop :=
  InfOften (fun n => EnabledAt A tr n) → InfOften (fun k => OccursAt A tr k)

/-! ### Fairness Relationships -/

/-- Strong fairness implies weak fairness.

If infinitely often enabled → taken (SF), then
continuously enabled → taken (WF), since continuous
enabledness is a special case of infinitely often enabled. -/
theorem strongFair_implies_weakFair (A : SystemState → SystemState → Prop) (tr : Trace)
    (h_sf : StrongFair A tr) : WeakFair A tr := by
  intro ⟨n, h_cont⟩
  apply h_sf
  intro k
  by_cases h : k ≥ n
  · exact ⟨k, Nat.le_refl k, h_cont k h⟩
  · have h' : k < n := Nat.lt_of_not_ge h
    exact ⟨n, Nat.le_of_lt h', h_cont n (Nat.le_refl n)⟩

/-! ### Usable Forms -/

/-- WeakFair usable form: derive once, reuse to prevent repetitive proof plumbing.

Given weak fairness on A, if A is continuously enabled from n,
then for any position k, there exists j ≥ k where A occurs. -/
theorem weakFair_usable (A : SystemState → SystemState → Prop) (tr : Trace)
    (h_wf : WeakFair A tr) :
    ∀ n, (∀ m, m ≥ n → EnabledAt A tr m) → ∀ k, ∃ j, j ≥ k ∧ OccursAt A tr j := by
  intro n h_enabled k
  have h_cont : ∃ n, ∀ m, m ≥ n → EnabledAt A tr m := ⟨n, h_enabled⟩
  exact (h_wf h_cont) k

/-- StrongFair usable form. -/
theorem strongFair_usable (A : SystemState → SystemState → Prop) (tr : Trace)
    (h_sf : StrongFair A tr) :
    (∀ n, ∃ m, m ≥ n ∧ EnabledAt A tr m) → ∀ k, ∃ j, j ≥ k ∧ OccursAt A tr j := by
  intro h_inf_enabled k
  exact h_sf h_inf_enabled k

/-! ### Fairness Composition -/

/-- Fair specification: Init ∧ □[Next]_vars with fairness constraints.

A fair specification includes:
1. Initial condition
2. Next-state relation (with stuttering)
3. Fairness constraints on relevant actions -/
structure FairSpec (tr : Trace) where
  /-- Trace satisfies Init at position 0. -/
  init : TraceInit tr
  /-- Trace satisfies [Next]_vars between consecutive positions. -/
  next : TraceNext tr
  /-- Collection of fairness constraints. -/
  fair : List (Trace → Prop)
  /-- All fairness constraints hold. -/
  fair_holds : ∀ f, f ∈ fair → f tr

/-! ### Enabled Stability Lemmas -/

/-- If action A is enabled at state s and the only way to disable it
is by taking A, then after any step, either A was taken or A is still enabled.

This is a common pattern for proving leads-to under weak fairness. -/
theorem enabled_stability
    (A : SystemState → SystemState → Prop)
    (s s' : SystemState)
    (h_enabled : Enabled A s)
    (h_step : StepOrStutter s s')
    (h_only_A_disables : ∀ B, B s s' → B ≠ A → Enabled A s') :
    A s s' ∨ Enabled A s' := by
  cases h_step with
  | inl h_next =>
    by_cases h_is_A : Step s s' = A s s'
    · left
      sorry -- Red Team target: extract A from Step
    · right
      sorry -- Red Team target: apply h_only_A_disables
  | inr h_stutter =>
    right
    rw [h_stutter]
    exact h_enabled

/-! ### Terminal State Fairness -/

/-- In terminal states, no action is enabled (except stuttering).

This ensures liveness proofs correctly handle absorption. -/
theorem terminal_not_enabled (A : SystemState → SystemState → Prop)
    (s : SystemState)
    (h_terminal : IsTerminal s)
    (h_A_requires_nonterminal : ∀ s', A s s' → ¬IsTerminal s) :
    ¬Enabled A s := by
  intro ⟨s', h_A⟩
  exact h_A_requires_nonterminal s' h_A h_terminal

end NearFall.Liveness
