import NearFall.Trace

/-!
# Temporal Operators for Infinite Traces

LTL-style temporal operators over infinite traces for liveness proofs.

## Main Definitions

* `InfOften` - Predicate holds infinitely often (□◇P)
* `Always` - Predicate holds at all positions (□P)
* `Eventually` - Predicate holds at some position (◇P)
* `LeadsTo` - P at n implies Eventually Q at m ≥ n (P ~> Q)
* `Until` - P holds until Q becomes true (P U Q)

## Notation (informal)

* □P  ≡ Always P
* ◇P  ≡ Eventually P
* □◇P ≡ InfOften P
* P ~> Q ≡ LeadsTo P Q (under fairness)

## References

* infinitestate.md Phase 2.2
* Manna & Pnueli, "Temporal Logic of Reactive Systems"
* TLA+ Specifying Systems, Chapter 8
-/

namespace NearFall.Liveness

open TLATypes

/-! ### Infinitely Often -/

/-- Predicate P holds infinitely often in a sequence.

For any starting point n, there exists a later position m ≥ n
where P holds. This is the essence of "infinitely often" (□◇P).

**LTL equivalent**: □◇P -/
def InfOften (P : Nat → Prop) : Prop :=
  ∀ n, ∃ m, m ≥ n ∧ P m

/-- Alternative formulation: for all n, P holds somewhere at or after n. -/
def InfOften' (P : Nat → Prop) : Prop :=
  ∀ n, ∃ m, n ≤ m ∧ P m

theorem infOften_iff_infOften' (P : Nat → Prop) :
    InfOften P ↔ InfOften' P := by
  constructor <;> intro h n <;> exact h n

/-! ### Always (Box) -/

/-- Predicate P holds at all positions in the trace.

**LTL equivalent**: □P
**TLA+ equivalent**: `[]P` -/
def Always (P : SystemState → Prop) (tr : Trace) : Prop :=
  ∀ n, P (tr n)

/-- Always with explicit starting point. -/
def AlwaysFrom (P : SystemState → Prop) (tr : Trace) (start : Nat) : Prop :=
  ∀ n, n ≥ start → P (tr n)

/-- If P holds always, it holds from any starting point. -/
theorem always_implies_alwaysFrom (P : SystemState → Prop) (tr : Trace)
    (h : Always P tr) (start : Nat) : AlwaysFrom P tr start := by
  intro n _
  exact h n

/-! ### Eventually (Diamond) -/

/-- Predicate P holds at some position in the trace.

**LTL equivalent**: ◇P
**TLA+ equivalent**: `<>P` -/
def Eventually (P : SystemState → Prop) (tr : Trace) : Prop :=
  ∃ n, P (tr n)

/-- Eventually from a given starting position. -/
def EventuallyFrom (P : SystemState → Prop) (tr : Trace) (start : Nat) : Prop :=
  ∃ n, n ≥ start ∧ P (tr n)

/-- Eventually implies EventuallyFrom 0. -/
theorem eventually_iff_eventuallyFrom0 (P : SystemState → Prop) (tr : Trace) :
    Eventually P tr ↔ EventuallyFrom P tr 0 := by
  constructor
  · intro ⟨n, h⟩
    exact ⟨n, Nat.zero_le n, h⟩
  · intro ⟨n, _, h⟩
    exact ⟨n, h⟩

/-! ### Leads-To -/

/-- P leads to Q: whenever P holds, Q eventually holds at or after.

This is the fundamental liveness pattern: "every P is eventually
followed by Q". Under fairness assumptions, this is how we prove
progress properties.

**LTL equivalent**: □(P → ◇Q)
**TLA+ equivalent**: `P ~> Q` -/
def LeadsTo (P Q : SystemState → Prop) (tr : Trace) : Prop :=
  ∀ n, P (tr n) → ∃ m, m ≥ n ∧ Q (tr m)

/-- Reflexivity: P leads to P. -/
theorem leadsTo_refl (P : SystemState → Prop) (tr : Trace) :
    LeadsTo P P tr := by
  intro n hp
  exact ⟨n, Nat.le_refl n, hp⟩

/-- Transitivity: if P ~> Q and Q ~> R, then P ~> R. -/
theorem leadsTo_trans (P Q R : SystemState → Prop) (tr : Trace)
    (hpq : LeadsTo P Q tr) (hqr : LeadsTo Q R tr) :
    LeadsTo P R tr := by
  intro n hp
  obtain ⟨m, h_ge, hq⟩ := hpq n hp
  obtain ⟨k, h_ge', hr⟩ := hqr m hq
  exact ⟨k, Nat.le_trans h_ge h_ge', hr⟩

/-- Weakening: if P ~> Q and Q → R, then P ~> R. -/
theorem leadsTo_weaken_right (P Q R : SystemState → Prop) (tr : Trace)
    (hpq : LeadsTo P Q tr) (hqr : ∀ s, Q s → R s) :
    LeadsTo P R tr := by
  intro n hp
  obtain ⟨m, h_ge, hq⟩ := hpq n hp
  exact ⟨m, h_ge, hqr (tr m) hq⟩

/-- Strengthening: if P → Q and Q ~> R, then P ~> R. -/
theorem leadsTo_weaken_left (P Q R : SystemState → Prop) (tr : Trace)
    (hpq : ∀ s, P s → Q s) (hqr : LeadsTo Q R tr) :
    LeadsTo P R tr := by
  intro n hp
  exact hqr n (hpq (tr n) hp)

/-! ### Until -/

/-- P holds until Q: P holds continuously until Q becomes true.

Note: this is "weak until" - Q may never happen if P holds forever.

**LTL equivalent**: P W Q (weak until) -/
def WeakUntil (P Q : SystemState → Prop) (tr : Trace) (start : Nat) : Prop :=
  (∀ n, n ≥ start → P (tr n)) ∨
  (∃ m, m ≥ start ∧ Q (tr m) ∧ ∀ k, start ≤ k ∧ k < m → P (tr k))

/-- P holds until Q: P holds continuously until Q becomes true, and Q does happen.

**LTL equivalent**: P U Q (strong until) -/
def StrongUntil (P Q : SystemState → Prop) (tr : Trace) (start : Nat) : Prop :=
  ∃ m, m ≥ start ∧ Q (tr m) ∧ ∀ k, start ≤ k ∧ k < m → P (tr k)

/-! ### Duality Theorems -/

/-- Duality: □P ↔ ¬◇¬P -/
theorem always_eventually_duality (P : SystemState → Prop) (tr : Trace) :
    Always P tr ↔ ¬Eventually (fun s => ¬P s) tr := by
  constructor
  · intro h_always ⟨n, h_not_p⟩
    exact h_not_p (h_always n)
  · intro h_not_ev n
    exact Classical.byContradiction fun h_not_p =>
      h_not_ev ⟨n, h_not_p⟩

/-- Duality: ◇P ↔ ¬□¬P -/
theorem eventually_always_duality (P : SystemState → Prop) (tr : Trace) :
    Eventually P tr ↔ ¬Always (fun s => ¬P s) tr := by
  constructor
  · intro ⟨n, hp⟩ h_always
    exact h_always n hp
  · intro h_not_always
    exact Classical.byContradiction fun h_not_ev =>
      h_not_always fun n hp =>
        absurd ⟨n, hp⟩ h_not_ev

/-! ### Infinitely Often Properties -/

/-- If P holds infinitely often and P → Q, then Q holds infinitely often. -/
theorem infOften_mono {P Q : Nat → Prop} (h : InfOften P) (hpq : ∀ n, P n → Q n) :
    InfOften Q := by
  intro n
  obtain ⟨m, h_ge, hp⟩ := h n
  exact ⟨m, h_ge, hpq m hp⟩

/-- InfOften at trace positions. -/
def InfOftenAt (P : SystemState → Prop) (tr : Trace) : Prop :=
  InfOften (fun n => P (tr n))

/-- If P holds always, then P holds infinitely often. -/
theorem always_implies_infOften (P : SystemState → Prop) (tr : Trace)
    (h : Always P tr) : InfOftenAt P tr := by
  intro n
  exact ⟨n, Nat.le_refl n, h n⟩

/-! ### Combination Theorems -/

/-- LeadsTo + InfOften: if P ~> Q and P infinitely often, then Q infinitely often. -/
theorem leadsTo_infOften (P Q : SystemState → Prop) (tr : Trace)
    (h_leads : LeadsTo P Q tr) (h_inf_p : InfOftenAt P tr) :
    InfOftenAt Q tr := by
  intro n
  obtain ⟨m, h_ge, hp⟩ := h_inf_p n
  obtain ⟨k, h_ge', hq⟩ := h_leads m hp
  exact ⟨k, Nat.le_trans h_ge h_ge', hq⟩

/-- Eventually + Always: if ◇□P then ∃n. AlwaysFrom P n. -/
def EventuallyAlways (P : SystemState → Prop) (tr : Trace) : Prop :=
  ∃ n, AlwaysFrom P tr n

/-- Always + Eventually: □◇P is InfOftenAt. -/
theorem alwaysEventually_iff_infOften (P : SystemState → Prop) (tr : Trace) :
    (∀ n, EventuallyFrom P tr n) ↔ InfOftenAt P tr := by
  constructor
  · intro h n
    obtain ⟨m, h_ge, hp⟩ := h n
    exact ⟨m, h_ge, hp⟩
  · intro h n
    obtain ⟨m, h_ge, hp⟩ := h n
    exact ⟨m, h_ge, hp⟩

end NearFall.Liveness
