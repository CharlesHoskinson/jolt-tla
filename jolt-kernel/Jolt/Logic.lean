/-!
# Jolt Kernel Logic Discipline

Pattern for all modules:
- `Spec : a -> Prop` - Specification predicate
- `check : a -> Bool` - Executable checker
- `check_sound : check x = true -> Spec x` - Soundness theorem

## Main Definitions

* `CheckSpec` - Typeclass for checkable specifications
* `decide_sound` - Standard soundness proof pattern
* `checkAll` - Combine multiple boolean checks

## Implementation Notes

Uses standard Lean 4 library. Key lemmas:
- `Bool.eq_true_iff` : (b = true) <-> b
- `decide_eq_true_eq` : (decide p = true) = p
- `Bool.and_eq_true` : (a && b = true) <-> (a = true /\ b = true)

-/

namespace Jolt

/-! ### Core Soundness Pattern -/

/-- Standard soundness proof when check = decide Spec.

Given a decidable proposition p, if `decide p = true`, then p holds.
This is the foundation of all checker soundness proofs. -/
theorem decide_sound {p : Prop} [Decidable p] (h : decide p = true) : p := by
  simp only [decide_eq_true_eq] at h
  exact h

/-- Boolean conjunction soundness.

If `a && b = true`, then both `a = true` and `b = true`. -/
theorem and_sound {a b : Bool} (h : a && b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

/-- Boolean disjunction soundness (left).

If `a || b = true` and `a = true`, we get the left case. -/
theorem or_sound_left {a b : Bool} (_h : a || b = true) (ha : a = true) : a = true := ha

/-! ### Checkable Specification Pattern -/

/-- Typeclass for specifications with executable checkers.

Every specification should have:
1. A Prop predicate (the specification)
2. A Bool function (the checker)
3. A soundness theorem (checker true implies spec) -/
class CheckSpec (α : Type _) where
  /-- The specification predicate. -/
  Spec : α → Prop
  /-- The executable checker. -/
  check : α → Bool
  /-- Soundness: if checker passes, spec holds. -/
  sound : ∀ x, check x = true → Spec x

/-- Combine multiple boolean checks. -/
def checkAll (checks : List Bool) : Bool := checks.all id

/-- Soundness of checkAll: all checks must pass. -/
theorem checkAll_sound (checks : List Bool) (h : checkAll checks = true) :
    ∀ b ∈ checks, b = true := by
  simp only [checkAll, List.all_eq_true, id_eq] at h
  exact h

/-! ### Helper Lemmas for Proofs -/

/-- If check equals decide of spec, soundness is automatic. -/
theorem check_decide_sound {α : Type _} (spec : α → Prop) (check : α → Bool)
    [∀ x, Decidable (spec x)]
    (h_eq : ∀ x, check x = decide (spec x)) (x : α) (h : check x = true) :
    spec x := by
  rw [h_eq] at h
  exact decide_sound h

/-- Chained conjunction soundness for 3 conditions. -/
theorem and3_sound {a b c : Bool} (h : a && b && c = true) :
    a = true ∧ b = true ∧ c = true := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Chained conjunction soundness for 4 conditions. -/
theorem and4_sound {a b c d : Bool} (h : a && b && c && d = true) :
    a = true ∧ b = true ∧ c = true ∧ d = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-! ### Negation Helpers -/

/-- If `!b = true`, then `b = false`. -/
theorem not_true_eq_false {b : Bool} (h : !b = true) : b = false := by
  cases b <;> simp at h ⊢

/-- If `b = false`, then `!b = true`. -/
theorem false_eq_not_true {b : Bool} (h : b = false) : !b = true := by
  rw [h]; rfl

/-! ### BEq to Eq Conversion -/

/-- If `a == b = true` for a type with LawfulBEq, then `a = b`. -/
theorem beq_to_eq {α : Type _} [BEq α] [LawfulBEq α] {a b : α} (h : (a == b) = true) : a = b := by
  exact eq_of_beq h

/-- If `a = b`, then `a == b = true` for any BEq type. -/
theorem eq_to_beq {α : Type _} [BEq α] [LawfulBEq α] {a b : α} (h : a = b) : (a == b) = true := by
  rw [h]; exact beq_self_eq_true b

end Jolt
