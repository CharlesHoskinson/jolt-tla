/-
  Test: Verify Goedel-Prover's Fr proof compiles
-/

-- BLS12-381 scalar field (standalone for test)
namespace GoedelTest

def modulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

structure Fr where
  val : Nat
  isLt : val < modulus

def Fr.ofNat (n : Nat) : Fr :=
  { val := n % modulus, isLt := Nat.mod_lt n (by native_decide) }

-- Goedel's proof (simplified/cleaned version)
theorem Fr.add_zero_right (a : Fr) : Fr.ofNat (a.val + 0) = a := by
  have h₁ : a.val + 0 = a.val := by simp
  have h₃ : a.val % modulus = a.val := by
    apply Nat.mod_eq_of_lt
    exact a.isLt
  simp only [h₁, Fr.ofNat]
  cases a with
  | mk v hv =>
    simp only [h₃]

end GoedelTest
