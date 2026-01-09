/-
  Test: Goedel-Prover's Fr field property proofs
-/

namespace GoedelFrProps

def modulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

structure Fr where
  val : Nat
  isLt : val < modulus

def Fr.ofNat (n : Nat) : Fr :=
  { val := n % modulus, isLt := Nat.mod_lt n (by native_decide) }

def Fr.zero : Fr := { val := 0, isLt := by native_decide }
def Fr.one : Fr := { val := 1, isLt := by native_decide }
def Fr.add (a b : Fr) : Fr := Fr.ofNat (a.val + b.val)
def Fr.mul (a b : Fr) : Fr := Fr.ofNat (a.val * b.val)

-- Test 1: add_comm (cleaned from Goedel's output)
theorem Fr.add_comm (a b : Fr) : Fr.add a b = Fr.add b a := by
  have h₁ : a.val + b.val = b.val + a.val := Nat.add_comm a.val b.val
  simp only [Fr.add, Fr.ofNat, h₁]

-- Test 2: add_zero (cleaned from Goedel's output)
theorem Fr.add_zero (a : Fr) : Fr.add a Fr.zero = a := by
  have h₃ : a.val % modulus = a.val := Nat.mod_eq_of_lt a.isLt
  simp only [Fr.add, Fr.ofNat, Fr.zero, Nat.add_zero, h₃]

-- Test 3: mul_comm (cleaned from Goedel's output)
theorem Fr.mul_comm (a b : Fr) : Fr.mul a b = Fr.mul b a := by
  have h₁ : a.val * b.val = b.val * a.val := Nat.mul_comm a.val b.val
  simp only [Fr.mul, Fr.ofNat, h₁]

-- Helper lemmas for add_assoc
private theorem mod_add_mod (a b m : Nat) : (a % m + b) % m = (a + b) % m := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

private theorem add_mod_mod (a b m : Nat) : (a + b % m) % m = (a + b) % m := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

-- Test 4: add_assoc (from Goedel - cleaned)
theorem Fr.add_assoc (a b c : Fr) : Fr.add (Fr.add a b) c = Fr.add a (Fr.add b c) := by
  simp only [Fr.add, Fr.ofNat]
  congr 1
  -- LHS: ((a.val + b.val) % modulus + c.val) % modulus
  -- RHS: (a.val + (b.val + c.val) % modulus) % modulus
  rw [mod_add_mod, add_mod_mod, Nat.add_assoc]

end GoedelFrProps
