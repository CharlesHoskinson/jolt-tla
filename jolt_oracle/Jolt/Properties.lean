import Jolt.Field.Fr
import Jolt.Encoding.Bytes32
import Jolt.Encoding.Fr2

/-!
# Formal Properties for Jolt Oracle

Provable properties about core types and operations.
These theorems establish correctness guarantees for the executable specification.

## Modules Covered
- Fr (BLS12-381 scalar field)
- Bytes32 (32-byte arrays)
- Fr2 (31+1 byte encoding)

## Status
These theorems use `sorry` placeholders to be filled by automated proof generation.
-/

namespace Jolt

open Fr

/-! ## Field Arithmetic Properties -/

/-- Addition is commutative. -/
theorem Fr.add_comm (a b : Fr) : a + b = b + a := by
  simp only [HAdd.hAdd, Add.add, Fr.add, Fr.ofNat]
  have h : Nat.add a.val b.val = Nat.add b.val a.val := Nat.add_comm a.val b.val
  simp_all

/-- Multiplication is commutative. -/
theorem Fr.mul_comm (a b : Fr) : a * b = b * a := by
  simp only [HMul.hMul, Mul.mul, Fr.mul, Fr.ofNat]
  have h : Nat.mul a.val b.val = Nat.mul b.val a.val := Nat.mul_comm a.val b.val
  simp_all

/-- Adding zero is identity (right). -/
theorem Fr.add_zero_right (a : Fr) : a + Fr.zero = a := by
  simp only [HAdd.hAdd, Add.add, Fr.add, Fr.zero, Fr.ofNat]
  have h1 : Nat.add a.val 0 = a.val := Nat.add_zero a.val
  have h2 : a.val % modulus = a.val := Nat.mod_eq_of_lt a.isLt
  simp_all

/-- Multiplying by one is identity (right). -/
theorem Fr.mul_one_right (a : Fr) : a * Fr.one = a := by
  simp only [HMul.hMul, Mul.mul, Fr.mul, Fr.one, Fr.ofNat]
  have h1 : Nat.mul a.val 1 = a.val := Nat.mul_one a.val
  have h2 : a.val % modulus = a.val := Nat.mod_eq_of_lt a.isLt
  simp_all

/-- Zero is the additive identity (left). -/
theorem Fr.zero_add (a : Fr) : Fr.zero + a = a := by
  simp only [HAdd.hAdd, Add.add, Fr.add, Fr.zero, Fr.ofNat]
  have h1 : Nat.add 0 a.val = a.val := Nat.zero_add a.val
  have h2 : a.val % modulus = a.val := Nat.mod_eq_of_lt a.isLt
  simp_all

/-- One is the multiplicative identity (left). -/
theorem Fr.one_mul (a : Fr) : Fr.one * a = a := by
  simp only [HMul.hMul, Mul.mul, Fr.mul, Fr.one, Fr.ofNat]
  have h1 : Nat.mul 1 a.val = a.val := Nat.one_mul a.val
  have h2 : a.val % modulus = a.val := Nat.mod_eq_of_lt a.isLt
  simp_all

/-! ## Bytes32 Properties -/

/-- The zero Bytes32 has exactly 32 bytes. -/
theorem Bytes32.zero_has_size_32 : Bytes32.zero.data.size = 32 :=
  Bytes32.zero.size_eq

/-- Any Bytes32 has exactly 32 bytes (by construction). -/
theorem Bytes32.size_invariant (b : Bytes32) : b.data.size = 32 :=
  b.size_eq

/-! ## Negation Properties -/

/-- Negating zero gives zero. -/
theorem Fr.neg_zero : -Fr.zero = Fr.zero := by
  simp only [Neg.neg, Fr.neg, Fr.zero]
  rfl

/-- Double negation is identity. -/
theorem Fr.neg_neg (a : Fr) : -(-a) = a := by
  by_cases h : a.val = 0
  · -- Case: a.val = 0
    have ha : a = Fr.zero := by
      cases a
      simp only [Fr.zero, Fr.mk.injEq]
      exact h
    simp only [ha, Fr.neg_zero]
  · -- Case: a.val ≠ 0
    simp only [Neg.neg, Fr.neg]
    simp only [h, dite_false]
    -- -a has val = modulus - a.val
    have hna : (modulus - a.val) ≠ 0 := by
      have hlt : a.val < modulus := a.isLt
      have hpos : a.val > 0 := Nat.pos_of_ne_zero h
      omega
    simp only [hna, dite_false]
    -- Now need to show modulus - (modulus - a.val) = a.val
    cases a with
    | mk v isLt =>
      simp only [Fr.mk.injEq]
      have hlt : v < modulus := isLt
      omega

/-- Subtracting zero is identity. -/
theorem Fr.sub_zero (a : Fr) : a - Fr.zero = a := by
  show Fr.add a (Fr.neg Fr.zero) = a
  have h1 : Fr.neg Fr.zero = Fr.zero := Fr.neg_zero
  simp only [h1]
  exact Fr.add_zero_right a

/-- Subtracting self gives zero. -/
theorem Fr.sub_self (a : Fr) : a - a = Fr.zero := by
  by_cases h : a.val = 0
  · -- Case: a.val = 0
    have ha : a = Fr.zero := by
      cases a
      simp only [Fr.zero, Fr.mk.injEq]
      exact h
    simp only [ha]
    show Fr.zero - Fr.zero = Fr.zero
    exact Fr.sub_zero Fr.zero
  · -- Case: a.val ≠ 0
    show Fr.add a (Fr.neg a) = Fr.zero
    simp only [Fr.add, Fr.neg, h, dite_false, Fr.ofNat, Fr.zero]
    -- a.val + (modulus - a.val) = modulus
    -- modulus % modulus = 0
    cases a with
    | mk v isLt =>
      simp only [Fr.mk.injEq]
      have hlt : v < modulus := isLt
      have hsum : v + (modulus - v) = modulus := by omega
      simp only [hsum, Nat.mod_self]

/-! ## Test Theorems for Red Team -/

/-- Multiplication by zero gives zero (TEST - for red team). -/
theorem Fr.mul_zero (a : Fr) : a * Fr.zero = Fr.zero := by
  simp only [HMul.hMul, Mul.mul, Fr.mul, Fr.zero, Fr.ofNat]
  rfl

/-- Zero times anything is zero (left). -/
theorem Fr.zero_mul (a : Fr) : Fr.zero * a = Fr.zero := by
  simp only [HMul.hMul, Mul.mul, Fr.mul, Fr.zero, Fr.ofNat]
  have h : Nat.mul 0 a.val = 0 := Nat.zero_mul a.val
  simp_all

end Jolt
