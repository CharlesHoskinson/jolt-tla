import Jolt.Logic

/-!
# Jolt Kernel Types

Core types matching spec.md S5, S7.

## Main Definitions

* `Fr` - BN254 scalar field element as `Fin r`
* `Bytes32` - 32-byte fixed-size container
* `U64` - 64-bit unsigned integer (alias for UInt64)
* `Fr2` - Fr pair with range constraints for Bytes32 encoding

## References

* Jolt Spec S5 (data types)
* Jolt Spec S7 (field encodings)
-/

namespace Jolt

/-! ### BN254 Field Type -/

/-- BN254 scalar field modulus. -/
def Fr.modulus : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- Proof that modulus is positive. -/
theorem Fr.modulus_pos : 0 < Fr.modulus := by decide

/-- Field element as Fin r - enforces canonical range [0, r-1]. -/
def Fr := Fin Fr.modulus

namespace Fr

/-- Zero element. -/
def zero : Fr := ⟨0, Fr.modulus_pos⟩

/-- One element. -/
def one : Fr := ⟨1, by decide⟩

/-- Smart constructor - rejects non-canonical. -/
def ofNat? (n : Nat) : Option Fr :=
  if h : n < Fr.modulus then some ⟨n, h⟩ else none

/-- Constructor from Nat (reduces mod r). -/
def ofNat (n : Nat) : Fr := ⟨n % Fr.modulus, Nat.mod_lt n Fr.modulus_pos⟩

/-- Get the underlying natural number value. -/
def toNat (x : Fr) : Nat := x.val

/-- Decidable equality. -/
instance instDecidableEqFr : DecidableEq Fr := inferInstanceAs (DecidableEq (Fin Fr.modulus))

/-- BEq instance (uses Fin's BEq). -/
instance instBEqFr : BEq Fr := inferInstanceAs (BEq (Fin Fr.modulus))

/-- LawfulBEq instance for Fr (uses Fin's LawfulBEq). -/
instance instLawfulBEqFr : LawfulBEq Fr := inferInstanceAs (LawfulBEq (Fin Fr.modulus))

/-- Repr for debugging. -/
instance : Repr Fr := ⟨fun x _ => s!"Fr({x.val})"⟩

/-- Inhabited instance. -/
instance : Inhabited Fr := ⟨Fr.zero⟩

/-- Addition (mod r). -/
instance : Add Fr := ⟨Fin.add⟩

/-- Multiplication (mod r). -/
instance : Mul Fr := ⟨Fin.mul⟩

/-- Subtraction (mod r). -/
instance : Sub Fr := ⟨Fin.sub⟩

/-- Negation (mod r). -/
instance : Neg Fr := ⟨fun x => ⟨(Fr.modulus - x.val) % Fr.modulus, Nat.mod_lt _ Fr.modulus_pos⟩⟩

/-- Zero detection. -/
def isZero (x : Fr) : Bool := x.val == 0

/-- Equality check. -/
def eq (a b : Fr) : Bool := a.val == b.val

/-- Theorem: Fr.zero has value 0. -/
theorem zero_val : Fr.zero.val = 0 := rfl

/-- Theorem: Fr.one has value 1. -/
theorem one_val : Fr.one.val = 1 := rfl

end Fr

/-! ### 64-bit Unsigned Integer -/

/-- 64-bit unsigned integer. -/
abbrev U64 := UInt64

namespace U64

/-- Convert U64 to Fr (always valid since 2^64 < r). -/
def toFr (x : U64) : Fr :=
  ⟨x.toNat, by
    have h : x.toNat < 2^64 := x.toBitVec.isLt
    have hmod : 2^64 < Fr.modulus := by decide
    exact Nat.lt_trans h hmod⟩

/-- Maximum U64 value. -/
def max : U64 := 0xFFFFFFFFFFFFFFFF

end U64

/-! ### 32-Byte Fixed Container -/

/-- 32-byte fixed-size container. -/
structure Bytes32 where
  /-- The underlying byte array. -/
  data : Array UInt8
  /-- Proof that array has exactly 32 bytes. -/
  h_len : data.size = 32
  deriving DecidableEq

namespace Bytes32

/-- Zero bytes (all zeros). -/
def zero : Bytes32 := ⟨(List.replicate 32 (0 : UInt8)).toArray, by native_decide⟩

/-- Get byte at index i. -/
def get (b : Bytes32) (i : Fin 32) : UInt8 :=
  b.data[i.val]'(by rw [b.h_len]; exact i.isLt)

/-- Set byte at index i. -/
def set (b : Bytes32) (i : Fin 32) (v : UInt8) : Bytes32 :=
  let idx : Fin b.data.size := ⟨i.val, by rw [b.h_len]; exact i.isLt⟩
  ⟨b.data.set idx v, by simp only [Array.size_set]; exact b.h_len⟩

/-- Convert to list of bytes. -/
def toList (b : Bytes32) : List UInt8 := b.data.toList

/-- Convert from list of bytes. -/
def fromList? (l : List UInt8) : Option Bytes32 :=
  if h : l.length = 32 then
    some ⟨l.toArray, by simp [h]⟩
  else none

/-- Convert from array. -/
def fromArray? (a : Array UInt8) : Option Bytes32 :=
  if h : a.size = 32 then some ⟨a, h⟩ else none

/-- BEq instance (derived from DecidableEq for LawfulBEq). -/
instance : BEq Bytes32 := ⟨fun a b => decide (a = b)⟩

/-- LawfulBEq for Bytes32. -/
instance : LawfulBEq Bytes32 where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-- Repr for debugging. -/
instance : Repr Bytes32 := ⟨fun b _ => s!"Bytes32({b.data.toList.take 4}...)"⟩

/-- Inhabited instance. -/
instance : Inhabited Bytes32 := ⟨Bytes32.zero⟩

/-- Theorem: toList has length 32. -/
theorem toList_length (b : Bytes32) : b.toList.length = 32 := by
  simp only [toList]
  rw [Array.length_toList]
  exact b.h_len

end Bytes32

/-! ### Fr Pair with Range Constraints -/

/-- Fr pair with range constraints for Bytes32 encoding. -/
structure Fr2 where
  /-- Low part (31 bytes worth). -/
  lo : Fr
  /-- High part (1 byte worth). -/
  hi : Fr
  /-- Constraint: lo < 2^248. -/
  lo_bound : lo.val < 2^248
  /-- Constraint: hi < 256. -/
  hi_bound : hi.val < 256
  deriving DecidableEq

namespace Fr2

/-- Check if a pair of Fr values satisfies Fr2 constraints. -/
def isValid (lo hi : Fr) : Bool :=
  lo.val < 2^248 && hi.val < 256

/-- Smart constructor. -/
def mk? (lo hi : Fr) : Option Fr2 :=
  if hlo : lo.val < 2^248 then
    if hhi : hi.val < 256 then
      some ⟨lo, hi, hlo, hhi⟩
    else none
  else none

/-- Zero Fr2 (both parts zero). -/
def zero : Fr2 := ⟨Fr.zero, Fr.zero, by decide, by decide⟩

/-- BEq instance. -/
instance : BEq Fr2 := ⟨fun a b => a.lo == b.lo && a.hi == b.hi⟩

/-- Repr for debugging. -/
instance : Repr Fr2 := ⟨fun x _ => s!"Fr2(lo={x.lo.val}, hi={x.hi.val})"⟩

/-- Inhabited instance. -/
instance : Inhabited Fr2 := ⟨Fr2.zero⟩

end Fr2

/-! ### Vector Type -/

/-- Fixed-size vector backed by Array. -/
structure Vec (α : Type) (n : Nat) where
  /-- Underlying array. -/
  data : Array α
  /-- Length proof. -/
  h_len : data.size = n
  deriving DecidableEq

namespace Vec

/-- Create vector filled with value v. -/
def replicate {α : Type} (n : Nat) (v : α) : Vec α n :=
  ⟨(List.replicate n v).toArray, by simp⟩

/-- Get element at index. -/
def get {α : Type} {n : Nat} (v : Vec α n) (i : Fin n) : α :=
  v.data[i.val]'(by rw [v.h_len]; exact i.isLt)

/-- Set element at index. -/
def set {α : Type} {n : Nat} (v : Vec α n) (i : Fin n) (x : α) : Vec α n :=
  let idx : Fin v.data.size := ⟨i.val, by rw [v.h_len]; exact i.isLt⟩
  ⟨v.data.set idx x, by simp only [Array.size_set]; exact v.h_len⟩

/-- Convert to list. -/
def toList {α : Type} {n : Nat} (v : Vec α n) : List α := v.data.toList

/-- BEq when α has BEq. -/
instance {α : Type} {n : Nat} [BEq α] : BEq (Vec α n) := ⟨fun a b => a.data == b.data⟩

/-- Repr when α has Repr. -/
instance {α : Type} {n : Nat} [Repr α] : Repr (Vec α n) := ⟨fun v _ => repr v.data.toList⟩

end Vec

/-! ### Register File -/

/-- RISC-V register file (32 registers). -/
abbrev RegFile := Vec Fr 32

namespace RegFile

/-- Initial register file (all zeros). -/
def initial : RegFile := Vec.replicate 32 Fr.zero

/-- Read register. -/
def read (rf : RegFile) (i : Fin 32) : Fr := Vec.get rf i

/-- Write register (x0 is hardwired to zero). -/
def write (rf : RegFile) (i : Fin 32) (v : Fr) : RegFile :=
  if i.val = 0 then rf else Vec.set rf i v

/-- Theorem: x0 is zero in initial register file. -/
theorem initial_x0_zero : read initial ⟨0, by decide⟩ = Fr.zero := by
  simp only [initial, read, Vec.get, Vec.replicate]
  rfl

/-- Theorem: write to x0 has no effect. -/
theorem write_x0_noop (rf : RegFile) (v : Fr) : write rf ⟨0, by decide⟩ v = rf := by
  simp only [write]
  rfl

end RegFile

end Jolt
