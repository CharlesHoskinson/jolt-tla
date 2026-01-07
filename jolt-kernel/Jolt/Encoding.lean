import Jolt.Types

/-!
# Jolt Kernel Encoding

Implements S7.2: Bytes32ToFr2 and Fr2ToBytes32 conversions.

## Main Definitions

* `bytesToNatLE` - Little-endian bytes to Nat
* `natToBytesLE` - Nat to little-endian bytes
* `Bytes32ToFr2` - Encode 32 bytes as Fr pair
* `Fr2ToBytes32` - Decode Fr pair to 32 bytes

## Main Results

* `roundtrip_sound` - Fr2ToBytes32 (Bytes32ToFr2 b) = some b
* `injective_sound` - Bytes32ToFr2 is injective on valid inputs

## Implementation Notes

Uses little-endian encoding:
- First 31 bytes encode `lo` field element
- Last 1 byte encodes `hi` field element

The 2^248 bound ensures lo fits in 31 bytes (31 * 8 = 248 bits).
The 256 bound ensures hi fits in 1 byte.

## References

* Jolt Spec S7.2 (Bytes32 to field element encoding)
-/

namespace Jolt.Encoding

open Jolt

/-! ### Little-Endian Byte Conversion -/

/-- Convert little-endian bytes to Nat.

bytesToNatLE [b0, b1, b2, ...] = b0 + 256*b1 + 256^2*b2 + ... -/
def bytesToNatLE : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bytesToNatLE bs

/-- Convert Nat to little-endian bytes of fixed length.

natToBytesLE n len produces exactly `len` bytes representing
n in little-endian format (with zero padding if needed). -/
def natToBytesLE (n : Nat) : (len : Nat) → List UInt8
  | 0 => []
  | len + 1 => (UInt8.ofNat (n % 256)) :: natToBytesLE (n / 256) len

/-! ### Conversion Properties -/

/-- Length of natToBytesLE output. -/
theorem natToBytesLE_length (n : Nat) (len : Nat) :
    (natToBytesLE n len).length = len := by
  induction len generalizing n with
  | zero => rfl
  | succ k ih => simp only [natToBytesLE, List.length_cons, ih]

/-! ### Bytes32 to Fr2 Encoding -/

/-- Encode Bytes32 as (lo: 31 bytes, hi: 1 byte) field elements.

Returns none if the encoding doesn't satisfy Fr2 constraints
(though for valid Bytes32, this should always succeed). -/
def Bytes32ToFr2 (b : Bytes32) : Option Fr2 :=
  let bytes := b.toList
  let lo_bytes := bytes.take 31
  let hi_byte := bytes.getD 31 0
  let lo_nat := bytesToNatLE lo_bytes
  let hi_nat := hi_byte.toNat
  -- Construct Fr values
  if hlo : lo_nat < Fr.modulus then
    if hlo_bound : lo_nat < 2^248 then
      if hhi_bound : hi_nat < 256 then
        let lo : Fr := ⟨lo_nat, hlo⟩
        let hi : Fr := ⟨hi_nat, by
          have h1 : hi_nat < 256 := hhi_bound
          have h2 : (256 : Nat) < Fr.modulus := by decide
          exact Nat.lt_trans h1 h2⟩
        some ⟨lo, hi, hlo_bound, hhi_bound⟩
      else none
    else none
  else none

/-- Decode Fr pair back to Bytes32.

Returns none if Fr2 constraints are violated. -/
def Fr2ToBytes32 (fr2 : Fr2) : Option Bytes32 :=
  let lo_bytes := natToBytesLE fr2.lo.val 31
  let hi_byte : UInt8 := UInt8.ofNat fr2.hi.val
  let bytes := lo_bytes ++ [hi_byte]
  Bytes32.fromList? bytes

/-- Decode separate lo and hi Fr values to Bytes32. -/
def Fr2ToBytes32' (lo hi : Fr) : Option Bytes32 :=
  if _hlo : lo.val < 2^248 then
    if _hhi : hi.val < 256 then
      let lo_bytes := natToBytesLE lo.val 31
      let hi_byte : UInt8 := UInt8.ofNat hi.val
      let bytes := lo_bytes ++ [hi_byte]
      Bytes32.fromList? bytes
    else none
  else none

/-! ### Specification Predicates -/

/-- Specification: round-trip property.

If Bytes32ToFr2 succeeds, Fr2ToBytes32 recovers the original. -/
def SpecRoundTrip : Prop :=
  ∀ b : Bytes32, match Bytes32ToFr2 b with
    | some fr2 => Fr2ToBytes32 fr2 = some b
    | none => True

/-- Specification: encoding is injective.

Different Bytes32 values produce different Fr2 values. -/
def SpecInjective : Prop :=
  ∀ a b : Bytes32,
    Bytes32ToFr2 a = Bytes32ToFr2 b →
    (Bytes32ToFr2 a).isSome →
    a = b

/-! ### Checker Functions -/

/-- Check if Fr pair satisfies Fr2 validity constraints. -/
def checkFr2Valid (lo hi : Fr) : Bool :=
  lo.val < 2^248 && hi.val < 256

/-! ### Soundness Axioms -/

/-- THEOREM: bytesToNatLE of natToBytesLE roundtrip.

Proof by induction on len. -/
theorem bytesToNatLE_natToBytesLE (n : Nat) (len : Nat) (h : n < 256^len) :
    bytesToNatLE (natToBytesLE n len) = n := by
  induction len generalizing n with
  | zero =>
    -- n < 256^0 = 1 means n = 0
    simp only [Nat.pow_zero] at h
    have hn : n = 0 := Nat.lt_one_iff.mp h
    simp only [hn, natToBytesLE, bytesToNatLE]
  | succ k ih =>
    -- natToBytesLE n (k+1) = (n % 256) :: natToBytesLE (n / 256) k
    simp only [natToBytesLE, bytesToNatLE]
    -- (UInt8.ofNat (n % 256)).toNat = n % 256
    have hmod_lt : n % 256 < 256 := Nat.mod_lt n (by omega)
    have hmod : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
      have h1 : (UInt8.ofNat (n % 256)).toNat = (n % 256) % UInt8.size := UInt8.toNat_ofNat
      have h2 : UInt8.size = 256 := rfl
      rw [h1, h2]
      exact Nat.mod_eq_of_lt hmod_lt
    rw [hmod]
    -- n / 256 < 256^k (needed for IH)
    have hdiv : n / 256 < 256^k := by
      have hpow : (256 : Nat)^(k + 1) = 256 * 256^k := Nat.pow_succ'
      rw [hpow] at h
      exact Nat.div_lt_of_lt_mul h
    -- Apply IH
    rw [ih (n / 256) hdiv]
    -- n % 256 + 256 * (n / 256) = n
    omega

/-- THEOREM: natToBytesLE of bytesToNatLE roundtrip.

Proof by induction on bytes. -/
theorem natToBytesLE_bytesToNatLE (bytes : List UInt8) :
    natToBytesLE (bytesToNatLE bytes) bytes.length = bytes := by
  induction bytes with
  | nil => simp only [bytesToNatLE, List.length_nil, natToBytesLE]
  | cons b bs ih =>
    simp only [bytesToNatLE, List.length_cons, natToBytesLE]
    -- n = b.toNat + 256 * bytesToNatLE bs
    -- n % 256 = b.toNat (since b.toNat < 256)
    have hb_lt : b.toNat < 256 := by
      have : b.toNat < UInt8.size := UInt8.toNat_lt_size b
      simp only [UInt8.size] at this
      exact this
    have hmod : (b.toNat + 256 * bytesToNatLE bs) % 256 = b.toNat := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hb_lt
    -- n / 256 = bytesToNatLE bs
    have hdiv : (b.toNat + 256 * bytesToNatLE bs) / 256 = bytesToNatLE bs := by
      rw [Nat.add_mul_div_left _ _ (by omega : 0 < 256)]
      simp only [Nat.div_eq_of_lt hb_lt, Nat.zero_add]
    rw [hmod, hdiv]
    -- UInt8.ofNat b.toNat = b
    rw [UInt8.ofNat_toNat, ih]

/-- THEOREM: bytesToNatLE is bounded by 256^len.

Proof by induction on the byte list. -/
theorem bytesToNatLE_bound (bytes : List UInt8) :
    bytesToNatLE bytes < 256^bytes.length := by
  induction bytes with
  | nil => simp only [bytesToNatLE, List.length_nil, Nat.pow_zero]; omega
  | cons b bs ih =>
    simp only [bytesToNatLE, List.length_cons]
    -- b.toNat < 256 and bytesToNatLE bs < 256^bs.length
    have hb : b.toNat < 256 := by
      have : b.toNat ≤ 255 := UInt8.toNat_lt_size b |> Nat.lt_succ_iff.mp
      omega
    -- 256^(bs.length + 1) = 256 * 256^bs.length
    have hpow : (256 : Nat)^(bs.length + 1) = 256 * 256^bs.length := Nat.pow_succ'
    rw [hpow]
    -- b.toNat + 256 * bytesToNatLE bs < 256 + 256 * 256^bs.length
    -- ≤ 256 * 256^bs.length since 256^bs.length ≥ 1
    have h256_pos : (256 : Nat)^bs.length ≥ 1 := Nat.one_le_pow _ _ (by omega)
    omega

/-- THEOREM: 31 bytes can encode values up to 2^248.

Since 256 = 2^8, we have 256^31 = (2^8)^31 = 2^(8*31) = 2^248. -/
theorem bytes31_bound : (256 : Nat)^31 = 2^248 := by native_decide

/-! ### Soundness Theorems -/

/-- Helper: bytes list has length 32 from lo_bytes (31) ++ hi_byte (1). -/
theorem concat_length_32 (lo_bytes : List UInt8) (hi_byte : UInt8)
    (h : lo_bytes.length = 31) :
    (lo_bytes ++ [hi_byte]).length = 32 := by
  simp only [List.length_append, List.length_singleton, h]

/-- Helper: take 31 ++ [get 31] = original for 32-element list. -/
theorem take31_append_get31 {α : Type} (xs : List α) (h : xs.length = 32) (default : α) :
    xs.take 31 ++ [xs.getD 31 default] = xs := by
  have hlt : 31 < xs.length := by omega
  -- getD equals get when index is in bounds
  have hget : xs.getD 31 default = xs[31]'hlt := by
    unfold List.getD
    simp only [List.getElem?_eq_getElem hlt, Option.getD_some]
  rw [hget]
  -- drop 31 of 32-element list is [xs[31]]
  have hdrop_len : (xs.drop 31).length = 1 := by simp [h]
  have hdrop_eq : xs.drop 31 = [xs[31]'hlt] := by
    match hd : xs.drop 31 with
    | [] =>
      -- Impossible: drop has length 1, not 0
      have : ([] : List α).length = 1 := by rw [← hd]; exact hdrop_len
      simp at this
    | [a] =>
      congr 1
      have h0 : a = (xs.drop 31)[0]'(by omega) := by simp [hd]
      rw [h0, List.getElem_drop]
    | b :: c :: rest =>
      -- Impossible: drop has length 1, not 2+
      have hlen : (b :: c :: rest).length = 1 := by rw [← hd]; exact hdrop_len
      simp at hlen
  -- Rewrite using take_append_drop
  calc xs.take 31 ++ [xs[31]'hlt]
      = xs.take 31 ++ xs.drop 31 := by rw [hdrop_eq]
    _ = xs := List.take_append_drop 31 xs

/-- Helper: fromList? ∘ toList = some for Bytes32. -/
theorem Bytes32_fromList_toList (b : Bytes32) :
    Bytes32.fromList? b.toList = some b := by
  unfold Bytes32.fromList? Bytes32.toList
  have hlen : b.data.toList.length = 32 := by simp [b.h_len]
  simp only [dif_pos hlen, Array.toArray_toList]

/-- Helper: 2^248 < Fr.modulus. -/
theorem pow248_lt_modulus : (2 : Nat)^248 < Fr.modulus := by native_decide

/-- Helper: take 31 of a 32-element list has length 31. -/
theorem take31_of_32 {α : Type} (xs : List α) (h : xs.length = 32) :
    (xs.take 31).length = 31 := by
  simp only [List.length_take, h]
  omega

/-- Helper: lo_nat from 31 bytes is bounded. -/
theorem lo_nat_bound (b : Bytes32) :
    let lo_bytes := b.toList.take 31
    let lo_nat := bytesToNatLE lo_bytes
    lo_nat < 2^248 := by
  simp only []
  have hlen : (b.toList.take 31).length ≤ 31 := by
    simp only [List.length_take]
    omega
  have hbound := bytesToNatLE_bound (b.toList.take 31)
  have h256_31 : (256 : Nat)^31 = 2^248 := bytes31_bound
  calc bytesToNatLE (b.toList.take 31)
      < 256^(b.toList.take 31).length := hbound
    _ ≤ 256^31 := Nat.pow_le_pow_right (by omega) hlen
    _ = 2^248 := h256_31

/-- Helper: hi_byte.toNat < 256. -/
theorem hi_nat_bound (byte : UInt8) : byte.toNat < 256 := by
  have h := UInt8.toNat_lt_size byte
  simp only [UInt8.size] at h
  exact h

/-- THEOREM: Bytes32ToFr2 always succeeds on valid Bytes32.

Proof: lo_nat < 2^248 < Fr.modulus and hi_nat < 256. -/
theorem Bytes32ToFr2_succeeds (b : Bytes32) : (Bytes32ToFr2 b).isSome := by
  unfold Bytes32ToFr2
  simp only []
  -- lo_nat < Fr.modulus
  have hlo_mod : bytesToNatLE (b.toList.take 31) < Fr.modulus := by
    have h1 := lo_nat_bound b
    exact Nat.lt_trans h1 pow248_lt_modulus
  -- lo_nat < 2^248
  have hlo_bound := lo_nat_bound b
  -- hi_nat < 256
  have hhi_bound := hi_nat_bound (b.toList.getD 31 0)
  simp only [hlo_mod, hlo_bound, hhi_bound, ↓reduceDIte, Option.isSome_some]

/-- THEOREM: Round-trip soundness.

Fr2ToBytes32 (Bytes32ToFr2 b) = some b. -/
theorem roundtrip_sound : SpecRoundTrip := by
  intro b
  -- We know Bytes32ToFr2 b succeeds
  have hsucceeds := Bytes32ToFr2_succeeds b
  simp only [Option.isSome_iff_exists] at hsucceeds
  obtain ⟨fr2, hfr2⟩ := hsucceeds
  simp only [hfr2]
  -- Unfold Fr2ToBytes32
  unfold Fr2ToBytes32
  -- Get the lo and hi values from the encoding
  unfold Bytes32ToFr2 at hfr2
  simp only [] at hfr2
  -- Extract the conditions
  have hlen32 := b.toList_length
  split at hfr2
  · rename_i hlo_mod
    split at hfr2
    · rename_i hlo_bound
      split at hfr2
      · rename_i hhi_bound
        -- fr2 is the encoded value
        injection hfr2 with hfr2_eq
        simp only [← hfr2_eq]
        -- lo_bytes = natToBytesLE (bytesToNatLE (b.toList.take 31)) 31
        -- hi_byte = UInt8.ofNat (b.toList.getD 31 0).toNat
        have hlo_len : (b.toList.take 31).length = 31 := take31_of_32 b.toList hlen32
        have hlo_roundtrip : natToBytesLE (bytesToNatLE (b.toList.take 31)) 31 = b.toList.take 31 := by
          have h := natToBytesLE_bytesToNatLE (b.toList.take 31)
          rw [hlo_len] at h
          exact h
        have hhi_roundtrip : UInt8.ofNat (b.toList.getD 31 0).toNat = b.toList.getD 31 0 :=
          UInt8.ofNat_toNat
        simp only [hlo_roundtrip, hhi_roundtrip]
        -- Now need: Bytes32.fromList? (b.toList.take 31 ++ [b.toList.getD 31 0]) = some b
        have hconcat := take31_append_get31 b.toList hlen32 0
        rw [hconcat]
        exact Bytes32_fromList_toList b
      · simp at hfr2
    · simp at hfr2
  · simp at hfr2

/-- THEOREM: Encoding is injective.

If Bytes32ToFr2 a = Bytes32ToFr2 b, then a = b.
Proof: Apply round-trip to both sides. -/
theorem injective_sound : SpecInjective := by
  intro a b heq hisSome
  -- Both encode to the same fr2
  simp only [Option.isSome_iff_exists] at hisSome
  obtain ⟨fr2, hfr2_a⟩ := hisSome
  have hfr2_b : Bytes32ToFr2 b = some fr2 := by rw [← heq]; exact hfr2_a
  -- Apply roundtrip_sound to both
  have ha := roundtrip_sound a
  have hb := roundtrip_sound b
  simp only [hfr2_a] at ha
  simp only [hfr2_b] at hb
  -- Fr2ToBytes32 fr2 = some a and Fr2ToBytes32 fr2 = some b
  rw [ha] at hb
  injection hb

end Jolt.Encoding
