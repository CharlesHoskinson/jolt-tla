import Jolt.Errors

namespace Jolt

/-- The BLS12-381 scalar field modulus. -/
def Fr.modulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

/-- A BLS12-381 scalar field element. -/
structure Fr where
  val : Nat
  isLt : val < Fr.modulus
  deriving DecidableEq

namespace Fr

instance : Repr Fr where
  reprPrec f _ := repr f.val

instance : Inhabited Fr := ⟨⟨0, by native_decide⟩⟩

/-- The additive identity. -/
def zero : Fr := ⟨0, by native_decide⟩

/-- The multiplicative identity. -/
def one : Fr := ⟨1, by native_decide⟩

/-- Convert a natural number to Fr, reducing mod r. -/
def ofNat (n : Nat) : Fr := ⟨n % modulus, Nat.mod_lt n (by native_decide)⟩

/-- Field addition. -/
def add (a b : Fr) : Fr := ofNat (a.val + b.val)

/-- Field multiplication. -/
def mul (a b : Fr) : Fr := ofNat (a.val * b.val)

/-- Field negation. -/
def neg (a : Fr) : Fr :=
  if h : a.val = 0 then zero
  else ⟨modulus - a.val, by
    have h1 : a.val > 0 := Nat.pos_of_ne_zero h
    have h2 : a.val < modulus := a.isLt
    omega⟩

/-- Field subtraction. -/
def sub (a b : Fr) : Fr := add a (neg b)

/-- Field squaring. -/
def sq (a : Fr) : Fr := mul a a

/-- Raise to the 5th power (used in Poseidon S-box). -/
def pow5 (x : Fr) : Fr := mul (sq (sq x)) x

instance : Add Fr := ⟨add⟩
instance : Mul Fr := ⟨mul⟩
instance : Sub Fr := ⟨sub⟩
instance : Neg Fr := ⟨neg⟩

/-- Convert Fr to Nat. -/
def toNat (x : Fr) : Nat := x.val

/-- Convert UInt64 to Fr. -/
def fromU64 (x : UInt64) : Fr := ofNat x.toNat

/-- Helper to get byte from ByteArray. -/
private def getByte (bytes : ByteArray) (i : Nat) : UInt8 :=
  if i < bytes.size then bytes.data[i]! else 0

/-- Decode 32 bytes (little-endian) to Fr, rejecting non-canonical values. -/
def fromBytes32LECanonical (bytes : ByteArray) : OracleResult Fr := do
  if bytes.size ≠ 32 then
    throw (ErrorCode.E104_WrongLength 32 bytes.size)
  let mut val : Nat := 0
  for i in [:32] do
    val := val + (getByte bytes i).toNat * (256 ^ i)
  if hge : val ≥ modulus then
    throw (ErrorCode.E300_NonCanonicalFr (toString val))
  else
    pure ⟨val, Nat.lt_of_not_le hge⟩

/-- Encode Fr as 32 bytes (little-endian). -/
def toBytes32LE (x : Fr) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  let mut val := x.val
  for _ in [:32] do
    bytes := bytes.push (val % 256).toUInt8
    val := val / 256
  return bytes

end Fr
end Jolt
