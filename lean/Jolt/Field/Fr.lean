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

/-- Parse a hex character to its numeric value (0-15). Returns none for invalid chars. -/
private def hexCharToNat (c : Char) : Option Nat :=
  if c >= '0' && c <= '9' then some (c.toNat - '0'.toNat)
  else if c >= 'a' && c <= 'f' then some (c.toNat - 'a'.toNat + 10)
  else if c >= 'A' && c <= 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Parse a 64-character lowercase hex string (no 0x prefix) as bytes32 little-endian to Fr.
    Per spec: canonical bytes32 is 64 lowercase hex chars representing LE bytes. -/
def fromHex64LE (hex : String) : OracleResult Fr := do
  if hex.length != 64 then
    throw (ErrorCode.E104_WrongLength 64 hex.length)
  -- Parse hex pairs as bytes (each pair is one byte)
  let mut bytes := ByteArray.empty
  let chars := hex.toList
  for i in [:32] do
    let hi := chars.getD (i * 2) '0'
    let lo := chars.getD (i * 2 + 1) '0'
    match hexCharToNat hi, hexCharToNat lo with
    | some h, some l => bytes := bytes.push ((h * 16 + l).toUInt8)
    | _, _ => throw ErrorCode.E103_InvalidHex
  fromBytes32LECanonical bytes

/-- Encode Fr as 64-character lowercase hex string (bytes32 LE format). -/
def toHex64LE (x : Fr) : String := Id.run do
  let bytes := toBytes32LE x
  let mut result := ""
  for i in [:32] do
    let b := bytes.data[i]!.toNat
    let hi := if b / 16 < 10 then Char.ofNat ('0'.toNat + b / 16)
              else Char.ofNat ('a'.toNat + b / 16 - 10)
    let lo := if b % 16 < 10 then Char.ofNat ('0'.toNat + b % 16)
              else Char.ofNat ('a'.toNat + b % 16 - 10)
    result := result.push hi
    result := result.push lo
  result

end Fr
end Jolt
