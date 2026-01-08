import Jolt.Field.Fr
import Jolt.Encoding.Bytes32

namespace Jolt

/-- A pair of field elements representing 32 bytes via 31+1 split. -/
structure Fr2 where
  lo : Fr
  hi : Fr
  deriving Repr, DecidableEq

/-- Encode Bytes32 as Fr2 using 31+1 split.

First 31 bytes → lo, last byte → hi.
This always succeeds since both parts are guaranteed < modulus. -/
def bytes32ToFr2 (bytes : Bytes32) : Fr2 := Id.run do
  let mut loVal : Nat := 0
  for i in [:31] do
    loVal := loVal + bytes.data[i]!.toNat * (256 ^ i)
  let hiVal := bytes.data[31]!.toNat
  pure { lo := Fr.ofNat loVal, hi := Fr.ofNat hiVal }

/-- Decode Fr2 to Bytes32.

Fails if:
- lo.val ≥ 2^248 (would overflow 31 bytes)
- hi.val ≥ 256 (would overflow 1 byte)

Never truncates—always rejects invalid values. -/
def fr2ToBytes32 (fr2 : Fr2) : OracleResult Bytes32 := do
  let loVal := fr2.lo.toNat
  let hiVal := fr2.hi.toNat
  if loVal ≥ 2^248 then
    throw ErrorCode.E301_Fr2LoBoundsViolation
  if hiVal ≥ 256 then
    throw ErrorCode.E302_Fr2HiBoundsViolation
  let mut bytes := ByteArray.empty
  let mut lo := loVal
  for _ in [:31] do
    bytes := bytes.push (lo % 256).toUInt8
    lo := lo / 256
  bytes := bytes.push hiVal.toUInt8
  if h : bytes.size = 32 then
    pure ⟨bytes, h⟩
  else
    -- This should never happen given the loop structure
    throw (ErrorCode.E104_WrongLength 32 bytes.size)

end Jolt
