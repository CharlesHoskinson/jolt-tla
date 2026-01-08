import Jolt.Errors

namespace Jolt

/-- A 32-byte array with size invariant. -/
structure Bytes32 where
  data : ByteArray
  size_eq : data.size = 32

namespace Bytes32

instance : Repr Bytes32 where
  reprPrec b _ := repr b.data.toList

/-- Construct Bytes32 from ByteArray, checking length. -/
def ofByteArray (ba : ByteArray) : OracleResult Bytes32 :=
  if h : ba.size = 32 then
    pure ⟨ba, h⟩
  else
    throw (ErrorCode.E104_WrongLength 32 ba.size)

/-- The all-zeros 32-byte array. -/
def zero : Bytes32 := ⟨⟨List.replicate 32 0 |>.toArray⟩, by native_decide⟩

instance : Inhabited Bytes32 := ⟨zero⟩

/-- Access a byte by index (unchecked). -/
def getD (b : Bytes32) (i : Nat) : UInt8 :=
  if i < b.data.size then b.data.data[i]! else 0

/-- Convert to ByteArray. -/
def toByteArray (b : Bytes32) : ByteArray := b.data

/-- Check equality by comparing underlying arrays. -/
instance : DecidableEq Bytes32 := fun a b =>
  if h : a.data.data = b.data.data then
    isTrue (by
      cases a with | mk ad asz =>
      cases b with | mk bd bsz =>
      simp only at h
      congr
      cases ad; cases bd
      simp_all)
  else
    isFalse (by intro heq; cases heq; exact h rfl)

end Bytes32
end Jolt
