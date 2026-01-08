import Jolt.Errors
import Jolt.Field.Fr
import Jolt.Encoding.Bytes32
import Jolt.Encoding.Fr2

namespace Jolt.Wrapper

/-- Status codes for wrapper public inputs. -/
inductive Status where
  | Success       -- 0
  | Failure       -- 1
  | Pending       -- 2
  deriving Repr, DecidableEq

namespace Status

def toFr : Status → Fr
  | .Success => Fr.zero
  | .Failure => Fr.one
  | .Pending => Fr.ofNat 2

def fromFr (x : Fr) : OracleResult Status := do
  if x.val == 0 then pure .Success
  else if x.val == 1 then pure .Failure
  else if x.val == 2 then pure .Pending
  else throw (ErrorCode.E402_OutOfRange "status must be 0, 1, or 2")

end Status

/-- Wrapper circuit public inputs.

Exactly 11 Fr elements arranged as specified in §5.2. -/
structure PublicInputs where
  /-- Program hash as Fr2 (elements 0-1) -/
  programHash : Fr2
  /-- Old state root as Fr2 (elements 2-3) -/
  oldRoot : Fr2
  /-- New state root as Fr2 (elements 4-5) -/
  newRoot : Fr2
  /-- Batch commitment as Fr2 (elements 6-7) -/
  batchCommitment : Fr2
  /-- Checkpoints digest (element 8) - canonical Fr -/
  checkpointsDigest : Fr
  /-- Status (element 9) - u8 as Fr -/
  status : Status
  /-- Batch nonce (element 10) - u64 as Fr -/
  batchNonce : UInt64
  deriving Repr

namespace PublicInputs

/-- Number of Fr elements. -/
def size : Nat := 11

/-- Convert to array of 11 Fr elements. -/
def toArray (pi : PublicInputs) : Array Fr :=
  #[pi.programHash.lo, pi.programHash.hi,
    pi.oldRoot.lo, pi.oldRoot.hi,
    pi.newRoot.lo, pi.newRoot.hi,
    pi.batchCommitment.lo, pi.batchCommitment.hi,
    pi.checkpointsDigest,
    pi.status.toFr,
    Fr.fromU64 pi.batchNonce]

/-- Construct from array of 11 Fr elements. -/
def fromArray (arr : Array Fr) : OracleResult PublicInputs := do
  if arr.size != 11 then
    throw (ErrorCode.E104_WrongLength 11 arr.size)
  let status ← Status.fromFr arr[9]!
  -- Validate batch_nonce fits in u64
  if arr[10]!.val >= 2^64 then
    throw (ErrorCode.E402_OutOfRange "batch_nonce exceeds u64")
  pure {
    programHash := { lo := arr[0]!, hi := arr[1]! }
    oldRoot := { lo := arr[2]!, hi := arr[3]! }
    newRoot := { lo := arr[4]!, hi := arr[5]! }
    batchCommitment := { lo := arr[6]!, hi := arr[7]! }
    checkpointsDigest := arr[8]!
    status := status
    batchNonce := arr[10]!.val.toUInt64
  }

/-- Validate checkpoints_digest is canonical (< modulus).

This is always true for Fr values, but we include for documentation. -/
def validateCanonical (_pi : PublicInputs) : OracleResult Unit := do
  -- Fr values are always < modulus by construction
  pure ()

end PublicInputs

end Jolt.Wrapper
