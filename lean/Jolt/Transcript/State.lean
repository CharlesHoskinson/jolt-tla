import Jolt.Transcript.Types
import Jolt.Transcript.TagValidation
import Jolt.Encoding.Bytes32
import Jolt.Encoding.Fr2

namespace Jolt.Transcript

/-- Convert up to 31 bytes to Fr (little-endian).

Rejects if more than 31 bytes (never truncate). -/
def frFromU248 (bytes : ByteArray) : OracleResult Fr := do
  if bytes.size > 31 then
    throw (ErrorCode.E104_WrongLength 31 bytes.size)
  let mut val : Nat := 0
  for i in [:bytes.size] do
    val := val + bytes[i]!.toNat * (256 ^ i)
  pure (Fr.ofNat val)

/-- Absorb a single field element (RAW, no type tag).

This is the primitive absorb - no type tagging. -/
def absorbFr (s : State) (x : Fr) : State :=
  { s with sponge := s.sponge.absorbOne x }

/-- Absorb a u64 with TYPE_U64 tag. -/
def absorbU64 (s : State) (x : UInt64) : State :=
  let s1 := absorbFr s TYPE_U64
  absorbFr s1 (Fr.fromU64 x)

/-- Absorb bytes with TYPE_BYTES tag.

Absorbs: TYPE_BYTES, then absorb_u64(len), then ceil(len/31) Fr elements.
Per §8.5.2: absorb_u64 includes TYPE_U64 before the length value. -/
def absorbBytes (s : State) (bytes : ByteArray) : OracleResult State := do
  -- Check length fits in u64
  if bytes.size >= MAX_U64 then
    throw (ErrorCode.E402_OutOfRange "bytes length exceeds u64")
  let len := bytes.size.toUInt64
  -- Absorb TYPE_BYTES, then absorb_u64(len) per §8.5.2
  let s1 := absorbFr s TYPE_BYTES
  let s2 := absorbU64 s1 len  -- §8.5.2 step 3: absorb_u64(n)
  -- Absorb in 31-byte chunks
  let mut st := s2
  let mut pos := 0
  while pos < bytes.size do
    let chunkEnd := min (pos + 31) bytes.size
    let chunk := bytes.extract pos chunkEnd
    let fr ← frFromU248 chunk
    st := absorbFr st fr
    pos := chunkEnd
  pure st

/-- Absorb Bytes32 as two Fr elements (Fr2 encoding). -/
def absorbBytes32 (s : State) (b : Bytes32) : State :=
  let fr2 := Jolt.bytes32ToFr2 b
  let s1 := absorbFr s fr2.lo
  absorbFr s1 fr2.hi

/-- Absorb a transcript tag per §8.6.

Absorbs: TYPE_TAG, then absorb_u64(len), then ceil(len/31) raw Fr chunks.
Per §8.6: absorb_u64 includes TYPE_U64 before the length value.
This is NOT the same as absorb_bytes (different type tag at start). -/
def absorbTag (s : State) (tag : String) : OracleResult State := do
  -- Validate tag format
  validateTag tag
  let bytes := tag.toUTF8
  -- Check length fits in u64
  if bytes.size >= MAX_U64 then
    throw (ErrorCode.E402_OutOfRange "tag length exceeds u64")
  let len := bytes.size.toUInt64
  -- Absorb TYPE_TAG, then absorb_u64(len) per §8.6
  let s1 := absorbFr s TYPE_TAG
  let s2 := absorbU64 s1 len  -- §8.6 step 4: absorb_u64(n)
  -- Absorb tag bytes in 31-byte chunks (raw, no TYPE_BYTES)
  let mut st := s2
  let mut pos := 0
  while pos < bytes.size do
    let chunkEnd := min (pos + 31) bytes.size
    let chunk := bytes.extract pos chunkEnd
    let fr ← frFromU248 chunk
    st := absorbFr st fr
    pos := chunkEnd
  pure st

/-- Absorb a vector of items with TYPE_VEC tag per §8.5.3.

Absorbs: TYPE_VEC, then absorb_u64(len), then each item via provided function. -/
def absorbVec {α : Type} (s : State) (items : Array α)
    (absorbItem : State → α → OracleResult State) : OracleResult State := do
  if items.size >= MAX_U64 then
    throw (ErrorCode.E402_OutOfRange "vector length exceeds u64")
  let len := items.size.toUInt64
  let s1 := absorbFr s TYPE_VEC
  let s2 := absorbU64 s1 len  -- §8.5.3 step 3: absorb_u64(n)
  let mut st := s2
  for item in items do
    st ← absorbItem st item
  pure st

/-- Squeeze a field element challenge.

Finalizes absorption and squeezes one Fr. -/
def challengeFr (s : State) : (Fr × State) :=
  let finalized := s.sponge.finalize
  let (x, sponge') := finalized.squeezeOne
  (x, { s with sponge := sponge', mode := .Squeezing })

/-- Squeeze multiple field element challenges. -/
def challengeFrN (s : State) (n : Nat) : (Array Fr × State) :=
  let finalized := s.sponge.finalize
  let (xs, sponge') := finalized.squeeze n
  (xs, { s with sponge := sponge', mode := .Squeezing })

/-- Initialize transcript per §8.4 TranscriptV1.init().

Per spec:
1. state[0..t-1] := 0
2. mode := ABSORB
3. pos := 0
4. absorb_tag("JOLT/TRANSCRIPT/V1")
5. return transcript

Callers MUST NOT absorb the domain tag again after calling this. -/
def initTranscript (cfg : Poseidon.Config) : OracleResult State := do
  let s := State.init cfg
  absorbTag s "JOLT/TRANSCRIPT/V1"

end Jolt.Transcript
