import Jolt.Errors
import Jolt.JSON.Types

namespace Jolt.JSON

/-- Maximum safe integer (2^53 - 1). -/
def MAX_SAFE_INT : Int := 9007199254740991

/-- Minimum safe integer (-(2^53 - 1)). -/
def MIN_SAFE_INT : Int := -9007199254740991

/-- Helper to get byte from ByteArray. -/
private def getByte (bytes : ByteArray) (i : Nat) : UInt8 :=
  if i < bytes.size then bytes.data[i]! else 0

/-- Check if bytes start with UTF-8 BOM. -/
def hasBOM (bytes : ByteArray) : Bool :=
  bytes.size >= 3 &&
  getByte bytes 0 == 0xEF &&
  getByte bytes 1 == 0xBB &&
  getByte bytes 2 == 0xBF

/-- Check if string contains a substring. -/
def stringContains (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Validate a number token against spec restrictions. -/
def validateNumberToken (raw : String) (value : Int) : OracleResult Unit := do
  if stringContains raw "e" || stringContains raw "E" then
    throw ErrorCode.E107_ExponentNotation
  if stringContains raw "." then
    throw ErrorCode.E108_FractionalNumber
  if value > MAX_SAFE_INT || value < MIN_SAFE_INT then
    throw ErrorCode.E109_IntegerOutOfRange

/-- Check if JSON value contains "TBD" placeholder string (non-recursive). -/
def containsTBD (v : JsonValue) : Bool :=
  match v with
  | .str s => s == "TBD"
  | _ => false  -- Simplified: only check top-level strings

/-- Check if string contains only ASCII characters. -/
def isASCIIString (s : String) : Bool := s.all (·.toNat < 128)

end Jolt.JSON
