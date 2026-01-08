import Jolt.Errors
import Jolt.JSON.Types

namespace Jolt.JSON

/-- Maximum safe integer (2^53 - 1). -/
def MAX_SAFE_INT : Int := 9007199254740991

/-- Minimum safe integer (-(2^53 - 1)). -/
def MIN_SAFE_INT : Int := -9007199254740991

/-- DoS protection limits for JSON parsing.

These limits prevent resource exhaustion attacks. Values are chosen to be
generous for legitimate use while blocking obvious attacks. -/
structure Limits where
  /-- Maximum input size in bytes (default: 16 MB) -/
  maxInputSize : Nat := 16 * 1024 * 1024
  /-- Maximum nesting depth for arrays/objects (default: 128) -/
  maxDepth : Nat := 128
  /-- Maximum string length in characters (default: 1 MB) -/
  maxStringLength : Nat := 1024 * 1024
  /-- Maximum number of fields in an object (default: 10000) -/
  maxObjectFields : Nat := 10000
  /-- Maximum number of elements in an array (default: 100000) -/
  maxArrayLength : Nat := 100000
  deriving Repr, Inhabited

namespace Limits

/-- Default limits for production use. -/
def default : Limits := {}

/-- Strict limits for constrained environments. -/
def strict : Limits where
  maxInputSize := 1024 * 1024      -- 1 MB
  maxDepth := 32
  maxStringLength := 65536         -- 64 KB
  maxObjectFields := 1000
  maxArrayLength := 10000

/-- Permissive limits for testing. -/
def permissive : Limits where
  maxInputSize := 256 * 1024 * 1024  -- 256 MB
  maxDepth := 512
  maxStringLength := 16 * 1024 * 1024
  maxObjectFields := 100000
  maxArrayLength := 1000000

end Limits

/-- Check input size against limits. -/
def checkInputSize (size : Nat) (limits : Limits) : OracleResult Unit := do
  if size > limits.maxInputSize then
    throw (ErrorCode.E110_InputTooLarge size limits.maxInputSize)

/-- Check nesting depth against limits. -/
def checkDepth (depth : Nat) (limits : Limits) : OracleResult Unit := do
  if depth > limits.maxDepth then
    throw (ErrorCode.E111_NestingTooDeep depth limits.maxDepth)

/-- Check string length against limits. -/
def checkStringLength (length : Nat) (limits : Limits) : OracleResult Unit := do
  if length > limits.maxStringLength then
    throw (ErrorCode.E112_StringTooLong length limits.maxStringLength)

/-- Check object field count against limits. -/
def checkObjectFields (count : Nat) (limits : Limits) : OracleResult Unit := do
  if count > limits.maxObjectFields then
    throw (ErrorCode.E113_TooManyFields count limits.maxObjectFields)

/-- Check array length against limits. -/
def checkArrayLength (length : Nat) (limits : Limits) : OracleResult Unit := do
  if length > limits.maxArrayLength then
    throw (ErrorCode.E114_ArrayTooLong length limits.maxArrayLength)

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

/-- Check if JSON value contains "TBD" placeholder string (recursive).

Per §3.5: "TBD" sentinel must be detected at any JSON path. -/
partial def containsTBD (v : JsonValue) : Bool :=
  match v with
  | .null => false
  | .bool _ => false
  | .num _ => false
  | .str s => s == "TBD"
  | .arr items => items.any containsTBD
  | .obj fields => fields.any (fun (_, val) => containsTBD val)

/-- Check if string contains only ASCII characters. -/
def isASCIIString (s : String) : Bool := s.all (·.toNat < 128)

end Jolt.JSON
