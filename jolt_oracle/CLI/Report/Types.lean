import Jolt.Errors
import Jolt.Field.Fr
import Jolt.Encoding.Bytes32

/-!
# CLI Report Types

Domain data structures for CLI reports.
Separates report data from presentation/rendering.

## Main Definitions
* `ExitCode` - CLI exit codes matching shell conventions
* `Status` - Health/verification status vocabulary
* `DigestReport` - Result of digest computation
* `ChainReport` - Result of chain verification
* `TestReport` - Result of test vector execution
-/

namespace CLI.Report

open Jolt

/-- CLI exit codes.

| Code | Status | When |
|------|--------|------|
| 0 | HEALTHY / VERIFIED | All checks pass |
| 2 | DEGRADED | Warnings present (with --fail-on=degraded) |
| 3 | UNHEALTHY / MISMATCH | Verification failed, hard failures |
| 4 | INVALID | Bad input JSON, missing fields, schema error |
| 5 | IO_ERROR | File not found, permission denied |

Note: Code 1 is reserved (shell conventions). -/
inductive ExitCode where
  | success       -- 0
  | degraded      -- 2
  | unhealthy     -- 3
  | invalid       -- 4
  | ioError       -- 5
  deriving Repr, BEq, Inhabited

namespace ExitCode

/-- Convert to UInt32 for process exit. -/
def toUInt32 : ExitCode → UInt32
  | .success => 0
  | .degraded => 2
  | .unhealthy => 3
  | .invalid => 4
  | .ioError => 5

end ExitCode

/-- Health status (controlled vocabulary). -/
inductive HealthStatus where
  | healthy
  | degraded
  | unhealthy
  deriving Repr, BEq, Inhabited

/-- Verification status (controlled vocabulary). -/
inductive VerifyStatus where
  | verified
  | mismatch
  | unknown
  deriving Repr, BEq, Inhabited

/-- Validity status (controlled vocabulary). -/
inductive ValidStatus where
  | valid
  | invalid
  deriving Repr, BEq, Inhabited

/-- Freshness status (controlled vocabulary). -/
inductive FreshStatus where
  | fresh
  | stale
  deriving Repr, BEq, Inhabited

/-- Result of a digest computation. -/
structure DigestReport where
  /-- Computed digest as Fr -/
  digest : Fr
  /-- Program hash (for context) -/
  programHash : Bytes32
  /-- Optional timing in microseconds -/
  timingUs : Option Nat := none
  deriving Repr

/-- Result of chain verification. -/
structure ChainReport where
  /-- Overall verification status -/
  status : VerifyStatus
  /-- Number of chunks verified -/
  chunksVerified : Nat
  /-- Error (if mismatch) -/
  error : Option ErrorCode := none
  /-- Failed chunk index (if mismatch) -/
  failedChunkIndex : Option Nat := none
  /-- Optional timing in microseconds -/
  timingUs : Option Nat := none
  deriving Repr

/-- Result of a single test vector. -/
structure TestVectorResult where
  /-- Test name -/
  name : String
  /-- Whether the test passed -/
  passed : Bool
  /-- Expected value (for reporting mismatches) -/
  expected : Option String := none
  /-- Actual value (for reporting mismatches) -/
  actual : Option String := none
  deriving Repr, Inhabited

/-- Result of test vector execution. -/
structure TestReport where
  /-- Number of tests passed -/
  passed : Nat
  /-- Number of tests failed -/
  failed : Nat
  /-- Individual results -/
  results : Array TestVectorResult
  /-- Optional timing in microseconds -/
  timingUs : Option Nat := none
  deriving Repr

/-- An error with context for display. -/
structure ErrorReport where
  /-- Error code -/
  code : ErrorCode
  /-- Human-readable message -/
  message : String
  /-- JSON path to error location (if applicable) -/
  path : Option String := none
  deriving Repr

/-- Create error report from error code. -/
def ErrorReport.fromCode (code : ErrorCode) : ErrorReport :=
  { code := code
    message := errorMessage code
    path := none }
where
  /-- Get human-readable message for error code. -/
  errorMessage : ErrorCode → String
    | .E100_InvalidJSON => "Invalid JSON syntax"
    | .E101_DuplicateKey k => s!"Duplicate key: {k}"
    | .E102_InvalidBase64 => "Invalid base64 encoding"
    | .E103_InvalidHex => "Invalid hexadecimal encoding"
    | .E104_WrongLength exp got => s!"Expected length {exp}, got {got}"
    | .E105_InvalidUTF8 => "Invalid UTF-8 encoding"
    | .E106_UnexpectedType exp => s!"Expected type: {exp}"
    | .E107_ExponentNotation => "Exponent notation not allowed"
    | .E108_FractionalNumber => "Fractional numbers not allowed"
    | .E109_IntegerOutOfRange => "Integer out of range (must be ±2^53-1)"
    | .E110_InputTooLarge s l => s!"Input too large ({s} bytes, limit {l})"
    | .E111_NestingTooDeep d l => s!"Nesting too deep ({d}, limit {l})"
    | .E112_StringTooLong len l => s!"String too long ({len} chars, limit {l})"
    | .E113_TooManyFields c l => s!"Too many fields ({c}, limit {l})"
    | .E114_ArrayTooLong len l => s!"Array too long ({len}, limit {l})"
    | .E115_NonASCIICharacter cp => s!"Non-ASCII character (codepoint {cp})"
    | .E200_UnknownRegistryKey k => s!"Unknown registry key: {k}"
    | .E201_ExternalHandlePresent k => s!"External handle present: {k}"
    | .E202_MissingRequiredKey k => s!"Missing required key: {k}"
    | .E203_TBDValuePresent k => s!"TBD value present: {k}"
    | .E204_InvalidRegistryHash => "Invalid registry hash"
    | .E205_NonCanonicalJSON => "Non-canonical JSON (keys must be sorted)"
    | .E206_InvalidKeyFormat k => s!"Invalid key format: {k}"
    | .E300_NonCanonicalFr v => s!"Non-canonical Fr value: {v}"
    | .E301_Fr2LoBoundsViolation => "Fr2 lo component exceeds 2^248 - 1"
    | .E302_Fr2HiBoundsViolation => "Fr2 hi component exceeds 255"
    | .E303_InvalidFrEncoding => "Invalid Fr encoding"
    | .E400_BindingMismatch f => s!"Binding mismatch: {f}"
    | .E401_OrderingViolation c => s!"Ordering violation: {c}"
    | .E402_OutOfRange f => s!"Value out of range: {f}"
    | .E403_ReservedNonZero f => s!"Reserved field must be zero: {f}"
    | .E404_InvalidHalted => "halted must be 0 or 1"
    | .E405_TerminationInvariant c => s!"Termination invariant violated: {c}"
    | .E406_InvalidTagFormat r => s!"Invalid tag format: {r}"
    | .E407_RegisterX0NonZero v => s!"Register x0 must be zero, got {v}"
    | .E500_ChainBreak i => s!"Chain break at chunk {i}"
    | .E501_DigestMismatch i => s!"Digest mismatch at chunk {i}"
    | .E502_InvalidChunkIndex => "Invalid chunk index"
    | .E503_EmptyChain => "Chain cannot be empty"
    | .E600_HashMismatch c => s!"Hash mismatch: {c}"
    | .E601_CommitmentMismatch => "Commitment mismatch"
    | .E602_TranscriptMismatch => "Transcript mismatch"
    | .E700_NonCanonicalTar => "Non-canonical tar archive"
    | .E701_InvalidTarHeader => "Invalid tar header"
    | .E702_UnsortedMembers => "Tar members must be bytewise sorted"
    | .E703_NonZeroMtime => "Tar mtime must be zero"
    | .E704_InvalidPath r => s!"Invalid path: {r}"
    | .E705_DuplicateMember => "Duplicate tar member"
    | .E706_InvalidMemberType => "Invalid tar member type"
    | .E707_PAXExtensionPresent => "PAX extension headers not allowed"

/-- Get error code string (e.g., "E404_InvalidHalted"). -/
def ErrorReport.codeString (e : ErrorReport) : String :=
  match e.code with
  | .E100_InvalidJSON => "E100_InvalidJSON"
  | .E101_DuplicateKey _ => "E101_DuplicateKey"
  | .E102_InvalidBase64 => "E102_InvalidBase64"
  | .E103_InvalidHex => "E103_InvalidHex"
  | .E104_WrongLength _ _ => "E104_WrongLength"
  | .E105_InvalidUTF8 => "E105_InvalidUTF8"
  | .E106_UnexpectedType _ => "E106_UnexpectedType"
  | .E107_ExponentNotation => "E107_ExponentNotation"
  | .E108_FractionalNumber => "E108_FractionalNumber"
  | .E109_IntegerOutOfRange => "E109_IntegerOutOfRange"
  | .E110_InputTooLarge _ _ => "E110_InputTooLarge"
  | .E111_NestingTooDeep _ _ => "E111_NestingTooDeep"
  | .E112_StringTooLong _ _ => "E112_StringTooLong"
  | .E113_TooManyFields _ _ => "E113_TooManyFields"
  | .E114_ArrayTooLong _ _ => "E114_ArrayTooLong"
  | .E115_NonASCIICharacter _ => "E115_NonASCIICharacter"
  | .E200_UnknownRegistryKey _ => "E200_UnknownRegistryKey"
  | .E201_ExternalHandlePresent _ => "E201_ExternalHandlePresent"
  | .E202_MissingRequiredKey _ => "E202_MissingRequiredKey"
  | .E203_TBDValuePresent _ => "E203_TBDValuePresent"
  | .E204_InvalidRegistryHash => "E204_InvalidRegistryHash"
  | .E205_NonCanonicalJSON => "E205_NonCanonicalJSON"
  | .E206_InvalidKeyFormat _ => "E206_InvalidKeyFormat"
  | .E300_NonCanonicalFr _ => "E300_NonCanonicalFr"
  | .E301_Fr2LoBoundsViolation => "E301_Fr2LoBoundsViolation"
  | .E302_Fr2HiBoundsViolation => "E302_Fr2HiBoundsViolation"
  | .E303_InvalidFrEncoding => "E303_InvalidFrEncoding"
  | .E400_BindingMismatch _ => "E400_BindingMismatch"
  | .E401_OrderingViolation _ => "E401_OrderingViolation"
  | .E402_OutOfRange _ => "E402_OutOfRange"
  | .E403_ReservedNonZero _ => "E403_ReservedNonZero"
  | .E404_InvalidHalted => "E404_InvalidHalted"
  | .E405_TerminationInvariant _ => "E405_TerminationInvariant"
  | .E406_InvalidTagFormat _ => "E406_InvalidTagFormat"
  | .E407_RegisterX0NonZero _ => "E407_RegisterX0NonZero"
  | .E500_ChainBreak _ => "E500_ChainBreak"
  | .E501_DigestMismatch _ => "E501_DigestMismatch"
  | .E502_InvalidChunkIndex => "E502_InvalidChunkIndex"
  | .E503_EmptyChain => "E503_EmptyChain"
  | .E600_HashMismatch _ => "E600_HashMismatch"
  | .E601_CommitmentMismatch => "E601_CommitmentMismatch"
  | .E602_TranscriptMismatch => "E602_TranscriptMismatch"
  | .E700_NonCanonicalTar => "E700_NonCanonicalTar"
  | .E701_InvalidTarHeader => "E701_InvalidTarHeader"
  | .E702_UnsortedMembers => "E702_UnsortedMembers"
  | .E703_NonZeroMtime => "E703_NonZeroMtime"
  | .E704_InvalidPath _ => "E704_InvalidPath"
  | .E705_DuplicateMember => "E705_DuplicateMember"
  | .E706_InvalidMemberType => "E706_InvalidMemberType"
  | .E707_PAXExtensionPresent => "E707_PAXExtensionPresent"

/-- Map error code to exit code. -/
def exitCodeForError (code : ErrorCode) : ExitCode :=
  match code with
  -- JSON/input errors → INVALID
  | .E100_InvalidJSON | .E101_DuplicateKey _ | .E102_InvalidBase64
  | .E103_InvalidHex | .E104_WrongLength _ _ | .E105_InvalidUTF8
  | .E106_UnexpectedType _ | .E107_ExponentNotation | .E108_FractionalNumber
  | .E109_IntegerOutOfRange | .E110_InputTooLarge _ _ | .E111_NestingTooDeep _ _
  | .E112_StringTooLong _ _ | .E113_TooManyFields _ _ | .E114_ArrayTooLong _ _
  | .E115_NonASCIICharacter _ => .invalid
  -- Registry errors → INVALID
  | .E200_UnknownRegistryKey _ | .E201_ExternalHandlePresent _
  | .E202_MissingRequiredKey _ | .E203_TBDValuePresent _
  | .E204_InvalidRegistryHash | .E205_NonCanonicalJSON
  | .E206_InvalidKeyFormat _ => .invalid
  -- Field errors → INVALID
  | .E300_NonCanonicalFr _ | .E301_Fr2LoBoundsViolation
  | .E302_Fr2HiBoundsViolation | .E303_InvalidFrEncoding => .invalid
  -- State errors → INVALID (input) or UNHEALTHY (verification)
  | .E400_BindingMismatch _ | .E401_OrderingViolation _
  | .E402_OutOfRange _ | .E403_ReservedNonZero _
  | .E404_InvalidHalted | .E405_TerminationInvariant _
  | .E406_InvalidTagFormat _ | .E407_RegisterX0NonZero _ => .invalid
  -- Chain/verification errors → UNHEALTHY
  | .E500_ChainBreak _ | .E501_DigestMismatch _
  | .E502_InvalidChunkIndex | .E503_EmptyChain => .unhealthy
  -- Hash errors → UNHEALTHY
  | .E600_HashMismatch _ | .E601_CommitmentMismatch
  | .E602_TranscriptMismatch => .unhealthy
  -- Tar errors → INVALID
  | .E700_NonCanonicalTar | .E701_InvalidTarHeader
  | .E702_UnsortedMembers | .E703_NonZeroMtime
  | .E704_InvalidPath _ | .E705_DuplicateMember
  | .E706_InvalidMemberType | .E707_PAXExtensionPresent => .invalid

end CLI.Report
