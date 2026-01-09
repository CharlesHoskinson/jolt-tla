/-!
# Error Codes

All error codes for the Jolt Oracle. Each represents a specific spec violation
that must be detected and reported consistently.

## Main Definitions
* `ErrorCode` - Enumeration of all oracle error codes
* `OracleResult` - Alias for `Except ErrorCode`

## References
* Jolt Spec §2-14 (various validation requirements)
-/

namespace Jolt

/-- All error codes for the Jolt Oracle.

Error codes are stable identifiers for conformance testing. Each represents
a specific spec violation that must be detected. -/
inductive ErrorCode where
  -- JSON errors (100-199)
  | E100_InvalidJSON
  | E101_DuplicateKey (key : String)
  | E102_InvalidBase64
  | E103_InvalidHex
  | E104_WrongLength (expected got : Nat)
  | E105_InvalidUTF8
  | E106_UnexpectedType (expected : String)
  | E107_ExponentNotation
  | E108_FractionalNumber
  | E109_IntegerOutOfRange
  | E110_InputTooLarge (size limit : Nat)
  | E111_NestingTooDeep (depth limit : Nat)
  | E112_StringTooLong (length limit : Nat)
  | E113_TooManyFields (count limit : Nat)
  | E114_ArrayTooLong (length limit : Nat)
  | E115_NonASCIICharacter (codepoint : Nat)
  -- Registry errors (200-299)
  | E200_UnknownRegistryKey (key : String)
  | E201_ExternalHandlePresent (key : String)
  | E202_MissingRequiredKey (key : String)
  | E203_TBDValuePresent (key : String)
  | E204_InvalidRegistryHash
  | E205_NonCanonicalJSON
  | E206_InvalidKeyFormat (key : String)
  -- Field errors (300-399)
  | E300_NonCanonicalFr (value : String)
  | E301_Fr2LoBoundsViolation
  | E302_Fr2HiBoundsViolation
  | E303_InvalidFrEncoding
  -- State errors (400-499)
  | E400_BindingMismatch (field : String)
  | E401_OrderingViolation (context : String)
  | E402_OutOfRange (field : String)
  | E403_ReservedNonZero (field : String)
  | E404_InvalidHalted
  | E405_TerminationInvariant (context : String)
  | E406_InvalidTagFormat (reason : String)
  | E407_RegisterX0NonZero (value : UInt64)
  -- Chain errors (500-599)
  | E500_ChainBreak (index : Nat)
  | E501_DigestMismatch (index : Nat)
  | E502_InvalidChunkIndex
  | E503_EmptyChain
  -- Hash errors (600-699)
  | E600_HashMismatch (context : String)
  | E601_CommitmentMismatch
  | E602_TranscriptMismatch
  -- Tar errors (700-799)
  | E700_NonCanonicalTar
  | E701_InvalidTarHeader (reason : String)
  | E702_UnsortedMembers
  | E703_NonZeroMtime
  | E704_InvalidPath (reason : String)
  | E705_DuplicateMember
  | E706_InvalidMemberType
  | E707_PAXExtensionPresent
  | E708_MissingRegistryJson
  deriving DecidableEq, Inhabited

instance : Repr ErrorCode where
  reprPrec e _ := match e with
    | .E100_InvalidJSON => "E100_InvalidJSON"
    | .E101_DuplicateKey k => s!"E101_DuplicateKey({k})"
    | .E102_InvalidBase64 => "E102_InvalidBase64"
    | .E103_InvalidHex => "E103_InvalidHex"
    | .E104_WrongLength exp got => s!"E104_WrongLength({exp}, {got})"
    | .E105_InvalidUTF8 => "E105_InvalidUTF8"
    | .E106_UnexpectedType exp => s!"E106_UnexpectedType({exp})"
    | .E107_ExponentNotation => "E107_ExponentNotation"
    | .E108_FractionalNumber => "E108_FractionalNumber"
    | .E109_IntegerOutOfRange => "E109_IntegerOutOfRange"
    | .E110_InputTooLarge s l => s!"E110_InputTooLarge({s}, limit={l})"
    | .E111_NestingTooDeep d l => s!"E111_NestingTooDeep({d}, limit={l})"
    | .E112_StringTooLong len l => s!"E112_StringTooLong({len}, limit={l})"
    | .E113_TooManyFields c l => s!"E113_TooManyFields({c}, limit={l})"
    | .E114_ArrayTooLong len l => s!"E114_ArrayTooLong({len}, limit={l})"
    | .E115_NonASCIICharacter cp => s!"E115_NonASCIICharacter(U+{Nat.toDigits 16 cp})"
    | .E200_UnknownRegistryKey k => s!"E200_UnknownRegistryKey({k})"
    | .E201_ExternalHandlePresent k => s!"E201_ExternalHandlePresent({k})"
    | .E202_MissingRequiredKey k => s!"E202_MissingRequiredKey({k})"
    | .E203_TBDValuePresent k => s!"E203_TBDValuePresent({k})"
    | .E204_InvalidRegistryHash => "E204_InvalidRegistryHash"
    | .E205_NonCanonicalJSON => "E205_NonCanonicalJSON"
    | .E206_InvalidKeyFormat k => s!"E206_InvalidKeyFormat({k})"
    | .E300_NonCanonicalFr v => s!"E300_NonCanonicalFr({v})"
    | .E301_Fr2LoBoundsViolation => "E301_Fr2LoBoundsViolation"
    | .E302_Fr2HiBoundsViolation => "E302_Fr2HiBoundsViolation"
    | .E303_InvalidFrEncoding => "E303_InvalidFrEncoding"
    | .E400_BindingMismatch f => s!"E400_BindingMismatch({f})"
    | .E401_OrderingViolation c => s!"E401_OrderingViolation({c})"
    | .E402_OutOfRange f => s!"E402_OutOfRange({f})"
    | .E403_ReservedNonZero f => s!"E403_ReservedNonZero({f})"
    | .E404_InvalidHalted => "E404_InvalidHalted"
    | .E405_TerminationInvariant c => s!"E405_TerminationInvariant({c})"
    | .E406_InvalidTagFormat r => s!"E406_InvalidTagFormat({r})"
    | .E407_RegisterX0NonZero v => s!"E407_RegisterX0NonZero({v})"
    | .E500_ChainBreak i => s!"E500_ChainBreak({i})"
    | .E501_DigestMismatch i => s!"E501_DigestMismatch({i})"
    | .E502_InvalidChunkIndex => "E502_InvalidChunkIndex"
    | .E503_EmptyChain => "E503_EmptyChain"
    | .E600_HashMismatch c => s!"E600_HashMismatch({c})"
    | .E601_CommitmentMismatch => "E601_CommitmentMismatch"
    | .E602_TranscriptMismatch => "E602_TranscriptMismatch"
    | .E700_NonCanonicalTar => "E700_NonCanonicalTar"
    | .E701_InvalidTarHeader r => s!"E701_InvalidTarHeader({r})"
    | .E702_UnsortedMembers => "E702_UnsortedMembers"
    | .E703_NonZeroMtime => "E703_NonZeroMtime"
    | .E704_InvalidPath r => s!"E704_InvalidPath({r})"
    | .E705_DuplicateMember => "E705_DuplicateMember"
    | .E706_InvalidMemberType => "E706_InvalidMemberType"
    | .E707_PAXExtensionPresent => "E707_PAXExtensionPresent"
    | .E708_MissingRegistryJson => "E708_MissingRegistryJson"

/-- Result type for oracle operations. -/
abbrev OracleResult (α : Type) := Except ErrorCode α

end Jolt
