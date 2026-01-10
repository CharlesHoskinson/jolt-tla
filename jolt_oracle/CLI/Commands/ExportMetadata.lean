import Jolt.Errors
import Jolt.Field.Fr
import Jolt.Poseidon.Params
import Jolt.Poseidon.Constants
import CLI.Format.Json

/-!
# Export Metadata Command

Exports oracle metadata as JSON for build.rs codegen in the Rust implementation.

## Output Format

```json
{
  "version": "1",
  "field": {
    "modulus": "<decimal string>",
    "modulus_hex": "<64-char hex string>"
  },
  "errors": [
    {"name": "E100_InvalidJSON", "code": 100, "params": []},
    {"name": "E101_DuplicateKey", "code": 101, "params": ["key"]},
    ...
  ],
  "poseidon": {
    "width": 3,
    "rate": 2,
    "capacity": 1,
    "full_rounds": 8,
    "partial_rounds": 60,
    "sbox_alpha": 5,
    "mds_matrix": [["<hex>", ...], ...],
    "round_constants": [["<hex>", "<hex>", "<hex>"], ...],
    "round_constants_hash": "<sha256 hex>"
  }
}
```

## References
- Transpiler.md: BUILD-001, BUILD-002, BUILD-003, BUILD-004
- Jolt Spec §3.4.1
-/

namespace CLI.Commands

open Jolt
open Jolt.Poseidon
open Jolt.Poseidon.Constants
open CLI.Format

/-- Error code info for metadata export. -/
structure ErrorInfo where
  name : String
  code : Nat
  params : List String
  deriving Repr

/-- Extract error code number from name (E100 -> 100). -/
private def extractErrorCode (name : String) : Nat :=
  -- Parse the number after 'E'
  let parts := name.splitOn "_"
  match parts.head? with
  | some codePrefix =>
    if codePrefix.startsWith "E" then
      let numStr := codePrefix.drop 1
      numStr.toNat?.getD 0
    else 0
  | none => 0

/-- All error codes with their names, codes, and parameter info. -/
def allErrorCodes : List ErrorInfo := [
  -- JSON errors (100-199)
  { name := "E100_InvalidJSON", code := 100, params := [] },
  { name := "E101_DuplicateKey", code := 101, params := ["key"] },
  { name := "E102_InvalidBase64", code := 102, params := [] },
  { name := "E103_InvalidHex", code := 103, params := [] },
  { name := "E104_WrongLength", code := 104, params := ["expected", "got"] },
  { name := "E105_InvalidUTF8", code := 105, params := [] },
  { name := "E106_UnexpectedType", code := 106, params := ["expected"] },
  { name := "E107_ExponentNotation", code := 107, params := [] },
  { name := "E108_FractionalNumber", code := 108, params := [] },
  { name := "E109_IntegerOutOfRange", code := 109, params := [] },
  { name := "E110_InputTooLarge", code := 110, params := ["size", "limit"] },
  { name := "E111_NestingTooDeep", code := 111, params := ["depth", "limit"] },
  { name := "E112_StringTooLong", code := 112, params := ["length", "limit"] },
  { name := "E113_TooManyFields", code := 113, params := ["count", "limit"] },
  { name := "E114_ArrayTooLong", code := 114, params := ["length", "limit"] },
  { name := "E115_NonASCIICharacter", code := 115, params := ["codepoint"] },
  -- Registry errors (200-299)
  { name := "E200_UnknownRegistryKey", code := 200, params := ["key"] },
  { name := "E201_ExternalHandlePresent", code := 201, params := ["key"] },
  { name := "E202_MissingRequiredKey", code := 202, params := ["key"] },
  { name := "E203_TBDValuePresent", code := 203, params := ["key"] },
  { name := "E204_InvalidRegistryHash", code := 204, params := [] },
  { name := "E205_NonCanonicalJSON", code := 205, params := [] },
  { name := "E206_InvalidKeyFormat", code := 206, params := ["key"] },
  -- Field errors (300-399)
  { name := "E300_NonCanonicalFr", code := 300, params := ["value"] },
  { name := "E301_Fr2LoBoundsViolation", code := 301, params := [] },
  { name := "E302_Fr2HiBoundsViolation", code := 302, params := [] },
  { name := "E303_InvalidFrEncoding", code := 303, params := [] },
  -- State errors (400-499)
  { name := "E400_BindingMismatch", code := 400, params := ["field"] },
  { name := "E401_OrderingViolation", code := 401, params := ["context"] },
  { name := "E402_OutOfRange", code := 402, params := ["field"] },
  { name := "E403_ReservedNonZero", code := 403, params := ["field"] },
  { name := "E404_InvalidHalted", code := 404, params := [] },
  { name := "E405_TerminationInvariant", code := 405, params := ["context"] },
  { name := "E406_InvalidTagFormat", code := 406, params := ["reason"] },
  { name := "E407_RegisterX0NonZero", code := 407, params := ["value"] },
  -- Chain errors (500-599)
  { name := "E500_ChainBreak", code := 500, params := ["index"] },
  { name := "E501_DigestMismatch", code := 501, params := ["index"] },
  { name := "E502_InvalidChunkIndex", code := 502, params := [] },
  { name := "E503_EmptyChain", code := 503, params := [] },
  -- Hash errors (600-699)
  { name := "E600_HashMismatch", code := 600, params := ["context"] },
  { name := "E601_CommitmentMismatch", code := 601, params := [] },
  { name := "E602_TranscriptMismatch", code := 602, params := [] },
  -- Tar errors (700-799)
  { name := "E700_NonCanonicalTar", code := 700, params := [] },
  { name := "E701_InvalidTarHeader", code := 701, params := ["reason"] },
  { name := "E702_UnsortedMembers", code := 702, params := [] },
  { name := "E703_NonZeroMtime", code := 703, params := [] },
  { name := "E704_InvalidPath", code := 704, params := ["reason"] },
  { name := "E705_DuplicateMember", code := 705, params := [] },
  { name := "E706_InvalidMemberType", code := 706, params := [] },
  { name := "E707_PAXExtensionPresent", code := 707, params := [] },
  { name := "E708_MissingRegistryJson", code := 708, params := [] }
]

/-- Format error info as JSON object. -/
private def formatErrorInfo (e : ErrorInfo) : String :=
  let paramsJson := jsonArray (e.params.map jsonString)
  jsonObject [
    ("name", jsonString e.name),
    ("code", jsonNat e.code),
    ("params", paramsJson)
  ]

/-- Convert a Nat to 64-char hex string (little-endian 32 bytes). -/
private def natToHex64LE (n : Nat) : String := Id.run do
  let mut result := ""
  let mut val := n
  for _ in [:32] do
    let b := val % 256
    let hi := if b / 16 < 10 then Char.ofNat ('0'.toNat + b / 16)
              else Char.ofNat ('a'.toNat + b / 16 - 10)
    let lo := if b % 16 < 10 then Char.ofNat ('0'.toNat + b % 16)
              else Char.ofNat ('a'.toNat + b % 16 - 10)
    result := result.push hi
    result := result.push lo
    val := val / 256
  result

/-- Format field metadata as JSON. -/
private def formatFieldMetadata : String :=
  let modulusDecimal := toString Fr.modulus
  let modulusHex := natToHex64LE Fr.modulus
  jsonObject [
    ("modulus", jsonString modulusDecimal),
    ("modulus_hex", jsonString modulusHex)
  ]

/-- Format MDS matrix as JSON (array of arrays of hex strings). -/
private def formatMdsMatrix : String :=
  let rows := #[
    #[MDS_0_0_HEX, MDS_0_1_HEX, MDS_0_2_HEX],
    #[MDS_1_0_HEX, MDS_1_1_HEX, MDS_1_2_HEX],
    #[MDS_2_0_HEX, MDS_2_1_HEX, MDS_2_2_HEX]
  ]
  let rowsJson := rows.toList.map fun row =>
    jsonArray (row.toList.map jsonString)
  jsonArray rowsJson

/-- Format round constants as JSON (array of 68 arrays, each with 3 hex strings). -/
private def formatRoundConstants : String :=
  let roundsJson := roundConstantsHex.toList.map fun round =>
    jsonArray (round.toList.map jsonString)
  jsonArray roundsJson

/-- Format Poseidon metadata as JSON. -/
private def formatPoseidonMetadata : String :=
  jsonObject [
    ("width", jsonNat POSEIDON_WIDTH),
    ("rate", jsonNat POSEIDON_RATE),
    ("capacity", jsonNat POSEIDON_CAPACITY),
    ("full_rounds", jsonNat POSEIDON_FULL_ROUNDS),
    ("partial_rounds", jsonNat POSEIDON_PARTIAL_ROUNDS),
    ("sbox_alpha", jsonNat POSEIDON_SBOX_ALPHA),
    ("mds_matrix", formatMdsMatrix),
    ("round_constants", formatRoundConstants),
    ("round_constants_hash", jsonString ROUND_CONSTANTS_HASH)
  ]

/-- Generate full metadata JSON. -/
def generateMetadataJson : String :=
  let errorsJson := jsonArray (allErrorCodes.map formatErrorInfo)
  jsonObject [
    ("version", jsonString "1"),
    ("field", formatFieldMetadata),
    ("errors", errorsJson),
    ("poseidon", formatPoseidonMetadata)
  ]

/-- Main entry point for export-metadata command. -/
def exportMetadataMain (_args : List String) : IO UInt32 := do
  IO.println (generateMetadataJson ++ "\n")
  return 0

end CLI.Commands
