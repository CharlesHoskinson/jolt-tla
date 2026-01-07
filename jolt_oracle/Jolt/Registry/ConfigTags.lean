import Jolt.Errors
import Jolt.State.VMState
import Jolt.Util.ByteOrder

namespace Jolt.Registry

/-- Check if string contains a substring. -/
private def stringContains (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Compare ByteArrays for equality. -/
private def byteArrayEq (a b : ByteArray) : Bool :=
  a.data == b.data

/-- The exact 17 required non-external config tag keys from §3.4. -/
def RequiredNonExternalTags : Array String := #[
  "JOLT_CIRCUIT_FLAGS_V1",
  "JOLT_CONTINUATION_FLAGS_V1",
  "JOLT_FORMAT_VERSION_V1",
  "JOLT_MAX_BYTECODE_SIZE_V1",
  "JOLT_MAX_INPUT_SIZE_V1",
  "JOLT_MAX_OUTPUT_SIZE_V1",
  "JOLT_MEMORY_LAYOUT_V1",
  "JOLT_POSEIDON_FR_V1",
  "JOLT_R1CS_SHAPE_V1",
  "JOLT_RAM_HASH_V1",
  "JOLT_RAM_SIZE_V1",
  "JOLT_RV_EXTENSIONS_V1",
  "JOLT_SPARTAN_SHAPE_V1",
  "JOLT_STEP_BUDGET_V1",
  "JOLT_TRACE_WIDTH_V1",
  "JOLT_WRAPPER_PARAMS_V1",
  "JOLT_WRAPPER_VK_HASH_V1"
]

/-- Check if a key is in the required set. -/
def isRequiredTag (key : String) : Bool :=
  RequiredNonExternalTags.contains key

/-- Check if a key is external (has _EXT_ or ends with _EXT_V*). -/
def isExternalTag (key : String) : Bool :=
  stringContains key "_EXT_"

/-- Project config_tags from a registry object.

Takes a lookup function from key to value bytes.
Errors on missing required keys. -/
def projectConfigTags (lookup : String → Option ByteArray) :
    OracleResult (Array State.ConfigTag) := do
  let mut tags : Array State.ConfigTag := #[]

  for key in RequiredNonExternalTags do
    match lookup key with
    | none =>
      throw (ErrorCode.E202_MissingRequiredKey key)
    | some value =>
      tags := tags.push { name := key.toUTF8, value := value }

  -- Sort by name_bytes (bytewise lexicographic)
  let sorted := sortByBytes State.ConfigTag.nameBytes tags
  pure sorted

/-- Validate config_tags match registry projection.

Compares prover-provided config_tags against fresh projection. -/
def validateConfigTags (provided : Array State.ConfigTag)
    (lookup : String → Option ByteArray) : OracleResult Unit := do
  let expected ← projectConfigTags lookup

  if provided.size != expected.size then
    throw (ErrorCode.E400_BindingMismatch "config_tags count mismatch")

  for i in [:provided.size] do
    let p := provided[i]!
    let e := expected[i]!
    if !byteArrayEq p.name e.name then
      throw (ErrorCode.E400_BindingMismatch s!"config_tag name mismatch at index {i}")
    if !byteArrayEq p.value e.value then
      throw (ErrorCode.E400_BindingMismatch s!"config_tag value mismatch at index {i}")

end Jolt.Registry
