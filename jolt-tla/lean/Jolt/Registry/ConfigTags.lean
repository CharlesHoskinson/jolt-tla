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

/-- The exact 17 required non-external config tag keys from §3.4.

These are the ONLY keys that MUST appear in registry.json.
External handles (JOLT_PARAMETER_REGISTRY_HASH_V1, JOLT_WRAPPER_VK_HASH_V1,
JOLT_CONFORMANCE_BUNDLE_HASH_V1) MUST NOT appear in registry.json.

Grouped by purpose:
- Cryptographic Core: POSEIDON, PCS, TRANSCRIPT_SCHEDULE
- Guest VM: RISCV_PROFILE, RISCV_UNPRIV_SPEC, GUEST_MEMMAP, TOOLCHAIN
- DoS Caps: MAX_MANIFEST_BYTES, MAX_INTENTS, MAX_CHECKPOINTS_BYTES
- Encoding Formats: BATCH_MANIFEST_ENCODING, BATCH_COMMITMENT, CHECKPOINTS_ENCODING
- Deployment Binding: CONTEXT_BYTES32
- Execution Config: CONTINUATIONS
- Implementation Identity: IMPL_COMMIT, WRAPPER_PROOF_SYSTEM -/
def RequiredNonExternalTags : Array String := #[
  -- Cryptographic Core (§3.4)
  "JOLT_POSEIDON_FR_V1",
  "JOLT_PCS_V1",
  "JOLT_TRANSCRIPT_SCHEDULE_V1",
  -- Guest VM Configuration (§3.4)
  "JOLT_RISCV_PROFILE_V1",
  "JOLT_RISCV_UNPRIV_SPEC_V1",
  "JOLT_GUEST_MEMMAP_V1",
  "JOLT_TOOLCHAIN_V1",
  -- DoS Caps (§3.4)
  "JOLT_MAX_MANIFEST_BYTES_V1",
  "JOLT_MAX_INTENTS_V1",
  "JOLT_MAX_CHECKPOINTS_BYTES_V1",
  -- Encoding Formats (§3.4)
  "JOLT_BATCH_MANIFEST_ENCODING_V1",
  "JOLT_BATCH_COMMITMENT_V1",
  "JOLT_CHECKPOINTS_ENCODING_V1",
  -- Deployment Binding (§3.4)
  "JOLT_CONTEXT_BYTES32_V1",
  -- Execution Configuration (§3.4)
  "JOLT_CONTINUATIONS_V1",
  -- Implementation Identity (§3.4)
  "JOLT_IMPL_COMMIT_V1",
  "JOLT_WRAPPER_PROOF_SYSTEM_V1"
]

/-- External handles that MUST NOT appear in registry.json per §3.3.

These are published alongside registry.json, not inside it:
- JOLT_PARAMETER_REGISTRY_HASH_V1: SHA-256 of the registry (circular)
- JOLT_WRAPPER_VK_HASH_V1: Depends on registry contents
- JOLT_CONFORMANCE_BUNDLE_HASH_V1: Bundle includes the registry -/
def ExternalHandleTags : Array String := #[
  "JOLT_PARAMETER_REGISTRY_HASH_V1",
  "JOLT_WRAPPER_VK_HASH_V1",
  "JOLT_CONFORMANCE_BUNDLE_HASH_V1"
]

/-- Check if a key is in the required set. -/
def isRequiredTag (key : String) : Bool :=
  RequiredNonExternalTags.contains key

/-- Check if a key is an external handle per §3.3. -/
def isExternalTag (key : String) : Bool :=
  ExternalHandleTags.contains key

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
