import Jolt.Errors
import Jolt.Field.Fr
import Jolt.Wrapper.PublicInputs

/-!
# JOLT_WRAPPER_PROOF_SYSTEM_V1

Defines the Midnight-compatible wrapper proof system configuration.

## Compatibility Contract

This module implements types and validation for byte-exact compatibility
with Midnight's native verifier stack:

- Proof system: Plonk-ish / Halo2 with KZG on BLS12-381
- Field encoding: 32-byte little-endian with strict canonicalization
- Transcript: Blake2b (parameters TBD)
- PCS params: 2^14 setup (k=14)
- Public inputs: 11 Fr elements in fixed order

## Wire Format Tags

- Outer proof container: `proof-versioned`
- Inner proof: `proof[v5]`
- Verifier key: `verifier-key[v6]`
- Binding domain: `midnight:binding-input[v1]`

## References

- Jolt Spec §5.2 (Public Inputs)
- Midnight ledger protocol specification
-/

namespace Jolt.Wrapper

/-! ## Proof System Parameters -/

/-- Proof system configuration constants. -/
structure ProofSystemConfig where
  /-- Proof system family identifier -/
  family : String := "Plonk-ish/Halo2"
  /-- Polynomial commitment scheme -/
  pcs : String := "KZG"
  /-- Elliptic curve -/
  curve : String := "BLS12-381"
  /-- Domain size parameter (log2 of domain size) -/
  k : Nat := 14
  /-- Actual domain size (2^k) -/
  domainSize : Nat := 16384
  deriving Repr, DecidableEq

/-- The canonical JOLT_WRAPPER_PROOF_SYSTEM_V1 configuration. -/
def wrapperProofSystemV1 : ProofSystemConfig := {}

/-! ## Wire Format Tags -/

/-- Version tags for proof containers per Midnight ledger format. -/
structure WireFormatTags where
  /-- Outer proof container tag -/
  proofOuter : String := "proof-versioned"
  /-- Inner proof version tag -/
  proofInner : String := "proof[v5]"
  /-- Verifier key version tag -/
  verifierKey : String := "verifier-key[v6]"
  /-- Binding domain separator -/
  bindingDomain : String := "midnight:binding-input[v1]"
  deriving Repr, DecidableEq

/-- The canonical wire format tags. -/
def wireFormatTagsV1 : WireFormatTags := {}

/-! ## Proof Container Types -/

/-- Raw proof bytes with version metadata. -/
structure VersionedProof where
  /-- Version tag (should be "proof[v5]") -/
  versionTag : String
  /-- Raw proof bytes -/
  proofBytes : ByteArray

namespace VersionedProof

/-- Validate that the version tag matches expected. -/
def validateVersion (p : VersionedProof) : OracleResult Unit := do
  if p.versionTag != wireFormatTagsV1.proofInner then
    throw (ErrorCode.E406_InvalidTagFormat s!"expected {wireFormatTagsV1.proofInner}, got {p.versionTag}")

end VersionedProof

/-- Raw verifier key bytes with version metadata. -/
structure VersionedVerifierKey where
  /-- Version tag (should be "verifier-key[v6]") -/
  versionTag : String
  /-- Raw verifier key bytes -/
  vkBytes : ByteArray

namespace VersionedVerifierKey

/-- Validate that the version tag matches expected. -/
def validateVersion (vk : VersionedVerifierKey) : OracleResult Unit := do
  if vk.versionTag != wireFormatTagsV1.verifierKey then
    throw (ErrorCode.E406_InvalidTagFormat s!"expected {wireFormatTagsV1.verifierKey}, got {vk.versionTag}")

end VersionedVerifierKey

/-! ## SRS Parameters -/

/-- SRS (Structured Reference String) identity. -/
structure SRSIdentity where
  /-- Human-readable name -/
  name : String := "bls_midnight_2p14"
  /-- Domain size parameter -/
  k : Nat := 14
  /-- SHA-256 hash of the SRS blob (for verification) -/
  hashSHA256 : Option ByteArray := none  -- TODO(NEEDS_EVIDENCE)

/-- The canonical SRS identity for JOLT_WRAPPER_PROOF_SYSTEM_V1. -/
def srsIdentityV1 : SRSIdentity := {}

/-! ## Public Input Serialization -/

/-- Serialize public inputs to 352 bytes (11 × 32 bytes).

Each Fr element is encoded as 32 bytes little-endian. -/
def serializePublicInputs (pi : PublicInputs) : ByteArray := Id.run do
  let frArray := pi.toArray
  let mut result := ByteArray.empty
  for fr in frArray do
    result := result ++ Fr.toBytes32LE fr
  result

/-- Expected size of serialized public inputs. -/
def publicInputsSerializedSize : Nat := 352  -- 11 × 32 bytes

/-- Validate serialized public inputs have correct length. -/
def validateSerializedPublicInputs (bytes : ByteArray) : OracleResult Unit := do
  if bytes.size != publicInputsSerializedSize then
    throw (ErrorCode.E104_WrongLength publicInputsSerializedSize bytes.size)

/-- Deserialize 352 bytes to public inputs. -/
def deserializePublicInputs (bytes : ByteArray) : OracleResult PublicInputs := do
  validateSerializedPublicInputs bytes
  let mut frArray : Array Fr := #[]
  for i in [:11] do
    let start := i * 32
    let chunk := bytes.extract start (start + 32)
    let fr ← Fr.fromBytes32LECanonical chunk
    frArray := frArray.push fr
  PublicInputs.fromArray frArray

/-! ## Transcript Parameters (Blake2b) -/

/-- Blake2b transcript configuration.

TODO(NEEDS_EVIDENCE): These values need confirmation from Midnight codebase. -/
structure Blake2bTranscriptConfig where
  /-- Hash function -/
  hashFunction : String := "Blake2b"
  /-- Challenge domain separator -/
  challengePrefix : UInt8 := 0x00
  /-- Common data domain separator -/
  commonPrefix : UInt8 := 0x01
  /-- Personalization string (if any) -/
  personalization : Option ByteArray := none  -- TODO(NEEDS_EVIDENCE)

/-- The canonical Blake2b transcript config for JOLT_WRAPPER_PROOF_SYSTEM_V1.

Note: These parameters are placeholders pending confirmation from Midnight code. -/
def blake2bTranscriptConfigV1 : Blake2bTranscriptConfig := {}

/-! ## Binding Input -/

/-- Domain separator for binding public inputs.

Per Midnight ledger rules, public inputs are bound using this domain. -/
def bindingDomainV1 : String := "midnight:binding-input[v1]"

/-! ## Full Configuration Record -/

/-- Complete JOLT_WRAPPER_PROOF_SYSTEM_V1 configuration. -/
structure WrapperProofSystemV1Config where
  proofSystem : ProofSystemConfig := wrapperProofSystemV1
  wireFormat : WireFormatTags := wireFormatTagsV1
  srs : SRSIdentity := srsIdentityV1
  transcript : Blake2bTranscriptConfig := blake2bTranscriptConfigV1
  publicInputsCount : Nat := 11
  bindingDomain : String := bindingDomainV1

/-- The canonical configuration instance. -/
def configV1 : WrapperProofSystemV1Config := {}

/-! ## Validation -/

/-- Validate that a proof system configuration matches V1 expectations. -/
def validateConfig (cfg : WrapperProofSystemV1Config) : OracleResult Unit := do
  -- Check domain size
  if cfg.proofSystem.k != 14 then
    throw (ErrorCode.E402_OutOfRange s!"k must be 14, got {cfg.proofSystem.k}")
  -- Check public inputs count
  if cfg.publicInputsCount != 11 then
    throw (ErrorCode.E402_OutOfRange s!"public inputs must be 11, got {cfg.publicInputsCount}")
  -- Check curve
  if cfg.proofSystem.curve != "BLS12-381" then
    throw (ErrorCode.E400_BindingMismatch s!"curve must be BLS12-381")
  pure ()

end Jolt.Wrapper
