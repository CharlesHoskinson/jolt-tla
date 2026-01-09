import Jolt.Errors
import Jolt.Encoding.Bytes32
import Jolt.JSON.Parser
import Jolt.JSON.JCS
import Jolt.Registry.Validate
import Jolt.Registry.ConfigTags
import Jolt.Hash.SHA256

/-!
# Registry Hash Computation

Computes JOLT_PARAMETER_REGISTRY_HASH_V1 per §3.3.

## Algorithm
1. Parse registry.json as JSON
2. Validate: exactly 17 required non-external keys, no external handles
3. Canonicalize via RFC 8785 JCS
4. Compute SHA-256 of canonical bytes

## Main Definitions
* `computeRegistryHash` - Compute registry hash from parsed JSON
* `computeRegistryHashBytes` - Compute registry hash from raw bytes
* `verifyRegistryHash` - Verify registry matches expected hash

## References
* Jolt Spec §3.3: Registry hash definition
* RFC 8785: JSON Canonicalization Scheme
-/

namespace Jolt.Registry

open Jolt.JSON
open Jolt.Hash

/-- Compute JOLT_PARAMETER_REGISTRY_HASH_V1 from parsed registry JSON.

Per §3.3:
- Input MUST be a JSON object with exactly the 17 required non-external keys
- No external handles (REGISTRY_HASH, VK_HASH, CONFORMANCE_HASH) may be present
- Output is SHA-256 of JCS canonical bytes

Returns 32-byte hash as ByteArray. -/
def computeRegistryHash (registry : JsonValue) : OracleResult ByteArray := do
  -- Validate registry structure and content
  let entries ← validateRegistry registry

  -- Verify exactly 17 keys (all required, no extras)
  if entries.size != RequiredNonExternalTags.size then
    throw (ErrorCode.E200_UnknownRegistryKey "wrong number of keys")

  -- Verify all keys are in required set (no unknown keys)
  for entry in entries do
    if !RequiredNonExternalTags.contains entry.key then
      throw (ErrorCode.E200_UnknownRegistryKey entry.key)

  -- Canonicalize via JCS
  let canonical := JCS.canonicalizeBytes registry

  -- Compute SHA-256
  pure (sha256 canonical)

/-- Compute registry hash from raw JSON bytes.

Parses bytes as JSON, validates, and computes hash. -/
def computeRegistryHashBytes (bytes : ByteArray) : OracleResult ByteArray := do
  let json ← parseJSONBytes bytes
  computeRegistryHash json

/-- Compute registry hash and return as Bytes32. -/
def computeRegistryHashBytes32 (registry : JsonValue) : OracleResult Bytes32 := do
  let hash ← computeRegistryHash registry
  Bytes32.ofByteArray hash

/-- Compute registry hash and return as hex string. -/
def computeRegistryHashHex (registry : JsonValue) : OracleResult String := do
  let _ ← computeRegistryHash registry  -- Validate first
  pure (sha256Hex (JCS.canonicalizeBytes registry))

/-- Verify registry hash matches expected value.

Returns true if SHA-256(JCS(registry)) equals expected hash. -/
def verifyRegistryHash (registry : JsonValue) (expected : ByteArray) : OracleResult Bool := do
  let computed ← computeRegistryHash registry
  if computed.size != expected.size then
    pure false
  else
    pure (computed.data == expected.data)

/-- Verify registry hash against expected Bytes32. -/
def verifyRegistryHashBytes32 (registry : JsonValue) (expected : Bytes32) : OracleResult Bool := do
  let computed ← computeRegistryHashBytes32 registry
  pure (computed == expected)

/-- Check if raw bytes are in canonical form and compute hash if valid.

Returns (isCanonical, hash) where:
- isCanonical: true if raw bytes equal JCS canonical form
- hash: SHA-256 of canonical bytes (computed regardless of isCanonical)

Per §3.3: registry.json raw bytes MUST equal canonical form. -/
def checkCanonicalAndHash (bytes : ByteArray) : OracleResult (Bool × ByteArray) := do
  let json ← parseJSONBytes bytes
  let _ ← validateRegistry json  -- Validate structure
  let canonical := JCS.canonicalizeBytes json
  let isCanonical := bytes.data == canonical.data
  let hash := sha256 canonical
  pure (isCanonical, hash)

end Jolt.Registry
