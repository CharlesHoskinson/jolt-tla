import Jolt.Oracle
import Jolt.Properties

/-!
# Jolt Oracle

Root module for the Jolt Executable Spec Oracle.

This oracle generates conformance test vectors for Jolt zkVM implementations.
Every Jolt implementation must produce identical outputs for identical inputs.

## Module Structure
- `Jolt.Errors` - Error codes
- `Jolt.Field.Fr` - BLS12-381 scalar field
- `Jolt.Encoding.*` - Bytes32, Fr2 encoding
- `Jolt.Util.*` - ASCII, ByteOrder utilities
- `Jolt.JSON.*` - JSON parsing and canonicalization
- `Jolt.Poseidon.*` - Poseidon hash function
- `Jolt.Transcript.*` - Fiat-Shamir transcript
- `Jolt.Registry.*` - Registry validation
- `Jolt.State.*` - VM state and digest
- `Jolt.Wrapper.*` - Wrapper public inputs
- `Jolt.Bundle.*` - Tar archive handling
- `Jolt.Oracle` - Main API
-/
