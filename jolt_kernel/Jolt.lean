import Jolt.Logic
import Jolt.Types
import Jolt.Encoding
import Jolt.Transcript
import Jolt.ConfigTags
import Jolt.StateDigest
import Jolt.Wrapper
import Jolt.Continuations
import Jolt.Kernel

/-!
# Jolt Kernel

Minimal auditable Lean 4 kernel for Jolt zkVM.

## Module Structure

* `Jolt.Logic` - Prop-first logic discipline
* `Jolt.Types` - Core types (Fr, Bytes32, Fr2)
* `Jolt.Encoding` - Bytes32 <-> Fr2 encoding
* `Jolt.Transcript` - Poseidon sponge transcript
* `Jolt.ConfigTags` - RFC 8785 JCS config tags
* `Jolt.StateDigest` - 14-step StateDigestV1
* `Jolt.Wrapper` - PublicInputsV1 and binding
* `Jolt.Continuations` - Chunk chaining validation
* `Jolt.Kernel` - Consolidated exports and theorems

## Trusted Computing Base

One constant: `PoseidonPermute`

## References

* Jolt Spec (spec.md)
-/
