import NearFall.Types
import NearFall.Encoding
import NearFall.Transcript
import NearFall.TLATypes
import NearFall.SMT
import NearFall.VMState
import NearFall.Continuations
import NearFall.Invariants
import NearFall.Checker
import NearFall.Soundness

/-!
# NearFall.Basic

Basic definitions and re-exports for the NearFall kernel.

## Main Definitions
* `NearFall.version` - Kernel version string

## Modules
* `NearFall.Types` - Core type definitions
* `NearFall.Encoding` - Canonical encoding with injectivity proofs
* `NearFall.Transcript` - Fiat-Shamir transcript with domain separation
* `NearFall.TLATypes` - TLA+ primitive type alignment
* `NearFall.SMT` - Sparse Merkle Tree types and axioms
* `NearFall.VMState` - Full VMStateV1 modeling (8 fields)
* `NearFall.Continuations` - ChunkRecord, StateDigest, continuation mechanics
* `NearFall.Invariants` - All 29 TLA+ invariants
* `NearFall.Checker` - Trace checker with 13 decidable invariant checks
* `NearFall.Soundness` - Soundness theorem with 10 axioms

## Axiom Count: 10
1. smt_root_binding
2. smt_collision_resistant
3. encode_event_injective
4. decode_encode_event
5. continuation_chunk_bound
6. public_inputs_correctly_assembled
7. status_ok_implies_exit_ok
8. state_digest_deterministic
9. state_digest_collision_resistant
10. transcript_collision_resistant

## Invariant Coverage: 29
- TYPE: 4 invariants
- BIND: 10 invariants (critical) - includes 3 security review additions
- SAFE: 7 invariants
- ATK: 8 invariants (attack prevention)

## Implementation Notes
This module serves as an entry point. Import this module to get
access to all NearFall definitions.

## References
* Jolt Spec §1-§15
* jolt-tla/tla/Invariants.tla
-/

namespace NearFall

/-- Kernel version string.

v0.3.0: Consolidated modules + security fixes
- Merged CheckerV2 → Checker, SoundnessV2 → Soundness
- 29 TLA+ invariants (was 26, +3 BIND from security review)
- 10 axioms for cryptographic assumptions
- 8 security fixes from security review
-/
def version : String := "0.3.0"

end NearFall
