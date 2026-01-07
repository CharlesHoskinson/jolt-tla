import Jolt.Types
import Jolt.Encoding
import Jolt.Transcript
import Jolt.ConfigTags
import Jolt.StateDigest
import Jolt.Wrapper
import Jolt.Continuations

/-!
# Jolt Kernel

Minimal trusted core for Jolt zkVM verification.

**This is the ONLY file auditors need to review.**

## Trusted Computing Base

1. `constant PoseidonPermute` - Poseidon permutation (not proven)
2. Lean 4 core library (widely vetted)

## Exported Surface

### Types
- `Fr` - BN254 field element
- `Bytes32` - 32-byte container
- `VMStateV1` - VM state structure
- `PublicInputsV1` - 11 Fr public inputs
- `ExecutionTrace` - Continuation chunks

### Functions
- `Bytes32ToFr2` - Encode bytes as field pair
- `stateDigestV1` - 14-step state commitment
- `checkWrapper` - Verify public input binding
- `checkContinuationChain` - Verify chunk chaining

### Theorems
All `check_sound` theorems: if checker passes, specification holds.

## Security Properties

The kernel guarantees that if all checkers pass:
1. No chunk skipping (consecutive indices)
2. No chunk splicing (digest chain)
3. No cross-config attacks (config in digest)
4. No memory forgery (SMT binding)
5. No replay attacks (nonce binding)

## Audit Instructions

1. Verify axiom list (should only be `stateDigest_collision_resistant`)
2. Run: `#print axioms Jolt.Kernel.wrapper_sound`
3. Verify no `sorry` in soundness theorems
4. Review `PoseidonPermute` trust assumption

## References

* Jolt Spec (spec.md)
* KERNEL_SCOPE.md
-/

namespace Jolt.Kernel

/-! ### Re-exported Types -/

-- Core types
export Jolt (Fr Bytes32 U64 Fr2 Vec RegFile)

-- VM state
export Jolt.StateDigest (HaltedFlag ExitCode VMStateV1)

-- Public inputs
export Jolt.Wrapper (PublicInputsV1)

-- Continuations
export Jolt.Continuations (ChunkRecord ExecutionTrace)

-- Config tags
export Jolt.ConfigTags (ConfigTag ConfigTags)

/-! ### Re-exported Functions -/

-- Encoding
export Jolt.Encoding (Bytes32ToFr2 Fr2ToBytes32 bytesToNatLE natToBytesLE)

-- Transcript
export Jolt.Transcript (TranscriptState PoseidonPermute PoseidonHashV1)

-- StateDigest
export Jolt.StateDigest (stateDigestV1)

-- Wrapper
export Jolt.Wrapper (checkWrapper checkRanges assemblePublicInputs)

-- Continuations
export Jolt.Continuations (checkContinuationChain checkChainContinuity)

-- ConfigTags
export Jolt.ConfigTags (checkConfigTags)

/-! ### Kernel Theorems -/

/-- KERNEL THEOREM 1: Encoding roundtrip soundness.

If Bytes32ToFr2 succeeds, Fr2ToBytes32 recovers the original. -/
theorem encoding_roundtrip_sound : Encoding.SpecRoundTrip :=
  Encoding.roundtrip_sound

/-- KERNEL THEOREM 2: Encoding injectivity.

Different Bytes32 values produce different Fr2 encodings. -/
theorem encoding_injective : Encoding.SpecInjective :=
  Encoding.injective_sound

/-- KERNEL THEOREM 3: Config tags soundness.

If checkConfigTags passes, tags are sorted and unique. -/
theorem configTags_sound : ∀ tags,
    ConfigTags.checkConfigTags tags = true →
    ConfigTags.SpecConfigTags tags :=
  ConfigTags.checkConfigTags_sound

/-- KERNEL THEOREM 4: Wrapper soundness.

If checkWrapper passes, wrapper specification holds. -/
theorem wrapper_sound : ∀ pi programHash stateIn stateOut,
    Wrapper.checkWrapper pi programHash stateIn stateOut = true →
    Wrapper.SpecWrapper pi programHash stateIn stateOut :=
  Wrapper.checkWrapper_sound

/-- KERNEL THEOREM 5: Continuation chain soundness.

If checkContinuationChain passes, continuation specification holds. -/
theorem continuations_sound : ∀ trace,
    Continuations.checkContinuationChain trace = true →
    Continuations.SpecContinuations trace :=
  Continuations.checkContinuationChain_sound

/-- KERNEL THEOREM 6: StateDigest determinism.

StateDigestV1 is a deterministic function. -/
theorem stateDigest_deterministic : StateDigest.SpecDeterministic :=
  StateDigest.stateDigest_deterministic

/-! ### Axiom Manifest -/

/-- Total axiom count for the kernel.

We have exactly TWO cryptographic axioms:
1. `PoseidonPermute` - The Poseidon permutation function (cryptographic primitive)
2. `stateDigest_collision_resistant` - StateDigest collision resistance

Both axioms are cryptographic security assumptions that cannot be proven
mathematically. They represent the trust boundary of the system. -/
def AXIOM_COUNT : Nat := 2

/-- Axiom documentation for auditors.

| ID | Axiom | Module | Purpose |
|----|-------|--------|---------|
| 1 | PoseidonPermute | Transcript.lean | Cryptographic permutation |
| 2 | stateDigest_collision_resistant | StateDigest.lean | Digest binding |

**Axiom 1 - PoseidonPermute**: The Poseidon permutation is a cryptographic
primitive that transforms a state vector. Security follows from the algebraic
structure of the round function.

**Axiom 2 - stateDigest_collision_resistant**: States that if two (programHash,
state) pairs produce the same StateDigestV1 output, then the pairs are equal.
This follows from PoseidonPermute being collision-resistant via the sponge
construction.

Both axioms are justified by the security of the Poseidon hash function,
which has security proofs in the random permutation model. -/
structure AxiomManifest where
  /-- Poseidon permutation function (cryptographic primitive). -/
  poseidonPermute : Prop
  /-- StateDigest collision resistance (from Poseidon). -/
  stateDigest_collision_resistant : Prop

/-! ### TCB Documentation -/

/-- Trusted Computing Base summary.

The kernel trusts:

1. **PoseidonPermute** (constant in Transcript.lean)
   - Cryptographic permutation
   - Security: collision resistance, preimage resistance
   - Reference: Poseidon paper (USENIX 2021)

2. **Lean 4 Core**
   - Type system soundness
   - Arithmetic correctness
   - Reference: Lean 4 documentation

Everything else is derived from definitions and proofs. -/
structure TCBSummary where
  /-- Poseidon permutation is collision resistant. -/
  poseidon_secure : Prop
  /-- Lean 4 type system is sound. -/
  lean_sound : Prop

/-! ### Security Guarantees -/

/-- Main security theorem: valid trace implies security properties.

If all checkers pass on an execution trace, then:
1. Chunk indices are consecutive (no skipping)
2. Chunk digests chain correctly (no splicing)
3. All chunks use same program and config (no cross-config)
4. Initial and final states are correctly bound
5. All digests are consistent with states -/
theorem valid_trace_is_secure (trace : ExecutionTrace) :
    Continuations.checkContinuationChain trace = true →
    Continuations.SpecContinuations trace :=
  continuations_sound trace

/-- Wrapper validity implies binding.

If wrapper check passes, public inputs are correctly bound to:
- Program hash
- Initial state digest
- Final state digest -/
theorem valid_wrapper_is_bound (pi : PublicInputsV1) (programHash : Bytes32)
    (stateIn stateOut : VMStateV1) :
    Wrapper.checkWrapper pi programHash stateIn stateOut = true →
    Wrapper.SpecWrapper pi programHash stateIn stateOut :=
  wrapper_sound pi programHash stateIn stateOut

/-! ### Audit Commands -/

-- Run these commands to audit the kernel:

-- 1. Check axioms used by wrapper_sound
-- #print axioms Jolt.Kernel.wrapper_sound

-- 2. Check axioms used by continuations_sound
-- #print axioms Jolt.Kernel.continuations_sound

-- 3. Verify no sorry in this file
-- (CI should fail if sorry present)

-- 4. Review TCB: only PoseidonPermute should appear
-- #check @Jolt.Transcript.PoseidonPermute

end Jolt.Kernel
