# TLA+ to Lean Alignment Matrix

## Overview

This document maps TLA+ specification modules (jolt-tla) to their corresponding Lean oracle implementations (jolt_oracle), ensuring traceability per NFR-05.

## Module Correspondence

| TLA+ Module | Lean Module(s) | Spec Section | Status |
|-------------|----------------|--------------|--------|
| Types.tla | Jolt/Field/Fr.lean, Jolt/Encoding/Bytes32.lean | 2.1-2.2 | Aligned |
| Encodings.tla | Jolt/Encoding/Fr2.lean | 2.2.1 | Aligned |
| Hash.tla | Jolt/Poseidon/*.lean | 3.4.1 | Aligned |
| Registry.tla | Jolt/Registry/*.lean | 3.2-3.8 | Aligned |
| Transcript.tla | Jolt/Transcript/*.lean | 8.4-8.6 | Aligned |
| VMState.tla | Jolt/State/VMState.lean | 11.5 | Aligned |
| Wrapper.tla | Jolt/Wrapper/*.lean | 5.2 | Aligned |
| Invariants.tla | (runtime validation) | - | Partial |
| JSON.tla | Jolt/JSON/*.lean | 2.6 | Aligned |
| Tar.tla | Jolt/Bundle/Tar.lean | 14.3 | Aligned |
| Bundle.tla | Jolt/Bundle/*.lean | 14 | Aligned |
| SMT.tla | (not implemented) | 12 | Gap |
| SMTOps.tla | (not implemented) | 12 | Gap |
| Continuations.tla | Jolt/Oracle.lean (partial) | 11 | Partial |

## Detailed Mappings

### Types.tla → Lean Types

| TLA+ Definition | Lean Definition | Notes |
|-----------------|-----------------|-------|
| `Fr` | `Jolt.Fr` | BLS12-381 scalar field |
| `Bytes32` | `Jolt.Bytes32` | 32-byte fixed array |
| `U64` | `UInt64` | Native Lean type |

### Hash.tla → Poseidon Modules

| TLA+ Constant | Lean Definition | File |
|---------------|-----------------|------|
| `POSEIDON_WIDTH` | `POSEIDON_WIDTH = 3` | Params.lean |
| `POSEIDON_FULL_ROUNDS` | `POSEIDON_FULL_ROUNDS = 8` | Params.lean |
| `POSEIDON_PARTIAL_ROUNDS` | `POSEIDON_PARTIAL_ROUNDS = 60` | Params.lean |
| `ALL_DOMAIN_TAGS` | (used inline) | - |

### Registry.tla → Registry Modules

| TLA+ Definition | Lean Definition | File |
|-----------------|-----------------|------|
| `RequiredKeys` | `requiredKeys` | KeyValidation.lean |
| `ExternalHandleTags` | `externalHandleTags` | KeyValidation.lean |
| `ValidKeyFormat` | `isValidKeyFormat` | KeyValidation.lean |
| `NoExternalHandlesInvariant` | (validation function) | Validate.lean |

### Transcript.tla → Transcript Modules

| TLA+ Definition | Lean Definition | File |
|-----------------|-----------------|------|
| `TYPE_BYTES_FR` | `TYPE_BYTES = Fr.ofNat 1` | Types.lean |
| `TYPE_U64_FR` | `TYPE_U64 = Fr.ofNat 2` | Types.lean |
| `TYPE_TAG_FR` | `TYPE_TAG = Fr.ofNat 3` | Types.lean |
| `TYPE_VEC_FR` | `TYPE_VEC = Fr.ofNat 4` | Types.lean |
| `AbsorbBytes` | `absorbBytes` | State.lean |
| `AbsorbU64` | `absorbU64` | State.lean |
| `AbsorbTag` | `absorbTag` | State.lean |
| `AbsorbVec` | `absorbVec` | State.lean |

### VMState.tla → State Modules

| TLA+ Definition | Lean Definition | File |
|-----------------|-----------------|------|
| `VMStateV1` | `VMStateV1` structure | VMState.lean |
| `ValidateRegisterX0` | `validateRegisterX0` | VMState.lean |
| `ValidateHalted` | `validateHalted` | VMState.lean |
| `ValidateTermination` | `validateTermination` | VMState.lean |
| `StateDigest` | `computeStateDigest` | Digest.lean |

### Wrapper.tla → Wrapper Modules

| TLA+ Definition | Lean Definition | File |
|-----------------|-----------------|------|
| `PublicInputs` | `PublicInputs` | PublicInputs.lean |
| `WrapperConfig` | (in ProofSystem.lean) | ProofSystem.lean |

### JSON.tla → JSON Modules

| TLA+ Definition | Lean Definition | File |
|-----------------|-----------------|------|
| `ValidJSON` | `parse` result | Parser.lean |
| `JCSEncode` | `canonicalize` | JCS.lean |
| `NoDuplicateKeys` | TreeSet detection | Parser.lean |

### Tar.tla → Bundle Modules

| TLA+ Definition | Lean Definition | File |
|-----------------|-----------------|------|
| `ValidTarPath` | `isValidPath` | Tar.lean |
| `BytewiseSorted` | `isSortedByBytes` | Tar.lean |
| `NoAbsolutePaths` | path validation | Tar.lean |

## Invariants Mapping

| TLA+ Invariant | Lean Validation | Status |
|----------------|-----------------|--------|
| `INV_SAFE_*` | (runtime checks) | Implicit |
| `INV_BIND_*` | State validation | Implemented |
| `INV_ATK_NoSplice` | Chain verification | Implemented |
| `INV_ATK_NoSkipChunk` | Chain verification | Implemented |
| `NoExternalHandlesInvariant` | Registry validation | Implemented |

## Constants Alignment

### Registry Keys (17 required)

Both TLA+ and Lean define the same 17 required keys:
- JOLT_BATCH_COMMITMENT_V1
- JOLT_BATCH_MANIFEST_ENCODING_V1
- JOLT_CHUNK_ENCODING_V1
- ... (see Registry.tla RequiredKeys)

### External Handles (3)

Both define:
- JOLT_PARAMETER_REGISTRY_HASH_V1
- JOLT_WRAPPER_VK_HASH_V1
- JOLT_CONFORMANCE_BUNDLE_HASH_V1

### Transcript Type Tags

| Tag | TLA+ | Lean |
|-----|------|------|
| BYTES | 1 | Fr.ofNat 1 |
| U64 | 2 | Fr.ofNat 2 |
| TAG | 3 | Fr.ofNat 3 |
| VEC | 4 | Fr.ofNat 4 |

## Known Gaps

### Not Implemented in Lean

1. **SMT.tla / SMTOps.tla** - Sparse Merkle Tree operations
   - Lean only validates root hashes, doesn't construct trees

2. **Continuations.tla** - Full continuation semantics
   - Lean verifies chain linkage, not execution

3. **VM Execution** - Step-by-step instruction execution
   - Lean validates state, doesn't simulate execution

### Partial Implementations

1. **Invariants.tla** - TLA+ invariants are model-checked
   - Lean has runtime validation but not formal invariant proofs

## Verification Protocol

To verify alignment:

```bash
# Check TLA+ constants
grep "RequiredKeys" jolt-tla/tla/Registry.tla
grep "requiredKeys" jolt_oracle/Jolt/Registry/KeyValidation.lean

# Check type tags
grep "TYPE_.*_FR" jolt-tla/tla/Transcript.tla
grep "TYPE_" jolt_oracle/Jolt/Transcript/Types.lean

# Run alignment check script
python3 jolt-tla/scripts/check_alignment.py
```

## References

- TLA+ Specification: `jolt-tla/tla/`
- Lean Oracle: `jolt_oracle/Jolt/`
- Spec Document: `jolt-tla/spec.md`
