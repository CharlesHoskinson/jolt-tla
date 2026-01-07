# Spec Mapping: Lean Symbols → Jolt Specification

**WARNING:** `spec.md` not found in repository. Mapping based on KERNEL_SCOPE.md and inline documentation.

## Types (Jolt/Types.lean)

**Spec Reference:** S5 (data types), S7 (field encodings)

| Lean Symbol | Spec Section | Description |
|-------------|--------------|-------------|
| `Fr` | S5.1 | BN254 scalar field element as `Fin r` |
| `Fr.modulus` | S5.1 | Value: `21888242871839275222246405745257275088548364400416034343698204186575808495617` |
| `Bytes32` | S5.3 | 32-byte fixed container with length proof |
| `U64` | S5.2 | 64-bit unsigned (alias for UInt64) |
| `Fr2` | S7.2 | Fr pair with constraints: lo < 2^248, hi < 256 |
| `Vec α n` | S5.4 | Fixed-size vector backed by Array |
| `RegFile` | S11.5 | 32 x Fr registers (x0 hardwired to zero) |

### Critical Bounds

| Type | Bound | Source |
|------|-------|--------|
| Fr | [0, r) where r = BN254 modulus | Enforced by `Fin r` |
| Fr2.lo | < 2^248 | Proof field `lo_bound` |
| Fr2.hi | < 256 | Proof field `hi_bound` |
| Bytes32 | length = 32 | Proof field `h_len` |

---

## Encoding (Jolt/Encoding.lean)

**Spec Reference:** S7.2 (Bytes32 to field element encoding)

| Lean Symbol | Spec Section | Description |
|-------------|--------------|-------------|
| `Bytes32ToFr2` | S7.2 | Encode 32 bytes as (lo: 31 bytes, hi: 1 byte) |
| `Fr2ToBytes32` | S7.2 | Decode Fr pair back to Bytes32 |
| `bytesToNatLE` | S7.2 | Little-endian bytes to Nat |
| `natToBytesLE` | S7.2 | Nat to little-endian bytes |
| `SpecRoundTrip` | S7.2 | Fr2ToBytes32(Bytes32ToFr2(b)) = some b |
| `SpecInjective` | S7.2 | Different bytes → different Fr2 |

### ⚠️ CRITICAL: Encoding Axioms (UNAUTHORIZED)

These soundness theorems are **axiomatized instead of proven**:
- `roundtrip_sound` - Should prove SpecRoundTrip
- `injective_sound` - Should prove SpecInjective
- `Bytes32ToFr2_succeeds` - Should prove totality on valid inputs

---

## Transcript (Jolt/Transcript.lean)

**Spec Reference:** S8 (Poseidon-based transcript)

| Lean Symbol | Spec Section | Description |
|-------------|--------------|-------------|
| `PoseidonPermute` | S8.1 | ✅ ALLOWED AXIOM (TCB) |
| `TranscriptState` | S8.2 | Sponge state machine |
| `stateWidth` | S8.2 | Value: 12 |
| `rate` | S8.2 | Value: 11 |
| `absorbFr` | S8.5 | Absorb single Fr element |
| `absorbTag` | S8.6 | Absorb tag bytes (31-byte chunks) |
| `squeezeFr` | S8.7 | Squeeze challenge Fr |
| `PoseidonHashV1` | S8.7 | Domain-separated hash |

---

## ConfigTags (Jolt/ConfigTags.lean)

**Spec Reference:** S3.8 (config_tags projection), RFC 8785 (JCS)

| Lean Symbol | Spec Section | Description |
|-------------|--------------|-------------|
| `ConfigTag` | S3.8 | name + valueBytes pair |
| `ConfigTags` | S3.8 | List of sorted, unique tags |
| `SpecConfigTags` | S3.8 | Tags sorted by UTF-16 code units |
| `checkConfigTags` | S3.8 | Validate sort order |
| `utf16Lt` | RFC 8785 | UTF-16 comparison (simplified to string <) |

### ⚠️ CRITICAL: ConfigTags Axiom (UNAUTHORIZED)

`checkConfigTags_sound` is **axiomatized instead of proven**.

---

## StateDigest (Jolt/StateDigest.lean)

**Spec Reference:** S11.10 (StateDigestV1 algorithm), S11.5 (VMStateV1)

| Lean Symbol | Spec Section | Description |
|-------------|--------------|-------------|
| `VMStateV1` | S11.5 | VM state structure |
| `stateDigestV1` | S11.10 | 14-step absorption algorithm |
| `HaltedFlag` | S11.5 | running / halted enum |
| `ExitCode` | S11.5 | 8-bit exit code |

### 14-Step Algorithm (stateDigestV1)

| Step | Field Absorbed | Code Line |
|------|----------------|-----------|
| 1 | Domain separator "StateDigestV1" | 159 |
| 2 | programHash as Fr2 | 162 |
| 3 | 32 registers | 165 |
| 4 | PC | 168 |
| 5 | stepCounter | 171 |
| 6 | rwRoot as Fr2 | 174 |
| 7 | ioRoot as Fr2 | 177 |
| 8 | halted flag | 180 |
| 9 | exitCode | 183 |
| 10-12 | configTags (count, names, values) | 186 |
| 13-14 | Final squeeze | 189 |

### ⚠️ CRITICAL: StateDigest Axiom (UNAUTHORIZED)

`stateDigest_collision_resistant` is **axiomatized**.

**Claimed justification:** "follows from PoseidonPermute collision resistance"

**Issue:** If it truly follows from PoseidonPermute, it should be PROVEN as a theorem, not asserted as a new axiom. This expands the TCB unnecessarily.

---

## Wrapper (Jolt/Wrapper.lean)

**Spec Reference:** S5.2 (PublicInputsV1), S5.6 (binding constraints)

| Lean Symbol | Spec Section | Description |
|-------------|--------------|-------------|
| `PublicInputsV1` | S5.2 | 11 Fr elements for verifier |
| `checkWrapper` | S5.6 | Validate all bindings |
| `checkRanges` | S5.2 | Validate range constraints |
| `assemblePublicInputs` | S5.6 | Construct from execution |

### PublicInputsV1 Layout (S5.2)

| Index | Field | Constraint |
|-------|-------|------------|
| 0 | programHashLo | < 2^248 |
| 1 | programHashHi | < 256 |
| 2 | digestIn | (full Fr) |
| 3 | digestOut | (full Fr) |
| 4 | batchCommitmentLo | < 2^248 |
| 5 | batchCommitmentHi | < 256 |
| 6 | statusFr | < 256 |
| 7 | batchNonceFr | < 2^64 |
| 8-10 | reserved1-3 | = 0 |

### ✅ Soundness Theorems PROVEN

All wrapper soundness theorems are properly proven:
- `checkRanges_sound`
- `checkProgramHashBinding_sound`
- `checkDigestBinding_sound`
- `checkWrapper_sound`

---

## Continuations (Jolt/Continuations.lean)

**Spec Reference:** S11 (Continuations), S11.10 (digest linking)

| Lean Symbol | Spec Section | Description |
|-------------|--------------|-------------|
| `ChunkRecord` | S11 | Single chunk execution record |
| `ExecutionTrace` | S11 | Sequence of chunks |
| `SpecChainContinuity` | S11.10 | digestOut[i] = digestIn[i+1] |
| `checkContinuationChain` | S11 | Full chain validation |

### Key Invariant

```
digestOut[chunk_i] = digestIn[chunk_{i+1}]
```

This ensures:
1. No chunk skipping (consecutive indices)
2. No chunk splicing (digests must match)
3. No cross-config attacks (config in digest)
4. Execution integrity (each chunk proves its transition)

### ✅ Soundness Theorems PROVEN

All continuation soundness theorems are properly proven:
- `checkChainContinuity_sound`
- `checkInitialBinding_sound`
- `checkFinalBinding_sound`
- `checkConsecutiveIndices_sound`
- `checkSameProgramHash_sound`
- `checkDigestsConsistent_sound`
- `checkConfigTagsPreserved_sound`
- `checkContinuationChain_sound`

### ✅ Attack Prevention Theorems PROVEN

- `splice_attack_prevented`
- `skip_attack_prevented`
- `cross_config_attack_prevented`

---

## IMPORTANT: Field Modulus

**BN254 scalar field modulus:**
```
r = 21888242871839275222246405745257275088548364400416034343698204186575808495617
```

Defined in `Jolt/Types.lean:26-27`.

**Verification needed:** Confirm this matches spec.md (not available).

---

## Summary: Spec Alignment

| Module | Soundness Status | Axiom Status |
|--------|------------------|--------------|
| Types.lean | ✅ All proven | No axioms |
| Encoding.lean | ⛔ 3 axiomatized | 7 unauthorized |
| Transcript.lean | ✅ All proven | 1 allowed (PoseidonPermute) |
| ConfigTags.lean | ⛔ 1 axiomatized | 1 unauthorized |
| StateDigest.lean | ✅ All proven | 1 unauthorized (crypto) |
| Wrapper.lean | ✅ All proven | No axioms |
| Continuations.lean | ✅ All proven | No axioms |

**CRITICAL:** 9 unauthorized axioms expand the TCB significantly.
