# Module Reference

API documentation for all TLA+ modules in the specification.

## Module Dependency Graph

```
Types
  │
  ▼
Encodings ──▶ Hash
                │
                ▼
            Transcript
                │
                ▼
SMT ◀────── SMTOps
  │
  ▼
VMState ◀── Registry
  │
  ▼
Continuations
  │
  ▼
Wrapper
  │
  ▼
JoltSpec
  │
  ▼
Invariants
  │
  ▼
MC_Jolt
```

---

## Types.tla

Foundation type definitions.

### Constants

| Name | Type | Description |
|------|------|-------------|
| `NUM_REGISTERS` | Nat | Number of RISC-V registers (32) |
| `FR_MODULUS` | Nat | BLS12-381 scalar field modulus |
| `FR_TLC_BOUND` | Nat | TLC bound for Fr enumeration |
| `U64_TLC_BOUND` | Nat | TLC bound for U64 enumeration |
| `CHUNK_MAX_STEPS` | Nat | Max steps per chunk |
| `MAX_CHUNKS` | Nat | Max chunks to model |

### Type Sets

| Name | Definition | Description |
|------|------------|-------------|
| `Fr` | `0..(FR_TLC_BOUND-1)` | Field element |
| `U64` | `0..(U64_TLC_BOUND-1)` | 64-bit unsigned |
| `U8` | `0..255` | 8-bit unsigned |
| `Bytes32` | `[0..31 -> U8]` | 32-byte array |

### Status Codes

| Name | Value | Meaning |
|------|-------|---------|
| `JOLT_STATUS_OK` | 0 | Successful execution |
| `JOLT_STATUS_TRAP_ILLEGAL` | 1 | Illegal instruction |
| `JOLT_STATUS_TRAP_MEMORY` | 2 | Memory access violation |
| `JOLT_STATUS_TRAP_SYSCALL` | 3 | Forbidden syscall |
| `JOLT_STATUS_TRAP_OOM` | 4 | Out of memory |
| `JOLT_STATUS_TRAP_INTERNAL` | 5 | Internal error |

---

## Encodings.tla

Byte/field encoding primitives.

### Operators

#### FrFromU64(x)
```tla
FrFromU64(x) == x % FR_TLC_BOUND
```
Convert U64 to Fr (with modular reduction for TLC).

#### FrFromU248(x)
```tla
FrFromU248(x) == x % FR_TLC_BOUND
```
Convert 248-bit integer to Fr.

#### Bytes32ToFr2(b)
```tla
Bytes32ToFr2(b) == [lo |-> ..., hi |-> ...]
```
Split 32-byte value into two Fr elements (lo: 248 bits, hi: 8 bits).

#### Fr2ToBytes32(lo, hi)
```tla
Fr2ToBytes32(lo, hi) == ...
```
Reconstruct Bytes32 from two Fr elements.

---

## Hash.tla

Cryptographic hash abstractions.

### Constants

| Name | Description |
|------|-------------|
| `TAG_STRINGS` | Set of valid domain separation tags |
| `PoseidonHashBytes` | Model override for Poseidon hash |
| `PoseidonHashFr2` | Model override for 2-input Poseidon |
| `SHA256Hash` | Model override for SHA-256 |

### Operators

#### ModelPoseidonHashBytes(tag, bytes)
```tla
ModelPoseidonHashBytes(tag, bytes) ==
    \* Returns fingerprint-based hash for TLC
```

#### ModelPoseidonHashFr2(tag, a, b)
```tla
ModelPoseidonHashFr2(tag, a, b) ==
    \* Returns fingerprint-based hash of two Fr inputs
```

#### ModelSHA256Hash(bytes)
```tla
ModelSHA256Hash(bytes) ==
    \* Returns fingerprint-based SHA-256 for TLC
```

---

## Transcript.tla

Fiat-Shamir transcript construction.

### Operators

#### TranscriptInit()
```tla
TranscriptInit() == [state |-> 0, absorbed |-> <<>>]
```
Initialize empty transcript.

#### TranscriptAbsorbTag(T, tag)
```tla
TranscriptAbsorbTag(T, tag) ==
    [T EXCEPT !.absorbed = Append(@, ["type" |-> "tag", "value" |-> tag])]
```
Absorb domain separation tag.

#### TranscriptAbsorbU64(T, x)
```tla
TranscriptAbsorbU64(T, x) ==
    [T EXCEPT !.absorbed = Append(@, ["type" |-> "u64", "value" |-> x])]
```
Absorb 64-bit integer.

#### TranscriptAbsorbBytes(T, b)
```tla
TranscriptAbsorbBytes(T, b) ==
    [T EXCEPT !.absorbed = Append(@, ["type" |-> "bytes", "value" |-> b])]
```
Absorb byte sequence.

#### TranscriptChallenge(T)
```tla
TranscriptChallenge(T) ==
    \* Squeeze challenge Fr from transcript state
```

---

## SMT.tla

Sparse Merkle Tree structures.

### Constants

| Name | Value | Description |
|------|-------|-------------|
| `PAGE_SIZE_BYTES` | 4096 | Bytes per memory page |
| `PAGE_SHIFT` | 12 | log2(PAGE_SIZE_BYTES) |
| `KEY_BITS` | 32 | SMT depth |

### Operators

#### SMTLeafHash(pageBytes)
```tla
SMTLeafHash(pageBytes) == PoseidonHashBytes("JOLT/SMT/PAGE/V1", pageBytes)
```

#### SMTNodeHash(left, right)
```tla
SMTNodeHash(left, right) == PoseidonHashFr2("JOLT/SMT/NODE/V1", left, right)
```

#### SMTRoot(tree)
```tla
SMTRoot(tree) == \* Compute root from tree structure
```

---

## VMState.tla

RISC-V VM state machine.

### VMStateV1 Record

```tla
VMStateV1 == [
    regs: [0..31 -> U64],      \* 32 general-purpose registers
    pc: U64,                    \* Program counter
    step_counter: U64,          \* Instructions executed
    rw_mem_root_bytes32: Bytes32,  \* R/W memory commitment
    io_root_bytes32: Bytes32,      \* I/O memory commitment
    halted: {0, 1},             \* Termination flag
    exit_code: U64,             \* Exit status (0-255 when halted)
    config_tags: Seq(...)       \* Registry projection
]
```

### Operators

#### ExecuteStep(vm)
```tla
ExecuteStep(vm) == STEP_FN(vm)
```
Execute one instruction (abstract).

#### IsSuccessfulHalt(vm)
```tla
IsSuccessfulHalt(vm) == vm.halted = 1 /\ vm.exit_code = 0
```

#### IsTrappedHalt(vm)
```tla
IsTrappedHalt(vm) == vm.halted = 1 /\ vm.exit_code > 0
```

---

## Continuations.tla

Chunked execution model.

### Operators

#### ComputeStateDigest(vm, programHash, configTags)
```tla
ComputeStateDigest(vm, programHash, configTags) ==
    LET T0 == TranscriptInit()
        T1 == TranscriptAbsorbTag(T0, "JOLT/STATE/V1")
        T2 == TranscriptAbsorbBytes(T1, programHash)
        T3 == TranscriptAbsorbU64(T2, vm.pc)
        \* ... absorb all fields ...
        Tn == TranscriptAbsorbConfigTags(T_{n-1}, configTags)
    IN TranscriptChallenge(Tn)
```

#### ChunkValid(chunk)
```tla
ChunkValid(chunk) ==
    /\ chunk.steps <= CHUNK_MAX_STEPS
    /\ chunk.halted \in {0, 1}
    /\ (chunk.halted = 0 => chunk.steps = CHUNK_MAX_STEPS)
```

#### ContinuityInvariant(chunks)
```tla
ContinuityInvariant(chunks) ==
    \A i \in 1..Len(chunks)-1:
        chunks[i].digest_out = chunks[i+1].digest_in
```

---

## Invariants.tla

All specification invariants.

### Aggregate Invariants

| Name | Contents |
|------|----------|
| `INV_TYPE_All` | All type invariants |
| `INV_BIND_All` | All binding invariants |
| `INV_SAFE_All` | All safety invariants |
| `INV_ATK_All` | All attack prevention invariants |
| `AllInvariants` | Everything |

### Individual Invariants

See [invariants.md](invariants.md) for complete reference.

---

## MC_Jolt.tla

TLC model configuration.

### Model Values

| Name | Value | Purpose |
|------|-------|---------|
| `ModelInit` | Concrete initial state | Avoids existential quantification |
| `ModelStepFn` | Abstract step function | Deterministic for TLC |
| `StateConstraint` | Bounds predicate | Limits state space |

### Usage

```bash
java -jar tla2tools.jar MC_Jolt.tla -config Jolt.cfg -workers auto
```
