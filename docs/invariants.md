# Invariant Reference

This document describes all 26 individual invariants (plus 6 composites) checked by the TLA+ specification.

## Invariant Categories

| Category | Prefix | Count | Severity |
|----------|--------|-------|----------|
| Type | `INV_TYPE_` | 4 | Medium |
| Binding | `INV_BIND_` | 7 | Critical |
| Safety | `INV_SAFE_` | 7 | High |
| Attack Prevention | `INV_ATK_` | 8 | Critical |

## Type Invariants (INV_TYPE_*)

Type invariants ensure all values are well-formed according to their type definitions.

### INV_TYPE_SystemState

**Purpose**: System-level state is well-formed.

**Checks**:
- `phase` is one of: `"init"`, `"executing"`, `"complete"`
- `batchNonce` is a valid Fr element

**Violation means**: Corrupted system state, likely implementation bug.

### INV_TYPE_Registry

**Purpose**: Configuration registry entries are well-formed.

**Checks**:
- Each entry has `key`, `value`, `required`, `validated` fields
- Keys are strings
- All required keys are present

**Violation means**: Invalid configuration, deployment should be blocked.

### INV_TYPE_VMState

**Purpose**: VM state fields are within valid ranges.

**Checks**:
- `regs[0..31]` are valid U64 values
- `pc` is a valid U64
- `step_counter` is a valid U64
- `halted` is 0 or 1
- `exit_code` is in [0, 255] when halted
- `rw_mem_root_bytes32` is a valid Bytes32
- `io_root_bytes32` is a valid Bytes32

**Violation means**: VM state corruption, invalid execution trace.

### INV_TYPE_ProgramHash

**Purpose**: Program hash is a valid Bytes32.

**Checks**:
- `programHash` has exactly 32 bytes
- Each byte is in [0, 255]

**Violation means**: Program identity cannot be verified.

### INV_TYPE_PublicInputs

**Purpose**: Public inputs are well-formed Fr elements.

**Checks**:
- All `*_lo`, `*_hi` fields are valid Fr
- `status_fr` is valid Fr
- `batch_nonce_fr` is valid Fr

**Violation means**: Proof cannot be verified on-chain.

---

## Binding Invariants (INV_BIND_*)

Binding invariants ensure cryptographic commitments are correct.

### INV_BIND_ProgramHash

**Purpose**: Public inputs contain correct program hash.

**Formula**:
```
publicInputs.program_hash_lo = Bytes32ToFr2(programHash).lo
publicInputs.program_hash_hi = Bytes32ToFr2(programHash).hi
```

**Attack prevented**: Program substitution—proving one program, claiming another.

### INV_BIND_OldRoot

**Purpose**: Initial state root matches actual initial memory.

**Formula**:
```
publicInputs.old_root_* = Bytes32ToFr2(initialState.rw_mem_root).*
```

**Attack prevented**: Claiming false initial state.

### INV_BIND_NewRoot

**Purpose**: Final state root matches actual final memory.

**Formula**:
```
publicInputs.new_root_* = Bytes32ToFr2(finalState.rw_mem_root).*
```

**Attack prevented**: Claiming false final state.

### INV_BIND_StatusFr

**Purpose**: Status field matches actual exit code.

**Formula**:
```
phase = "complete" =>
  publicInputs.status_fr = FrFromU64(vmState.exit_code)
```

**Attack prevented**: Misrepresenting execution outcome.

### INV_BIND_StateDigest

**Purpose**: State digest correctly binds all VM state fields.

**Checks**: StateDigest computation includes:
- program_hash (program identity)
- pc (program counter)
- regs[0..31] (all registers)
- step_counter (execution progress)
- rw_mem_root (R/W memory commitment)
- io_root (I/O memory commitment)
- halted (termination flag)
- exit_code (exit status)
- config_tags (configuration)

**Attack prevented**: Tampering with any state field without detection.

### INV_BIND_ConfigTags

**Purpose**: Config tags in VM state match registry projection.

**Formula**:
```
vmState.config_tags = ProjectRegistry(registry, RequiredKeys)
```

**Attack prevented**: Using wrong configuration for proving vs. verification.

### INV_BIND_BatchCommitment

**Purpose**: Batch commitment correctly computed from manifest.

**Attack prevented**: Tampering with batch contents.

### INV_BIND_CheckpointsDigest

**Purpose**: Checkpoints digest correctly computed.

**Attack prevented**: Checkpoint manipulation.

### INV_BIND_Nonce

**Purpose**: Batch nonce matches claimed value.

**Attack prevented**: Nonce reuse/manipulation.

---

## Safety Invariants (INV_SAFE_*)

Safety invariants ensure protocol behaves correctly.

### INV_SAFE_NoOverflow

**Purpose**: No arithmetic overflow in computations.

**Checks**:
- step_counter doesn't overflow U64
- Field arithmetic stays within Fr bounds

**Violation means**: Undefined behavior in arithmetic.

### INV_SAFE_ValidTransition

**Purpose**: State transitions follow protocol rules.

**Checks**:
- Phase transitions are valid: init → executing → complete
- No backward transitions

**Violation means**: Protocol state machine violated.

### INV_SAFE_RegisterX0Zero

**Purpose**: Register x0 is always zero (RISC-V requirement).

**Formula**:
```
vmState.regs[0] = 0
```

**Violation means**: Invalid RISC-V execution.

### INV_SAFE_HaltedFlagValid

**Purpose**: Halted flag is boolean.

**Formula**:
```
vmState.halted ∈ {0, 1}
```

### INV_SAFE_RunningExitCodeZero

**Purpose**: Running VM has zero exit code.

**Formula**:
```
vmState.halted = 0 => vmState.exit_code = 0
```

### INV_SAFE_HaltedExitCodeValid

**Purpose**: Halted VM has valid exit code.

**Formula**:
```
vmState.halted = 1 => vmState.exit_code ∈ [0, 255]
```

### INV_SAFE_ContinuationChain

**Purpose**: Chunk digests form valid chain.

**Checks**:
- chunk[i].digest_out = chunk[i+1].digest_in
- First chunk starts at step 0
- Non-final chunks: halted = 0, steps = CHUNK_MAX_STEPS
- Final chunk: halted = 1

**Violation means**: Chunks cannot be correctly linked.

---

## Attack Prevention Invariants (INV_ATK_*)

Each invariant prevents a specific attack vector.

### INV_ATK_NoPrefixProof

**Purpose**: Cannot claim success without completing execution.

**Attack**: Generate proof for first N steps where computation succeeds, even though full execution would fail (e.g., skip balance check).

**Prevention**: Final chunk must have `halted = 1` and wrapper checks `status_fr`.

**Formula**:
```
phase = "complete" =>
  (vmState.halted = 1 ∧ vmState.exit_code = 0)
```

### INV_ATK_NoSkipChunk

**Purpose**: Cannot skip chunks in continuation sequence.

**Attack**: Prove chunks 0, 1, 3 (skip 2) where chunk 2 contains critical check.

**Prevention**: Digest chaining—chunk[i].digest_out must equal chunk[i+1].digest_in.

### INV_ATK_NoSplice

**Purpose**: Cannot mix chunks from different executions.

**Attack**: Take chunk 0 from execution A, chunk 1 from execution B.

**Prevention**: program_hash is bound into StateDigest, different programs have different digests.

### INV_ATK_NoCrossConfig

**Purpose**: Cannot use different config for proving vs. verification.

**Attack**: Prove with permissive MAX_STEPS, verify expects stricter limit.

**Prevention**: config_tags bound into StateDigest and checked at verification.

### INV_ATK_NoRootForgery

**Purpose**: Cannot claim false memory state.

**Attack**: Claim initial memory contains favorable values it didn't have.

**Prevention**: old_root/new_root in public inputs, bound to actual SMT roots.

### INV_ATK_NoMemoryForgery

**Purpose**: Cannot forge read-write memory.

**Attack**: Manipulate rw_mem_root to claim false R/W memory state.

**Prevention**: SMT root is cryptographic commitment, collision-resistant.

### INV_ATK_NoIOForgery

**Purpose**: Cannot forge input/output memory.

**Attack**: Claim different I/O than actually occurred.

**Prevention**: io_root separately committed and bound.

### INV_ATK_NoReplay

**Purpose**: Cannot replay proofs from different batches.

**Attack**: Reuse valid proof from batch A in batch B.

**Prevention**: batch_nonce bound into public inputs, verified on-chain.

---

## Verification

All invariants are checked by TLC model checker:

```bash
java -jar tla2tools.jar -config Jolt.cfg JoltContinuations.tla -workers auto
```

Expected output:
```
Model checking completed. No error has been found.
```

If any invariant fails, TLC produces a counterexample trace showing exactly how the violation occurs.

---

## Attack Coverage Matrix

This section provides an explicit mapping between attacker goals defined in the threat model and the formal invariants that prevent them.
Each row shows how a specific attack is blocked by one or more invariants and the enforcement mechanism that makes the prevention work.

### Primary Attack Prevention

| Attack Class | Attacker Goal | Preventing Invariant(s) | Enforcement Mechanism |
|--------------|---------------|-------------------------|------------------------|
| **Prefix** | Prove partial execution, skip validation at step N | `INV_ATK_NoPrefixProof` | Halted flag semantics require `halted = 1` for completion; `status_fr` binding to exit_code ensures final state is checked |
| **Skip** | Omit chunks to bypass authorization logic | `INV_ATK_NoSkipChunk` | Chunk index consecutiveness enforced; digest chaining breaks if any chunk is missing |
| **Splice** | Combine chunks from different executions | `INV_ATK_NoSplice`, `INV_SAFE_ContinuationChain` | StateDigest binds `program_hash` into every chunk boundary; different programs produce different digests |
| **Replay** | Resubmit old proofs for new transactions | `INV_ATK_NoReplay`, `INV_BIND_Nonce` | Batch nonce bound into StateDigest and public inputs; nonce uniqueness checked on-chain |
| **Config swap** | Prove with loose parameters, verify with strict | `INV_ATK_NoCrossConfig`, `INV_BIND_ConfigTags` | Config tags bound into StateDigest; registry projection validated at every chunk boundary |

### Memory and State Integrity

| Attack Class | Attacker Goal | Preventing Invariant(s) | Enforcement Mechanism |
|--------------|---------------|-------------------------|------------------------|
| **Root forgery** | Claim false initial/final memory state | `INV_ATK_NoRootForgery`, `INV_BIND_OldRoot`, `INV_BIND_NewRoot` | SMT roots bound into public inputs; Poseidon collision resistance prevents forging matching roots |
| **Memory forgery** | Manipulate R/W memory between chunks | `INV_ATK_NoMemoryForgery` | `rw_mem_root_bytes32` must match at chunk boundaries; enforced by StateDigest chaining |
| **I/O forgery** | Manipulate input/output memory between chunks | `INV_ATK_NoIOForgery` | `io_root_bytes32` must match at chunk boundaries; enforced by StateDigest chaining |

### Supporting Invariants

These invariants do not directly prevent attacks but ensure the enforcement mechanisms work correctly:

| Category | Invariant(s) | Role in Attack Prevention |
|----------|--------------|---------------------------|
| Type safety | `INV_TYPE_VMState`, `INV_TYPE_ProgramHash`, `INV_TYPE_PublicInputs` | Ensure well-formed inputs to digest computation; prevent type confusion attacks |
| Binding correctness | `INV_BIND_StateDigest`, `INV_BIND_ProgramHash`, `INV_BIND_StatusFr` | Ensure public inputs correctly reflect execution state; prevent binding bypass |
| Protocol correctness | `INV_SAFE_RegisterX0`, `INV_SAFE_HaltedBinary`, `INV_SAFE_VMHaltedExitCode` | Ensure VM semantics are valid; prevent invalid state transitions that could bypass checks |

---

## Continuation Integrity

The continuation chain provides a cryptographic binding that unifies all chunks into a single execution context.
This integrity is enforced collectively by the invariants listed above through the following mechanisms:

**StateDigest as the core binding primitive.**
Every chunk boundary is committed to by a StateDigest that includes:
- Program identity (`program_hash`)
- Execution position (`pc`, `step_counter`)
- VM register state (`regs[0..31]`)
- Memory commitments (`rw_mem_root`, `io_root`)
- Configuration (`config_tags`)
- Termination state (`halted`, `exit_code`)

**Digest chaining enforces temporal ordering.**
The constraint `chunk[i].digest_out = chunk[i+1].digest_in` ensures:
- No chunks can be skipped (breaks the chain)
- No chunks can be reordered (mismatched digests)
- No chunks can be spliced from different executions (different program_hash)

**Public input binding makes verification checkable.**
All security-critical values are exposed as public inputs:
- Initial and final memory roots (`old_root`, `new_root`)
- Program identity (`program_hash`)
- Execution outcome (`status_fr`)
- Anti-replay nonce (`batch_nonce_fr`)

Together, these mechanisms ensure that a valid proof represents exactly one complete execution of one program with no tampering at chunk boundaries.

---

## Scope Boundaries

The formal specification and invariants cover continuation integrity and cryptographic binding.
The following classes of threats are intentionally out of scope, as documented in the threat model:

**Out of scope:**
- Side-channel attacks on prover implementation (timing, power analysis)
- Denial of service and resource exhaustion (liveness is verifier's responsibility)
- Network-level attacks (eclipse, partition, routing)
- Bugs in verification tools themselves (Lean compiler, TLC model checker)
- Compromised verifier or malicious runtime environment
- Physical attacks on hardware executing the prover or verifier

**In scope:**
- All attacks that attempt to produce invalid proofs that would be accepted by an honest verifier
- Protocol-level attacks exploiting chunk boundaries, state transitions, or configuration mismatches
- Cryptographic attacks within the security assumptions stated (Poseidon collision resistance, BLS12-381 discrete log hardness)

For attacks involving a compromised verifier, the security model assumes the verifier correctly checks public inputs against the specification.
