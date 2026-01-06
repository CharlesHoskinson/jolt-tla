# Architecture Overview

## System Design

The Jolt continuation system enables proving arbitrarily long RISC-V program executions by splitting them into chunks.

```
┌─────────────────────────────────────────────────────────────────────┐
│                        EXECUTION TRACE                               │
│  Step 0          Step N          Step 2N         Step 3N    Halt    │
│    │               │               │               │          │      │
│    ▼               ▼               ▼               ▼          ▼      │
│ ┌─────┐         ┌─────┐         ┌─────┐         ┌─────┐             │
│ │Chunk│─digest─▶│Chunk│─digest─▶│Chunk│─digest─▶│Chunk│             │
│ │  0  │         │  1  │         │  2  │         │  3  │             │
│ └─────┘         └─────┘         └─────┘         └─────┘             │
│    │               │               │               │                 │
│    ▼               ▼               ▼               ▼                 │
│ ┌─────┐         ┌─────┐         ┌─────┐         ┌─────┐             │
│ │Proof│         │Proof│         │Proof│         │Proof│             │
│ │  0  │         │  1  │         │  2  │         │  3  │             │
│ └─────┘         └─────┘         └─────┘         └─────┘             │
│    │               │               │               │                 │
│    └───────────────┴───────────────┴───────────────┘                 │
│                           │                                          │
│                           ▼                                          │
│                    ┌────────────┐                                    │
│                    │  Wrapper   │                                    │
│                    │   Proof    │                                    │
│                    └────────────┘                                    │
│                           │                                          │
│                           ▼                                          │
│                    ┌────────────┐                                    │
│                    │  On-Chain  │                                    │
│                    │  Verifier  │                                    │
│                    └────────────┘                                    │
└─────────────────────────────────────────────────────────────────────┘
```

## Trust Model

### What Soundness Guarantees

If the verifier accepts a proof, then with overwhelming probability:
- A valid execution trace exists
- The trace started from the claimed initial state
- The trace ended in the claimed final state
- All intermediate state transitions followed RISC-V semantics

### What Soundness Does NOT Guarantee

- **Confidentiality**: Proofs reveal nothing about intermediate states, but provers see everything
- **Liveness**: A malicious prover can refuse to generate proofs
- **Correctness of the program**: Only that the program ran correctly, not that it computes what you want

```
┌─────────────────────────────────────────────────────────┐
│                   TRUST BOUNDARIES                       │
│                                                          │
│  ┌──────────────┐         ┌──────────────┐              │
│  │    Prover    │         │   Verifier   │              │
│  │              │         │              │              │
│  │ • Sees all   │  proof  │ • Sees only  │              │
│  │   state      │────────▶│   public     │              │
│  │ • Trusted    │         │   inputs     │              │
│  │   for        │         │ • Trustless  │              │
│  │   liveness   │         │              │              │
│  └──────────────┘         └──────────────┘              │
│                                                          │
└─────────────────────────────────────────────────────────┘
```

## Data Flow

### Chunk Proving

```
Input:
  - VMState_in: Starting VM state
  - program_hash: Hash of ELF binary
  - config_tags: Registry configuration

Processing:
  1. Execute CHUNK_MAX_STEPS instructions (or until halt)
  2. Compute state_digest_in = StateDigest(VMState_in, program_hash, config_tags)
  3. Compute state_digest_out = StateDigest(VMState_out, program_hash, config_tags)
  4. Generate Jolt proof for the chunk

Output:
  - ChunkProof with (state_digest_in, state_digest_out, steps, halted)
```

### StateDigest Computation

The StateDigest binds all security-critical fields into a single field element:

```
StateDigest(vm, program_hash, config_tags):
  T = Transcript.init()
  T.absorb_tag("JOLT/STATE/V1")
  T.absorb_bytes(program_hash)           # Bind program identity
  T.absorb_u64(vm.pc)                    # Bind program counter
  for i in 0..31:
    T.absorb_u64(vm.regs[i])             # Bind all registers
  T.absorb_u64(vm.step_counter)          # Bind execution progress
  T.absorb_bytes(vm.rw_mem_root)         # Bind R/W memory state
  T.absorb_bytes(vm.io_mem_root)         # Bind I/O memory state
  T.absorb_u64(vm.halted)                # Bind termination status
  T.absorb_u64(vm.exit_code)             # Bind exit code
  T.absorb_tag("JOLT/CONFIG_TAGS/V1")
  T.absorb_u64(len(config_tags))
  for (name, value) in sorted(config_tags):
    T.absorb_tag("JOLT/TAG/V1")
    T.absorb_bytes(name)
    T.absorb_bytes(value)
  return T.challenge_fr()                # Squeeze digest
```

### Continuation Chaining

```
Chunk 0                Chunk 1                Chunk 2
┌────────────────┐     ┌────────────────┐     ┌────────────────┐
│ digest_in: D0  │     │ digest_in: D1  │     │ digest_in: D2  │
│ digest_out: D1 │────▶│ digest_out: D2 │────▶│ digest_out: D3 │
│ steps: N       │     │ steps: N       │     │ steps: M       │
│ halted: 0      │     │ halted: 0      │     │ halted: 1      │
└────────────────┘     └────────────────┘     └────────────────┘

Invariants:
  - Chunk[i].digest_out == Chunk[i+1].digest_in  (chaining)
  - Chunk[0].step_counter_in == 0                (start from beginning)
  - All non-final chunks: halted == 0            (no early termination)
  - Final chunk: halted == 1                     (must terminate)
```

## Memory Commitment

Memory is committed using Sparse Merkle Trees (SMT):

```
                        Root
                       /    \
                    H01      H23
                   /   \    /   \
                 H0    H1  H2    H3
                  │     │   │     │
                Page0 Page1 Page2 Page3
                (4KB) (4KB) (4KB) (4KB)

Parameters:
  - PAGE_SIZE: 4096 bytes
  - KEY_BITS: 32 (address space / page size)
  - Bit order: MSB-first (address bits)

Hash functions:
  - leaf_fr(page) = PoseidonHash("JOLT/SMT/PAGE/V1", page)
  - node_fr(L, R) = PoseidonHash2("JOLT/SMT/NODE/V1", L, R)
```

## Security Properties

### Binding Properties

| Property | What It Binds | TLA+ Invariant |
|----------|---------------|----------------|
| Program binding | ELF hash to proof | `INV_BIND_ProgramHash` |
| State binding | VM state to digest | `INV_BIND_StateDigest` |
| Config binding | Registry to execution | `INV_BIND_ConfigTags` |
| Root binding | Memory to SMT root | `INV_BIND_OldRoot`, `INV_BIND_NewRoot` |

### Attack Prevention

| Attack | Prevention | TLA+ Invariant |
|--------|------------|----------------|
| Skip chunk | Chain integrity check | `INV_ATK_NoSkipChunk` |
| Splice execution | Program hash in digest | `INV_ATK_NoSplice` |
| Early termination | halted flag check | `INV_ATK_NoPrefixProof` |
| Memory forgery | SMT root binding | `INV_ATK_NoMemoryForgery` |
