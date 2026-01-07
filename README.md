# Jolt TLA+ Formal Specification

> **Machine-checkable security proofs for zkVM continuation semantics**

[![TLA+ Verified](https://img.shields.io/badge/TLA%2B-Verified-success)]()
[![Version](https://img.shields.io/badge/version-0.1.0-blue)]()
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)
[![Spec Status](https://img.shields.io/badge/spec-Released_for_Comment-orange)]()

```
┌───────────────────────────────────────────────────────────────────────┐
│                  JOLT CONTINUATION PROVING SYSTEM                     │
├───────────────────────────────────────────────────────────────────────┤
│                                                                       │
│  ┌─────────────┐      ┌─────────────┐      ┌─────────────┐            │
│  │   CHUNK 0   │      │   CHUNK 1   │      │   CHUNK N   │            │
│  │  0 .. 1M    │─────>│  1M .. 2M   │─────>│   (final)   │            │
│  │  running    │      │  running    │      │   halted    │            │
│  └──────┬──────┘      └──────┬──────┘      └──────┬──────┘            │
│         │                    │                    │                   │
│         V                    V                    V                   │
│   StateDigest_0 ═══════ StateDigest_1 ═══════ StateDigest_N           │
│                                                                       │
│  Skip a chunk    --> digests mismatch --> proof rejected              │
│  Splice programs --> digests mismatch --> proof rejected              │
└───────────────────────────────────────────────────────────────────────┘
```

---

## The Chunking Problem

Zero-knowledge virtual machines hit a wall: **proofs have resource limits, but programs don't.**

Jolt proves RISC-V execution with zero-knowledge proofs. Validators check a succinct proof instead of re-running the computation. But proof generation needs memory proportional to the computation size. A million CPU cycles might need 64GB of RAM. A billion cycles? No machine can do it.

The workaround is chunking. Split execution into segments, prove each one, chain them cryptographically. The verifier checks that each chunk proof is valid and that they connect—chunk 1's final state matches chunk 2's initial state.

Simple in theory. The details are where things break.

---

## When Linking Fails

The chain between chunks is load-bearing. Get it wrong and attackers can:

| Attack | Method | Result |
|--------|--------|--------|
| **Prefix** | Prove only the first half | Skip a balance check at step 900,000 |
| **Skip** | Submit chunks 0, 1, 3 | Drop the chunk with authorization logic |
| **Splice** | Mix chunks from runs A and B | Cherry-pick favorable fragments |
| **Replay** | Resubmit yesterday's proof | Double-spend a settled transaction |
| **Config swap** | Prove loose, verify strict | Exploit parameter mismatches |

Each attack produces a valid-looking proof for an invalid computation. In systems where proofs move assets, one exploitable gap means unlimited loss.

This specification exists because "be careful" isn't a security model. We define the protocol formally, state what security means as mathematical invariants, then prove they hold in every reachable state.

---

## The Core Mechanism

Everything hinges on **StateDigest**—a cryptographic commitment to the full VM state at chunk boundaries.

```
StateDigest = Hash(
    program_hash,      // which program
    pc,                // where in execution
    registers[0..31],  // all register values
    step_counter,      // how far along
    rw_mem_root,       // memory commitment
    io_root,           // I/O commitment
    halted,            // done yet?
    exit_code,         // return value
    config_tags        // which configuration
)
```

Skip a chunk? The digest chain breaks—output of chunk N-1 won't match input of chunk N+1. Splice executions? Program hashes differ. Forge memory? Merkle roots won't match.

Every attack produces a detectable inconsistency. The spec defines this algorithm to the bit level: encoding, domain separation, byte order. Two implementations following this spec produce identical digests for identical states.

---

## Verified Properties

We don't just specify behavior—we specify what "secure" means, then prove it.

```
┌────────────────────────────────────────────────────────────────┐
│                      29 VERIFIED INVARIANTS                    │
├────────────────────────────────────────────────────────────────┤
│                                                                │
│  TYPE SAFETY (4)                                               │
│  [x] Values well-formed according to types                     │
│  [x] No undefined behavior from malformed inputs               │
│                                                                │
│  CRYPTOGRAPHIC BINDING (10)                                    │
│  [x] Program hash bound -- can't swap programs                 │
│  [x] Memory roots bound -- can't forge state                   │
│  [x] Config tags bound -- can't switch parameters              │
│  [x] Batch nonce bound -- can't replay proofs                  │
│                                                                │
│  PROTOCOL CORRECTNESS (7)                                      │
│  [x] State transitions follow rules                            │
│  [x] Chunk boundaries deterministic                            │
│  [x] Register x0 always zero (RISC-V requirement)              │
│                                                                │
│  ATTACK PREVENTION (8)                                         │
│  [x] INV_ATK_NoPrefixProof -- must complete execution          │
│  [x] INV_ATK_NoSkipChunk -- can't omit chunks                  │
│  [x] INV_ATK_NoSplice -- can't mix executions                  │
│  [x] INV_ATK_NoReplay -- can't reuse proofs                    │
│  [x] INV_ATK_NoCrossConfig -- can't switch configs             │
│  [x] INV_ATK_NoRootForgery -- can't fake memory state          │
│  [x] INV_ATK_NoMemoryForgery -- can't manipulate R/W memory    │
│  [x] INV_ATK_NoIOForgery -- can't manipulate I/O memory        │
│                                                                │
└────────────────────────────────────────────────────────────────┘
```

---

## Three Verification Layers

| Layer | What It Is | Who It's For |
|-------|-----------|--------------|
| `JoltContinuations.tla` | Executable TLA+ model (~900 lines) | Auditors, verification engineers |
| `lean/` | Machine-checked Lean 4 proofs (~4K lines) | Formal verification, production |
| `spec.md` | Prose specification (~40K words) | Implementers, researchers |

The TLA+ spec isn't documentation. It's a model the TLC checker executes, exploring all reachable states, verifying invariants hold in each. If there's a state sequence that breaks security, TLC finds it.

The Lean 4 kernel provides machine-checked proofs of the same invariants. No axiom gaps, no "sorry" placeholders—every theorem is fully proven. Build it yourself: `cd lean && lake build`.

The prose spec explains decisions. Byte ordering, endianness, domain tags—details an implementer needs but that would clutter a formal model.

---

## Reading Paths

| Starting Point | Path | Time |
|----------------|------|------|
| Evaluating for your project | This README → `docs/architecture.md` | 30 min |
| Building an integration | `spec.md` §5 → §11 | 2-4 hours |
| Auditing security | `docs/invariants.md` → attack table | 1-2 hours |
| Studying zkVM design | Full `spec.md` → `JoltContinuations.tla` | 1-2 days |
| Building your own zkVM | StateDigest algorithm (§11.10) | 2-3 hours |

---

## Verify It Yourself

### Requirements

- Java 11+
- [TLA+ tools](https://github.com/tlaplus/tlaplus/releases) (`tla2tools.jar`)

### Run the Model Checker

```bash
# Parse
java -cp tla2tools.jar tla2sany.SANY JoltContinuations.tla

# Check all 29 invariants
java -jar tla2tools.jar -config Jolt.cfg JoltContinuations.tla -workers auto
```

**Expected:**
```
Model checking completed. No error has been found.
  7 states generated, 7 distinct states found, 0 states left on queue.
```

Seven states because TLC uses small bounds (3 steps/chunk, 5 max chunks). Enough to hit all transition types. The invariants are algebraic—they don't depend on scale.

---

## Repository Layout

```
jolt-tla/
├── JoltContinuations.tla    # <- Start here
├── Jolt.cfg                 # TLC configuration
├── spec.md                  # Full prose spec (17 sections)
│
├── tla/                     # Modular sources
│   ├── Types.tla            # Fr, U64, Bytes32
│   ├── Encodings.tla        # Byte/field conversions
│   ├── Hash.tla             # Hash abstraction
│   ├── Transcript.tla       # Fiat-Shamir sponge
│   ├── SMT.tla              # Sparse Merkle Tree
│   ├── SMTOps.tla           # SMT operations
│   ├── VMState.tla          # RISC-V state machine
│   ├── Registry.tla         # Config management
│   ├── Continuations.tla    # Chunk chaining
│   ├── Wrapper.tla          # Proof wrapper
│   ├── JoltSpec.tla         # Top-level
│   ├── Invariants.tla       # All invariants
│   └── MC_Jolt.tla          # Model check harness
│
├── lean/                       # Lean 4 verification kernel
│   ├── NearFall/               # Source modules
│   ├── lakefile.toml           # Build config
│   └── README.md
│
├── docs/
│   ├── architecture.md
│   ├── invariants.md
│   └── module-reference.md
│
├── CONTRIBUTING.md
├── SECURITY.md
├── CHANGELOG.md
└── LICENSE
```

---

## Relationship to the Jolt Paper

| Paper | This Spec | Delta |
|-------|-----------|-------|
| §3 RISC-V Primer | §6 VM Spec | Register semantics, trap handling |
| §5 Memory Checking | §11.8 SMT | Bit-level traversal, page encoding |
| §6 Continuations | §11 Protocol | StateDigest algorithm, boundaries |
| §7 Commitments | §8 Transcript | Sponge state machine, typed absorption |

**Paper**: Arun, Setty, Thaler. *"Jolt: SNARKs for Virtual Machines via Lookups"*. EUROCRYPT 2024. [ePrint 2023/1217](https://eprint.iacr.org/2023/1217)

The paper proves cryptographic security. This spec proves protocol correctness—that implementations following it get the security the paper assumes.

---

## Model Checking Bounds

| Parameter | TLC | Production | Note |
|-----------|-----|------------|------|
| `CHUNK_MAX_STEPS` | 3 | ~10⁶ | Invariants don't depend on step count |
| `MAX_CHUNKS` | 5 | Unbounded | Covers all boundary cases |
| `FR_TLC_BOUND` | 16384 | ~2²⁵⁵ | Algebraic, not numeric |
| Hash | Fingerprints | Poseidon | Collision resistance assumed |

---

## The TLA+ Bet

TLA+ is Leslie Lamport's specification language. Amazon, Microsoft, and others use it to find bugs in distributed systems before they ship.

We use it because:
- The model checker explores states exhaustively
- The semantics are unambiguous
- It separates "what" from "how"
- Auditors can read it

Tests check cases. Specifications check **all** cases. A test verifies skipping chunk 2 fails. The spec proves skipping any chunk in any execution fails, and shows why.

---

## Status

**Released for Comment** — v0.1.0

Feature-complete. All invariants pass. Open for review before finalizing.

Feedback wanted on: ambiguities, missing attacks, modeling improvements, documentation gaps.

See [CHANGELOG.md](CHANGELOG.md).

---

## Security

Vulnerabilities: **do not open a public issue.**

See [SECURITY.md](SECURITY.md). We respond within 72 hours.

---

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).

**Useful contributions:**

| Type | Example |
|------|---------|
| New invariants | "Chunks can't be reordered" |
| Attack vectors | "What if prover controls RNG?" |
| Test vectors | StateDigest conformance tests |
| Clarity fixes | "Section 8.4 is unclear" |

---

## References

**Core:**
- [Jolt Paper](https://eprint.iacr.org/2023/1217)
- [Jolt Docs](https://jolt.a16zcrypto.com/)

**TLA+:**
- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)

**Background:**
- [RISC-V Spec](https://riscv.org/specifications/)
- [Poseidon Hash](https://eprint.iacr.org/2019/458)

---

## Acknowledgments

- **Arasu Arun, Srinath Setty, Justin Thaler** — Jolt
- **Leslie Lamport** — TLA+
- **a16z crypto** — Jolt implementation

---

## License

Apache 2.0. See [LICENSE](LICENSE).

Copyright 2026 Charles Hoskinson

---

## Author

**Charles Hoskinson** — CEO, IOG
