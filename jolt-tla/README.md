# Jolt TLA+ Formal Specification

> **Machine-checkable security proofs for zkVM continuation semantics**

[![TLA+ CI](https://github.com/CharlesHoskinson/jolt-tla/actions/workflows/tlaplus.yml/badge.svg)](https://github.com/CharlesHoskinson/jolt-tla/actions/workflows/tlaplus.yml)
[![Lean CI](https://github.com/CharlesHoskinson/jolt-tla/actions/workflows/lean.yml/badge.svg)](https://github.com/CharlesHoskinson/jolt-tla/actions/workflows/lean.yml)
[![Version](https://img.shields.io/badge/version-0.3.1-blue)]()
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

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

## Why an Executable Spec Oracle?

Two teams implement the same protocol from the same prose spec. They agree on intent. But one serializes JSON keys alphabetically, the other preserves insertion order. One tolerates an extra field, the other rejects it. Both choices feel reasonable. Both pass their own tests.

Then their nodes meet on a live network. One accepts a block the other rejects. Consensus splits. Assets fork.

The oracle is the impartial referee. Feed it the same bundle, get the same digest—or the same rejection. Any discrepancy surfaces immediately, before it becomes a chain split.

**What makes it canonical?** The oracle enforces a unique, normalized representation. Hashes, signatures, and commitments have exactly one meaning and one byte-encoding. No wiggle room.

**What makes it executable?** It ships as runnable code. Anyone can invoke it. The answer to "what does correct mean here?" is not a debate—it's a function call.

```
oracle digest state.json
> 0x7a3f...c891

oracle verify chain continuation.json
> ✓ Chain valid: 5 chunks, digests link correctly
```

In distributed systems, ambiguity is not a nuisance. It is an attack surface and a fork mechanism. The oracle replaces interpretation with evaluation. When a transition is disputed, the oracle provides the single notion of truth: either invalid, or this exact result.

**Where oracles earn their keep:**

| Use Case | How |
|----------|-----|
| CI conformance gate | Generate golden vectors, check against them |
| Developer toolchain | Validate blocks, proofs, state transitions locally |
| Audit trail | Reproduce any historical computation |
| Cross-team alignment | One truth, many implementations |

The oracle is correctness-first and fail-closed. Malformed inputs get rejected, not "helpfully" normalized. Differences cannot be glossed over. They are forced into the open.

**What the oracle is not:** A production node optimized for throughput. A network simulator. It focuses on the deterministic functional core—given pre-state and inputs, compute post-state (or reject). That boundary keeps it small, auditable, and stable. When the rules change, you update one ground truth, and the ecosystem gets a new target to align against.

---

## What's New in v0.3.1

### Modular TLA+ Now Canonical

The modular specification (`tla/MC_Jolt.tla`) is now the canonical entrypoint:

- **19 TLA+ modules** with proper separation of concerns
- **CI updated** to use modular harness
- **Monolith generation** script for single-file deployments

### Registry Expanded to 17 Keys

`Registry.tla` now includes all required configuration keys per §3.4:

- **17 required keys**: `JOLT_POSEIDON_FR_V1` through `JOLT_WRAPPER_PROOF_SYSTEM_V1`
- **3 external handles**: Computed tags that MUST NOT appear in registry.json
- **Key format validation**: `^JOLT_[A-Z0-9_]+_V[0-9]+$`

### Status Enum Aligned with Lean

`status_fr` now uses Status enum `{0,1,2}` matching Lean Jolt implementation:

| Value | Meaning |
|-------|---------|
| 0 | SUCCESS (halted with exit_code = 0) |
| 1 | FAILURE (halted with exit_code > 0) |
| 2 | PENDING (not yet halted) |

### Domain Tags Centralized

All 17 domain tags now defined in `Hash.tla` with `IsValidTagFormat` validation:

- Tags must start with `JOLT/`
- Charset: `[A-Z0-9/_]`
- Cardinality verified by ASSUME

### New Modules

- **Tar.tla**: TAR archive validation per §14.3 (path safety, canonical ordering)
- **JSON.tla**: JSON safety constraints per §2.6.1 (safe integers, JCS)
- **Bundle.tla**: Conformance bundle structure (TAR + JSON + Registry)
- **RegistryValidationTests.tla**: 19 test cases for registry validation
- **TranscriptValidationTests.tla**: 28 test cases for transcript validation

---

## What's New in v0.3.0

### Poseidon Parameters Finalized

`JOLT_POSEIDON_FR_V1` is now fully specified (spec.md §3.4.1):

| Parameter | Value |
|-----------|-------|
| State width (t) | 3 |
| Rate (r) | 2 |
| Capacity (c) | 1 |
| Full rounds | 8 |
| Partial rounds | 60 |
| S-box | x⁵ |
| Field | BLS12-381/Fr |

MDS matrix and all 204 round constants are pinned. TBD count: 15 → 14.

### Midnight Wrapper Compatibility

`JOLT_WRAPPER_PROOF_SYSTEM_V1` adds Midnight-compatible proof wrapping:

- **Curve**: BLS12-381
- **PCS**: KZG with k=14 (domain size 16384)
- **Wire format**: `proof[v5]`, `verifier-key[v6]`
- **Public inputs**: 11 elements in specified order
- **Nonce replay protection**: Built-in

New TLA+ validation module: `WrapperValidationTests.tla` (15 test cases).

### Oracle CLI

Executable specification with interactive REPL. See [Oracle CLI](#oracle-cli-1) section below.

---

## Verified Properties

We don't just specify behavior—we specify what "secure" means, then prove it.

```
┌────────────────────────────────────────────────────────────────┐
│                      30 VERIFIED INVARIANTS                    │
├────────────────────────────────────────────────────────────────┤
│                                                                │
│  TYPE SAFETY (5)                                               │
│  [x] Values well-formed according to types                     │
│  [x] No undefined behavior from malformed inputs               │
│  [x] Poseidon parameters valid per §3.4.1                      │
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
| `tla/MC_Jolt.tla` | Modular TLA+ spec (19 modules, canonical) | Auditors, verification engineers |
| `lean/` | Machine-checked Lean 4 kernel + Oracle CLI (~8K lines) | Formal verification, production |
| `spec.md` | Prose specification (~40K words) | Implementers, researchers |

The TLA+ spec isn't documentation. It's a model the TLC checker executes, exploring all reachable states, verifying invariants hold in each. If there's a state sequence that breaks security, TLC finds it.

The Lean 4 kernel provides machine-checked proofs of the same invariants. No axiom gaps, no "sorry" placeholders—every theorem is fully proven. Build it yourself: `cd lean && lake build`.

The prose spec explains decisions. Byte ordering, endianness, domain tags—details an implementer needs but that would clutter a formal model.

---

## Why Three Layers?

Each layer answers a different question and catches bugs the others cannot.

**The prose spec** answers "what and why." It uses RFC 2119 keywords (MUST, SHOULD, MAY) to specify obligations. When you need to understand what a valid state looks like or why the digest includes config_tags, read spec.md. The prose catches ambiguity and missing requirements—but it can't execute, so it can't tell you if two implementations agree.

**The TLA+ model** answers "can this go wrong?" TLC explores all reachable states and checks that no sequence of operations violates security invariants. When TLC fails, it produces a counterexample trace showing the exact operations that reach a bad state. The model catches design bugs before any code exists—but it uses finite bounds, so it can't check properties at production scale.

**The Lean oracle** answers "what's the right answer?" Feed it a state, get the one correct digest. If your implementation produces a different digest, your implementation is wrong. The oracle catches implementation drift and byte-level edge cases—but it executes one path at a time, so it can't model-check all possible interleavings.

Together they form a defense-in-depth verification strategy:

```
┌─────────────────────────────────────────────────────────────────┐
│                     NORMATIVE HIERARCHY                          │
│                                                                  │
│                    ┌──────────────┐                              │
│                    │  PROSE SPEC  │  ← Authoritative              │
│                    │   spec.md    │    (RFC 2119: MUST/SHOULD)   │
│                    └──────┬───────┘                              │
│                           │                                      │
│              ┌────────────┴────────────┐                         │
│              │                         │                         │
│              ▼                         ▼                         │
│     ┌────────────────┐       ┌────────────────┐                  │
│     │   TLA+ MODEL   │       │  LEAN ORACLE   │                  │
│     │   (verifies)   │◄─────►│  (executes)    │                  │
│     └────────┬───────┘       └────────┬───────┘                  │
│              │                        │                          │
│              ▼                        ▼                          │
│       TLC Results               Golden Vectors                   │
│    "All invariants hold"      (conformance tests)                │
│                                                                  │
│  CONFLICT RESOLUTION:                                            │
│  • Prose wins → update TLA+/Lean                                 │
│  • TLA+ ≠ Lean → bug in one of them, check prose                 │
│  • Missing case → prose underspecified, file spec issue          │
└─────────────────────────────────────────────────────────────────┘
```

When the artifacts disagree, prose is authoritative. If TLA+ or Lean conflicts with the prose spec, the formal artifact has a bug. If TLA+ and Lean conflict with each other, check both against prose to find which one diverged.

---

## Using the Outputs

**Reading the prose.** Look up requirements by section number. §11.5 describes VMStateV1 fields. §2.2.1 specifies Fr2 encoding. Error codes like E501 are defined in `Jolt/Errors.lean`. When you disagree with a behavior, check the spec first—it's the source of truth.

**Interpreting TLC results.** TLC either passes or fails. When it passes, you get confirmation that all invariants hold across all explored states:

```
Model checking completed. No error has been found.
  7 states generated, 7 distinct states found, 0 states left on queue.
```

When it fails, you get a counterexample trace:

```
Error: Invariant INV_ATK_NoSkipChunk is violated.
Trace:
  State 1: <Init> chunks = <<>>
  State 2: <AddChunk> chunks = <<[idx: 0, digest: "abc"]>>
  State 3: <AddChunk> chunks = <<[idx: 0, digest: "abc"], [idx: 2, digest: "xyz"]>>
           ^^^^^^^^ chunk index skipped from 0 to 2
```

Read the trace from top to bottom. Each state shows what operation was taken and the resulting system state. The violation tells you which invariant broke. Fix the model or the spec, then re-run until all invariants pass.

**Using the oracle.** The oracle computes canonical values. Run it on the same input as your implementation and compare:

```bash
# Compute the correct digest for a state
$ lake exe oracle digest state.json
{ "status": "ok", "digest": "0x7a3f...c891" }

# Validate a continuation chain
$ lake exe oracle verify chain.json
{ "status": "error", "code": "E501", "message": "Chunk 1 start_digest != chunk 0 end_digest" }

# Generate test vectors for your CI (all-zeros state)
$ lake exe oracle generate state_digest input.json > golden.json
```

If your Rust/Go/TypeScript implementation produces a different digest than the oracle, your implementation is wrong. The oracle is the referee.

---

## Verify It Yourself

### Requirements

- Java 17+
- TLA+ tools v1.8.0 (pinned for reproducibility)

### Download TLA+ Tools

```bash
# Download pinned version
curl -fsSL -o tla2tools.jar \
  https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar

# Verify checksum (SHA256)
# Expected: 5ff9dcd6a1bcae6a62a0d654e39659c8a2e577fed90b3ef464d1752a48b2be5b
sha256sum tla2tools.jar
```

### Run the Model Checker

```bash
# Parse (canonical modular entrypoint)
java -cp tla2tools.jar tla2sany.SANY tla/MC_Jolt.tla

# Check all 30 invariants
java -XX:+UseParallelGC -Xmx4g -jar tla2tools.jar \
  -config Jolt.cfg tla/MC_Jolt.tla -workers auto
```

**Expected:**
```
Model checking completed. No error has been found.
  7 states generated, 7 distinct states found, 0 states left on queue.
```

Seven states because TLC uses small bounds (3 steps/chunk, 5 max chunks). Enough to hit all transition types. The invariants are algebraic—they don't depend on scale.

### Continuous Integration

Every push runs TLA+ verification via GitHub Actions. See `.github/workflows/tlaplus.yml`. Artifacts include full TLC output showing which invariants were checked.

---

## Repository Layout

```
jolt-tla/
├── JoltContinuations.tla    # <- Start here
├── Jolt.cfg                 # TLC configuration
├── WrapperValidation.cfg    # Wrapper tests config
├── spec.md                  # Full prose spec (17 sections)
│
├── .github/workflows/       # CI pipelines
│   ├── tlaplus.yml          # TLA+ verification
│   └── lean.yml             # Lean 4 build
│
├── tla/                     # Modular TLA+ sources (canonical)
│   ├── Types.tla            # Fr, U64, Bytes32
│   ├── Encodings.tla        # Byte/field conversions
│   ├── Hash.tla             # Hash + 17 domain tags (centralized)
│   ├── Transcript.tla       # Fiat-Shamir sponge + type tags
│   ├── SMT.tla              # Sparse Merkle Tree
│   ├── SMTOps.tla           # SMT operations
│   ├── VMState.tla          # RISC-V state machine
│   ├── Registry.tla         # 17 keys + 3 external handles
│   ├── Continuations.tla    # Chunk chaining
│   ├── Wrapper.tla          # Proof wrapper + Status enum
│   ├── Tar.tla              # TAR archive validation (§14.3)
│   ├── JSON.tla             # JSON safety + JCS (§2.6.1)
│   ├── Bundle.tla           # Conformance bundle structure
│   ├── RegistryValidationTests.tla   # Registry test cases
│   ├── TranscriptValidationTests.tla # Transcript test cases
│   ├── WrapperValidationTests.tla    # 15 validation tests
│   ├── JoltSpec.tla         # Top-level composition
│   ├── Invariants.tla       # All 30 invariants
│   └── MC_Jolt.tla          # Model check harness (canonical)
│
├── lean/                    # Lean 4 executable spec
│   ├── Jolt/                # Core modules
│   │   ├── Encoding/        # Bytes32, Fr2
│   │   ├── Field/           # Fr arithmetic
│   │   ├── JSON/            # JCS, Parser
│   │   ├── Poseidon/        # Hash implementation
│   │   ├── Registry/        # Config validation
│   │   ├── State/           # VMState, Digest
│   │   ├── Transcript/      # Fiat-Shamir sponge
│   │   └── Wrapper/         # Public inputs
│   ├── CLI/                 # Oracle CLI
│   │   ├── Commands/        # digest, verify, etc.
│   │   └── REPL/            # Interactive mode
│   ├── NearFall/            # Proof modules
│   ├── Jolt.lean            # Library root
│   ├── lakefile.lean        # Build config
│   └── README.md
│
├── docs/
│   ├── architecture.md
│   ├── invariants.md
│   ├── alignment.md         # TLA/Lean/spec alignment matrix
│   └── module-reference.md
│
├── scripts/
│   ├── check_alignment.sh   # CI diff-check for constants
│   └── generate_monolith.sh # Generate single-file TLA
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

## Oracle CLI

The Jolt Oracle is an executable specification that computes canonical digests and verifies continuation chains.

### Build

```bash
cd lean
lake build
```

### Commands

```bash
# Health check
lake exe oracle status

# Compute state digest from JSON
lake exe oracle digest state.json

# Verify continuation chain
lake exe oracle verify chain continuation.json

# Generate test vectors
lake exe oracle generate vectors --count 10

# Interactive REPL
lake exe oracle repl
```

### REPL Commands

```
jolt> help              # Show available commands
jolt> load state.json   # Load a state file
jolt> digest            # Compute digest of loaded state
jolt> verify            # Verify current chain
jolt> set field value   # Modify state fields
jolt> show              # Display current state
jolt> quit              # Exit REPL
```

---

## Status

**Released** — v0.3.1

Feature-complete with executable specification. All 30 invariants pass. Oracle CLI provides conformance testing. TLA+ aligned with Lean Jolt oracle (Status enum, 17 registry keys, 17 domain tags).

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
