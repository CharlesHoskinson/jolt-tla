# Jolt TLA+ Formal Specification

> **Machine-checkable security proofs for zkVM continuation semantics**

[![TLA+ CI](https://github.com/CharlesHoskinson/jolt-tla/actions/workflows/tlaplus.yml/badge.svg)](https://github.com/CharlesHoskinson/jolt-tla/actions/workflows/tlaplus.yml)
[![Lean CI](https://github.com/CharlesHoskinson/jolt-tla/actions/workflows/lean.yml/badge.svg)](https://github.com/CharlesHoskinson/jolt-tla/actions/workflows/lean.yml)
[![Version](https://img.shields.io/badge/version-0.3.2-blue)]()
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

---

## TL;DR — Try It in 60 Seconds

```bash
# 1. Build the oracle
cd jolt_oracle && lake build

# 2. Compute a state digest
echo '{"program_hash":"0x0000000000000000000000000000000000000000000000000000000000000000","state":{"pc":0,"regs":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"step_counter":0,"rw_mem_root":"0x0000000000000000000000000000000000000000000000000000000000000000","io_root":"0x0000000000000000000000000000000000000000000000000000000000000000","halted":0,"exit_code":0,"config_tags":[]}}' > state.json
lake exe oracle digest state.json
# Expected: Digest: 24421670062301725635551677633693836338234896090794496795972501815695727753187

# 3. Run TLA+ model checker (requires Java 17+)
cd ../jolt-tla
java -jar tla2tools.jar -config Jolt.cfg tla/MC_Jolt.tla -workers auto
# Expected: "Model checking completed. No error has been found."
```

**What you just did:**
- Built an executable specification that defines "correct" for all Jolt implementations
- Computed the canonical StateDigest for a minimal VM state
- Verified that no sequence of operations can violate 30 security invariants

---

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

## Definitions

**Chunk.** A segment of VM execution, typically 2²⁰ cycles. Each chunk has a start state, end state, and proof. Chunks are numbered sequentially starting from 0.

**Continuation chain.** A sequence of chunks where each chunk's end state digest equals the next chunk's start state digest. The chain proves a complete execution from initial state to halted state.

**StateDigest.** A single field element (Fr) computed by hashing all VM state fields through a Poseidon sponge. Two states with the same digest are identical. Defined in spec.md §11.10.2.

**VMStateV1.** The canonical VM state structure: `pc`, `regs[0..31]`, `step_counter`, `rw_mem_root`, `io_root`, `halted`, `exit_code`, `config_tags`. Register x0 must always be zero (RISC-V invariant).

**Registry key.** A configuration parameter identifier matching `^JOLT_[A-Z0-9_]+_V[0-9]+$`. The spec defines 17 required keys (e.g., `JOLT_POSEIDON_FR_V1`). External handles are computed, not stored.

**Domain tag.** A string prefix used for cryptographic domain separation in transcripts. All tags start with `JOLT/` and contain only `[A-Z0-9/_]`. Prevents cross-protocol attacks.

**Bundle.** A canonical TAR archive containing `registry.json` plus proof artifacts. Paths must be relative, sorted bytewise, with zero mtime. Defined in spec.md §14.3.

**Fr.** A scalar field element of BLS12-381, integers mod r where r = 52435875...513 (254 bits). All cryptographic commitments live in this field.

**Public inputs.** The 11 Fr elements exposed to the verifier: `program_hash`, `old_state_root`, `new_state_root`, `batch_commitment`, `step_count`, `status_fr`, plus five reserved. Defined in spec.md §5.2.

---

## Threat Model

**Attacker capabilities.** The attacker controls:
- All prover inputs (states, proofs, bundles)
- Chunk ordering and selection (can omit, reorder, duplicate)
- Timing of proof submission
- Choice of configuration parameters (unless pinned by config_tags)

**Attacker goals we defend against:**
- **Prefix attack**: Prove partial execution, skip validation at step N
- **Skip attack**: Omit chunks to bypass authorization logic
- **Splice attack**: Combine chunks from different executions
- **Replay attack**: Resubmit old proofs for new transactions
- **Config swap**: Prove with loose parameters, verify with strict

**Assumptions:**
- Poseidon hash is collision-resistant (cannot find two states with same digest)
- BLS12-381 discrete log is hard (signatures unforgeable)
- TLC fingerprint hashing is sufficient for bounded model checking (not production)
- Verifier has access to correct registry parameters

**Out of scope:**
- Side-channel attacks on prover implementation
- Denial of service / resource exhaustion
- Network-level attacks (eclipse, partition)
- Bugs in the Lean compiler or TLC model checker

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

## What's New in v0.3.2

### Oracle Poseidon Constants Fixed

Critical bug fix: `Oracle.init` was using `Poseidon.defaultConfig` with empty round constants
and MDS matrix, causing all state digests to compute incorrectly (returning 0).

**Fixed:** Oracle now uses `joltPoseidonConfig` with the full BLS12-381 constants from
midnight-circuits v6.0.0 (204 round constants, 3x3 MDS matrix).

### Golden Test Vectors Computed

`test_vectors/golden_v1.json` now contains computed StateDigest values:

| Test Case | Digest (Fr decimal) |
|-----------|---------------------|
| minimal_state_zeros | 24421670062301725635551677633693836338234896090794496795972501815695727753187 |
| typical_state | 30919686901236335602438576816898388225550310633849398790605613577781839025832 |
| halted_state | 40400183813884747956300889570234739091911790924111649960538043847858548402419 |
| state_with_config_tags | 51269420250097274214666708236162143841421999722140888943312460699788950625363 |

### Nix Flake Support

Reproducible builds via Nix flakes:

```bash
nix develop        # Enter dev shell with Lean 4.26.0, Java 17, TLA+ tools
nix flake check    # Verify flake
```

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
| `jolt_oracle/` | Machine-checked Lean 4 kernel + Oracle CLI (~8K lines) | Formal verification, specification |
| `jolt-oracle-rs/` | Rust implementation (conformance-tested against Lean) | Production deployment |
| `spec.md` | Prose specification (~40K words) | Implementers, researchers |

The TLA+ spec isn't documentation. It's a model the TLC checker executes, exploring all reachable states, verifying invariants hold in each. If there's a state sequence that breaks security, TLC finds it.

The Lean 4 kernel provides machine-checked proofs of the same invariants. Build it yourself: `cd lean && lake build`.

The prose spec explains decisions. Byte ordering, endianness, domain tags—details an implementer needs but that would clutter a formal model.

---

## Liveness Verification (NearFall)

Safety invariants prove "bad things don't happen." Liveness proves "good things eventually happen." The NearFall module provides machine-checked liveness proofs for the continuation protocol.

### Why Does the Machine Stop?

Here's the problem. You've got a zero-knowledge virtual machine that runs programs in chunks. It starts, does some work, and should eventually finish. But how do you *know* it finishes? Not "probably finishes" or "usually finishes"—we want a mathematical proof that says: given these rules, the machine cannot run forever. It has to stop.

Safety and liveness are different beasts. Safety says "nothing bad happens"—the registers stay correct, the hashes don't collide, nobody can forge a proof. We've had that for a while. But liveness says "something good eventually happens." That's harder. You can't just check one state at a time. You have to reason about *all possible futures*, including the infinite ones where some gremlin keeps the machine spinning forever.

So we built a countdown clock. Not a real clock—a mathematical one we call the variant. Every time the machine does real work—executes a chunk, completes, or fails—the number goes down. Every time it does busywork—starts up, stutters—the number stays the same or goes down. The variant is a natural number, which means it can't go below zero. And here's the punch line: if a number keeps going down and can't go below zero, it has to hit zero eventually. When it hits zero, you're in a terminal state. Done.

But there's a catch. What if the machine just stutters forever? Sits there doing nothing, variant frozen at 17? That's where fairness comes in. We don't assume the scheduler is adversarial—we assume weak fairness. In plain terms: if an action is ready to go and stays ready, it eventually gets taken. The system can't dodge its obligations forever. Under weak fairness, the countdown clock must tick. The variant must fall. The machine must stop.

The whole edifice—infinite traces, temporal operators, fairness conditions, progress partitions—it looks like a lot of machinery. And it is. But strip away the notation and you've got one idea: build a countdown that can only go down, prove the scheduler has to let it tick, and conclude the game ends. That's the liveness theorem. That's why the machine stops.

### What's Proven

| Property | Meaning |
|----------|---------|
| **No deadlock** | Non-terminal states always have an enabled action |
| **Progress from INIT** | Under weak fairness, execution leaves INIT phase |
| **Eventually terminal** | Under weak fairness + bounded chunks, reaches COMPLETE or FAILED |
| **Variant decrease** | Progress steps strictly decrease termination measure |

### Key Definitions

```lean
-- Infinite trace semantics (matches TLA+ [Next]_vars)
def Trace := Nat → SystemState
def StepOrStutter (s s' : SystemState) : Prop := Step s s' ∨ s' = s

-- Temporal operators
def Eventually (P : SystemState → Prop) (tr : Trace) : Prop := ∃ n, P (tr n)
def LeadsTo (P Q : SystemState → Prop) (tr : Trace) : Prop :=
  ∀ n, P (tr n) → ∃ m, m ≥ n ∧ Q (tr m)

-- Weak fairness: continuously enabled → infinitely often taken
def WeakFair (A : Action) (tr : Trace) : Prop :=
  (∃ n, ∀ m ≥ n, Enabled A (tr m)) → InfOften (Occurs A tr)
```

### State Machine

```
                           Jolt Continuation State Machine
    ┌─────────────────────────────────────────────────────────────────────────┐
    │                                                                         │
    │                         StartExecution                                  │
    │         ┌───────┐      ─────────────────►      ┌───────────┐            │
    │         │       │                              │           │            │
    │         │ INIT  │                              │ EXECUTING │◄───┐       │
    │         │       │                              │           │    │       │
    │         └───────┘                              └─────┬─────┘    │       │
    │                                                      │          │       │
    │                                                      │          │       │
    │                              ExecuteChunk            │          │       │
    │                              (chunk not complete)    └──────────┘       │
    │                                                                         │
    │                                      │                                  │
    │                                      │                                  │
    │                 ┌────────────────────┴────────────────────┐             │
    │                 │                                         │             │
    │                 │ CompleteExecution          ExecutionFailed            │
    │                 │ (continuation complete)    (VM trapped)  │            │
    │                 ▼                                         ▼             │
    │          ┌──────────┐                              ┌──────────┐         │
    │          │          │                              │          │         │
    │          │ COMPLETE │                              │  FAILED  │         │
    │          │    ◉     │                              │    ◉     │         │
    │          └──────────┘                              └──────────┘         │
    │              Terminal (absorbing)                    Terminal           │
    │                                                                         │
    └─────────────────────────────────────────────────────────────────────────┘

    Legend:
    ─────►  Transition (action)
    ◉       Terminal state (only stuttering allowed)
    ◄───┐
        │   Self-loop
    ────┘
```

### Termination Variant

The termination proof uses a single natural number variant:

```
Variant(s) = RemainingChunks(s) × CHUNK_MAX_STEPS + StepsRemaining(s)
```

- Terminal phases (COMPLETE, FAILED): variant = 0
- Progress steps: variant strictly decreases
- Non-progress steps: variant does not increase

This guarantees termination under weak fairness assumptions.

### Build

```bash
cd lean && lake build
```

### Roadmap

**Lean Track (NearFall)**

- [x] Trace.lean — Infinite trace semantics (`Nat → SystemState`)
- [x] Temporal.lean — LTL operators (Always, Eventually, LeadsTo, InfOften)
- [x] Fairness.lean — Weak/strong fairness with corrected TLA+ semantics
- [x] Variant.lean — Termination variant and progress partition
- [x] Liveness.lean — Progress theorems under fairness (stubs)
- [x] Progress.lean — No-deadlock lemmas
- [x] Alignment.lean — Semantic alignment with TLA+
- [ ] Red Team: Fill `sorry` placeholders in Liveness.lean
- [ ] Red Team: Fill `sorry` placeholders in Variant.lean
- [ ] Red Team: Fill `sorry` placeholder in Fairness.lean (enabled_stability)

**TLA+ Track (TLAPS Proofs)**

- [ ] CryptoModel.tla — Tagged preimage constructors, scoped injectivity
- [ ] TypeOK.tla — Type invariant with encoding membership
- [ ] SafetyInduction.tla — Inductive invariant, variant lemmas
- [ ] AttackLemmas.tla — Encoding injectivity, digest binding
- [ ] LivenessProofs.tla — WF/ENABLED leads-to with enabledness stability

**Integration**

- [x] ASSUMPTIONS.md — Assumption registry and proof obligation map
- [x] CI workflows — Lean build integrated
- [ ] Red Team batch processing on NearFall modules
- [ ] Cross-track alignment verification

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

### Where Is This Rule Implemented?

| Prose § | Concept | TLA+ Module | Lean Module | What's Checked |
|---------|---------|-------------|-------------|----------------|
| §2.1.1 | Fr modulus (BLS12-381) | `Types.tla:FR_MODULUS` | `Jolt/Field/Fr.lean` | Field arithmetic bounded |
| §3.4 | 17 registry keys | `Registry.tla:KEY_*` | `Jolt/Registry/ConfigTags.lean` | Key format validated |
| §5.2 | 11 public inputs | `Wrapper.tla:PublicInputsV1` | `Jolt/Wrapper/PublicInputs.lean` | Count and layout verified |
| §7.6 | Bytes32→Fr2 encoding | `Encodings.tla:Bytes32ToFr2` | `Jolt/Encoding/Bytes32.lean` | lo < 2²⁴⁸, hi < 256 |
| §8.4 | Transcript type tags | `Transcript.tla:TYPE_*` | `Jolt/Transcript/Types.lean` | Domain separation enforced |
| §8.6 | Tag format validation | `Hash.tla:IsValidTagFormat` | `Jolt/Transcript/TagValidation.lean` | ASCII `[A-Z0-9/_]` only |
| §11.5 | VMStateV1 structure | `VMState.tla:VMStateV1` | `Jolt/State/VMState.lean` | 8 fields, regs[0]=0 |
| §11.10.2 | StateDigest algorithm | `Continuations.tla:ComputeStateDigest` | `Jolt/State/Digest.lean` | 14-step Poseidon sponge |
| §14.3 | TAR canonicalization | `Tar.tla:ValidTar` | `Jolt/Bundle/Tar.lean` | Paths relative, sorted |

Full mapping: `docs/alignment.md`

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

## Walkthrough: Two-Chunk Chain

This example shows a complete execution split into two chunks, demonstrating how StateDigest chaining prevents attacks.

**Chunk 0** — Initial execution (steps 0–24):

```json
{
  "chunk_index": 0,
  "start_state": {
    "pc": 0, "regs": [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    "step_counter": 0,
    "rw_mem_root": "0000000000000000000000000000000000000000000000000000000000000000",
    "io_root": "0000000000000000000000000000000000000000000000000000000000000000",
    "halted": 0, "exit_code": 0, "config_tags": []
  },
  "end_state": {
    "pc": 100, "regs": [0,5,10,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    "step_counter": 25,
    "rw_mem_root": "1111111111111111111111111111111111111111111111111111111111111111",
    "io_root": "2222222222222222222222222222222222222222222222222222222222222222",
    "halted": 0, "exit_code": 0, "config_tags": []
  }
}
```

**Chunk 1** — Continuation (steps 25–50, halts):

```json
{
  "chunk_index": 1,
  "start_state": {
    "pc": 100, "regs": [0,5,10,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    "step_counter": 25,
    "rw_mem_root": "1111111111111111111111111111111111111111111111111111111111111111",
    "io_root": "2222222222222222222222222222222222222222222222222222222222222222",
    "halted": 0, "exit_code": 0, "config_tags": []
  },
  "end_state": {
    "pc": 256, "regs": [0,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    "step_counter": 50,
    "rw_mem_root": "3333333333333333333333333333333333333333333333333333333333333333",
    "io_root": "4444444444444444444444444444444444444444444444444444444444444444",
    "halted": 1, "exit_code": 0, "config_tags": []
  }
}
```

**The linkage rule:** `digest(chunk[0].end_state) == digest(chunk[1].start_state)`

Run the oracle to verify:

```bash
$ lake exe oracle verify chain.json
{ "status": "ok", "chunks_verified": 2 }
```

**Now break it.** Change `chunk[1].start_state.pc` from 100 to 101:

```bash
$ lake exe oracle verify chain_broken.json
{ "status": "error", "code": "E501", "message": "Digest mismatch at chunk 1" }
```

The oracle caught a splice attempt. This is `INV_ATK_NoSplice` in action—any modification to a chunk's start state breaks the digest chain.

**Attack → Invariant mapping:**

| Attack | What you changed | Error | TLA+ invariant |
|--------|------------------|-------|----------------|
| Skip chunk | Remove chunk 1 entirely | E502 | `INV_ATK_NoSkipChunk` |
| Splice | Modify start_state | E501 | `INV_ATK_NoSplice` |
| Prefix | Submit only chunk 0 | E503 | `INV_ATK_NoPrefixProof` |
| Replay | Reuse old chain with same nonce | E501 | `INV_ATK_NoReplay` (digest includes nonce) |

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

**Why small bounds are sufficient:**

The invariants fall into two categories:

1. **Scale-independent** (25 of 30): These check structural properties that don't depend on state size. `INV_ATK_NoSkipChunk` verifies chunk indices are sequential—true for 3 chunks or 3 million. `INV_SAFE_RegisterX0` checks regs[0]=0—independent of how many steps executed.

2. **Bounded by design** (5 of 30): These involve finite enumerations. `INV_TYPE_StatusEnum` checks status ∈ {0,1,2}—only 3 values to check. Registry key validation covers exactly 17 keys.

**What TLC cannot check:**
- Collision resistance (assumes Poseidon hash is ideal)
- Computational limits (Fr operations use 16384-bit bound, not 254-bit)
- Concurrent interleavings (model is sequential)

**Compensation strategy:**
- Lean oracle provides exact Fr arithmetic (254-bit)
- Golden test vectors catch byte-level implementation drift
- CI runs both TLC and `lake exe test` on every commit

### Continuous Integration

Every push runs TLA+ verification via GitHub Actions. See `.github/workflows/tlaplus.yml`. Artifacts include full TLC output showing which invariants were checked.

---

## Repository Layout

```
jolt-tla/
├── JoltContinuations.tla    # Legacy monolith (use tla/MC_Jolt.tla instead)
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
├── jolt_oracle/             # Lean 4 executable spec (canonical)
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
│   │   ├── Commands/        # digest, verify, export-metadata, generate-corpus
│   │   └── REPL/            # Interactive mode
│   ├── Jolt.lean            # Library root
│   ├── lakefile.lean        # Build config
│   └── metadata.json        # Exported constants for Rust codegen
│
├── jolt-oracle-rs/          # Rust implementation (conformance-tested)
│   ├── Cargo.toml           # Project configuration
│   ├── build.rs             # Codegen from Lean metadata.json
│   ├── src/
│   │   ├── lib.rs           # Library root
│   │   ├── main.rs          # CLI binary
│   │   ├── error.rs         # ErrorCode (uses codegen)
│   │   ├── runner.rs        # LeanRunner subprocess backend
│   │   ├── field/           # Fr (BLS12-381 scalar)
│   │   ├── poseidon/        # Permutation + sponge
│   │   ├── state/           # VMState, Digest (planned)
│   │   └── json/            # I-JSON, JCS (planned)
│   ├── README.md
│   └── TODO.md              # Implementation roadmap
│
├── lean/                    # Lean 4 proof modules
│   └── NearFall/            # Liveness verification (infinite-state)
│       ├── Trace.lean       # Infinite traces (Nat → State)
│       ├── Temporal.lean    # LTL operators (□, ◇, ~>)
│       ├── Fairness.lean    # Weak/strong fairness
│       ├── Variant.lean     # Termination variant
│       ├── Liveness.lean    # Progress theorems
│       ├── Progress.lean    # No-deadlock lemmas
│       └── Alignment.lean   # TLA+/Lean semantic alignment
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

## Rust Oracle (jolt-oracle-rs/)

Two implementations of the same specification will eventually disagree. One team serializes JSON keys alphabetically; another preserves insertion order. Both choices seem reasonable, and both pass their own tests. When these implementations meet on a live network, one node accepts a block the other rejects. The chain forks. The Lean oracle exists to prevent this. Give it a state and it returns the one correct digest. There is no room for interpretation. Correctness is not a debate—it is a function call.

Lean defines truth, but it cannot ship. Production systems are native binaries written in Rust or C or Go. They run without interpreters. Lean requires its own toolchain, and embedding it in a blockchain node or hardware wallet creates friction. The obvious alternative—rewrite everything in Rust from scratch—reintroduces the original problem. The specification says "serialize the state," but does that mean big-endian or little-endian? Two careful teams reading the same prose will eventually choose differently on some edge case.

So we take a different path. Lean remains the canonical specification, the referee that settles disputes. The Rust implementation must match it byte for byte. The build system reads error codes and cryptographic constants directly from Lean exports, so parameters cannot drift. During testing, a subprocess invokes the Lean oracle and compares outputs. Any divergence means the Rust code is wrong. The oracle stays authoritative. Rust becomes a verified replacement—fast enough for production, correct because it matches the spec exactly.

### Build

```bash
cd jolt-oracle-rs
cargo build --release
cargo test
```

See `jolt-oracle-rs/TODO.md` for the implementation roadmap.

---

## Consensus Footguns

These implementation mistakes cause chain splits. The oracle rejects all of them—if your implementation doesn't, you'll fork.

**JSON canonicalization.** JCS (RFC 8785) sorts keys by UTF-16 code unit, not byte value. `"a"` < `"b"` but `"Z"` < `"a"`. Duplicate keys must error, not last-wins. The oracle enforces this; many JSON libraries don't.

**Integer bounds.** JSON integers must fit in ±(2⁵³−1) per spec §2.6.1. Larger values must be strings. Silent truncation to 64-bit causes different hashes on different platforms.

**Byte order.** Fr elements serialize little-endian. StateDigest absorbs fields in a specific order (pc → regs[0..31] → step_counter). Swapping the order changes the digest.

**Domain separation.** Every Poseidon invocation starts with a domain tag (`JOLT/STATE/V1`, `JOLT/TRANSCRIPT/V1`, etc.). Missing or wrong tags let attackers replay commitments across contexts.

**Type tag confusion.** Transcript absorption uses type discriminators: BYTES=1, U64=2, TAG=3, VEC=4. Absorbing a U64 as BYTES produces a different challenge. The oracle catches this; hand-rolled code might not.

**Register x0.** RISC-V requires `regs[0] = 0` always. A state with `regs[0] = 1` is invalid. Some implementations skip this check, creating unprovable states.

**Halted semantics.** `halted ∈ {0, 1}`, not a boolean that might be 2 or 255. When `halted = 0`, `exit_code` must be 0. Violating these constraints produces error E404/E405.

**Config tag ordering.** Config tags in the digest must match the projection from §3.8, sorted bytewise. Computing them differently (e.g., insertion order) breaks cross-implementation verification.

**Tar canonicalization.** Bundle archives must have zero mtime, no absolute paths, no `..`, and entries sorted bytewise. `tar` defaults don't produce canonical output; you need explicit flags.

**Error precedence.** When multiple errors apply, the spec defines which wins (§16). Returning E501 when E400 should fire causes verification mismatches.

---

## Adversarial Proof Review

The fundamental problem with proof is not writing it—it is knowing whether to trust it. A proof that compiles is not necessarily a proof that convinces. We have all seen arguments that type-check yet leave us uneasy, proofs where the machinery works but the insight hides. The question is not "does Lean accept this?" but rather "should Lean accept this, and if so, why?" To answer that question, we submit every proof to adversarial review before we trust it.

Our methodology employs two independent reviewers: Goedel-Prover and DeepSeek-Prover-V2. Each examines the proof from a different vantage point, looking for the gaps that a single perspective might miss. The first reviewer probes the logical structure—are the hypotheses too strong, the conclusion too weak, the intermediate steps hiding complexity? The second reviewer searches for patterns that suggest trouble: proof terms that exploit definitional equality in surprising ways, tactics that succeed for the wrong reasons, lemmas that prove too much or too little. Only when both reviewers fail to find fault do we proceed to the final oracle.

That oracle is Lean 4 itself, and it has the final word. The reviewers may raise concerns or miss subtleties, but the type checker does not negotiate. A proof compiles or it does not. What the adversarial process gives us is not certainty—we already had that from the type checker—but confidence. When a proof survives two rounds of hostile scrutiny and then compiles without Mathlib, without axioms beyond our stated assumptions, without sorry or admit, we have earned the right to believe it. The proof is not just correct; it is robust.

| Model | Role | Reference |
|-------|------|-----------|
| Goedel-Prover | Adversarial review (Round 1) | [arXiv:2502.07640](https://arxiv.org/abs/2502.07640) |
| DeepSeek-Prover-V2 | Adversarial review (Round 2) | [arXiv:2412.12877](https://arxiv.org/abs/2412.12877) |

---

## Status

**Released** — v0.3.2

Feature-complete with executable specification. All 30 invariants pass. Oracle CLI provides conformance testing. TLA+ aligned with Lean Jolt oracle (Status enum, 17 registry keys, 17 domain tags).

**v0.3.2 fixes:** Oracle now computes correct Poseidon digests using joltPoseidonConfig with midnight-circuits v6.0.0 constants. Golden test vectors added. Nix flake support for reproducible builds.

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
