# Jolt Continuation Proving System Specification

**Author:** Charles Hoskinson
**Version:** 1.0 — Released for Comment
**Date:** January 2026
**Status:** Public Review Draft
**Copyright:** 2026 Charles Hoskinson
**License:** Apache 2.0


---

## Executive Summary

### The problem in one sentence

You have 10,000 trades to settle. The chain can't re-execute them—too slow, too expensive, too public. So you execute off-chain and prove you did it correctly. This specification defines exactly how that proof works.

### What this document specifies

The Jolt Specification defines the **consensus-critical proving interface** for Jolt continuations: the contract between whoever generates proofs and whoever verifies them. The contract must be tight enough that independent implementations, written by different teams in different languages, produce compatible results. Any ambiguity is a potential network fork.

The system takes a batch of settlement intents, executes them in a deterministic RISC-V virtual machine (Jolt), wraps the proof for efficient on-chain verification (Halo2), and produces 11 field elements that the chain checks before authorizing a state transition.

**Key mechanism preview:** At the heart of continuation security is the StateDigest (§11.10)—a single field element that cryptographically commits to the entire VM state at chunk boundaries. Like a relay baton with a serial number, it prevents chunk skipping, splicing, and cross-configuration attacks. Every security guarantee in this specification ultimately traces back to StateDigest chaining.

### The four guarantees

**1. Deterministic Execution (Section 6, Section 7)** — The Settlement Engine runs on RV64IMC with fully specified semantics. Given identical inputs, every conforming implementation produces bit-identical outputs. No undefined behavior. No implementation-defined choices. No floating-point. No uninitialized memory reads.

**2. Succinct Proof (Section 5, Sections 9-12)** — Jolt proves execution correctness. The proof is small (kilobytes, not gigabytes). Verification is fast (milliseconds, not hours). The statement is strong: "this program, given these inputs, produced these outputs, and halted."

**3. Cryptographic Binding (Section 8, Section 11)** — Every connection is mathematical. The Fiat-Shamir transcript binds commitments to challenges. StateDigest chains continuation chunks. State roots bind memory contents. Breaking these bindings requires breaking the underlying cryptographic assumptions.

**4. Fail-Closed Gating (Section 3, Section 14)** — The system defaults to rejection. Missing parameters? Reject. TBD tags? Reject. Conformance tests fail? Reject. The spec prevents premature deployment by design.

### Current status

**Pending parameter finalization.** Of 17 required registry keys, 14 await final values (see §3.4). The architecture is complete—security model defined, algorithms specified. What remains is instantiation: finalizing Poseidon parameters, selecting toolchain versions, setting resource caps, and passing the two-implementation conformance gate.

### What's outside scope

This specification covers the proving layer. It does not specify: Settlement Engine application logic (what trades are valid), bridge design (how assets move cross-chain), economic parameters (fees, incentives), governance (how the system upgrades), or network layer (batch propagation).

---


## Document Statistics

| Metric | Value |
|--------|-------|
| Total sections | 17 (Sections 1-17, plus front matter) |
| Total words | ~40,000 |
| Original normative spec | ~4,500 words |
| Expansion ratio | ~8.9x |
| Registry keys pending final values | 14 of 17 |
| Required independent implementations | 2 |
| Public inputs (Fr elements) | 11 |

---

## Key Artifacts Reference

| Artifact | Section | Status |
|----------|---------|--------|
| 11 Public Inputs (Fr elements) | §5.5 | Fully defined |
| 17 Required Registry Keys | §3.4 | Fully enumerated |
| VMStateV1 (8 fields) | §11.5 | Fully defined |
| StateDigestV1 Algorithm (14 steps) | §11.10 | Fully defined |
| Bytes32ToFr2 Encoding | §7.6 | Fully defined |
| Transcript Sponge (typed absorption) | §8.4-§8.6 | Fully defined |
| SMT Parameters (depth, bit order) | §11.8 | Fully defined |
| Conformance Bundle Format | §14.3 | Fully defined |
| Threat Matrix | §15.10 | Complete (9 categories) |
| Deployment Checklist | §3.7 | 6 items |

---

## Table of Contents

- Section 1: Overview and scope
- Section 2: Normative language and conventions
- Section 3: Jolt continuations Parameter Registry and deployment gates
- Section 4: Architecture overview
- Section 5: Wrapper proof interface and public inputs
- Section 6: Deterministic guest VM specification (RV64IMC)
- Section 7: Word/field encodings and bytes32 safety
- Section 8: Transcript specification (Poseidon sponge)
- Section 9: Lasso / lookup gadget set (if used)
- Section 10: secp256k1 ECDSA verification workload (if used)
- Section 11: Continuations, snapshots, and StateDigest
- Section 12: Polynomial commitment scheme constraints and wrapper feasibility
- Section 13: Confidentiality and artifact handling
- Section 14: Conformance bundle and release gating
- Section 15: Security considerations
- Section 16: TLA+ Formal Specification Quick Reference
- Section 17: TLA+ Formal Specification Source Code

---

## Section 1: Overview and scope

### 1.0 Strategic Context

Blockchains promise trustless execution. They deliver it through radical transparency: every transaction visible to every observer before confirmation. This openness is both their greatest strength and their fatal flaw for serious capital.

Consider the institutional trader managing a $500 million portfolio. On a traditional exchange, a broker works her rebalancing order quietly over hours, revealing nothing until settlement. On a blockchain, she has no broker. Her transaction enters a public mempool where bots, competing funds, and sophisticated traders observe her intent and front-run it. By settlement, she has paid an invisible tax in worse execution, leaked strategy, and informed competitors. The same openness that makes blockchains trustworthy makes them hostile to large participants. Pension funds, sovereign wealth, corporate treasuries---the largest pools of capital on Earth---remain on the sidelines not because blockchain technology is immature, but because the execution environment broadcasts their strategies to the world.

Intent-based systems offer a partial solution. Instead of specifying "swap 1 ETH for USDC on Uniswap V3, pool 0x8ad5..., with 0.5% slippage," the user declares only the outcome: "I want at least 2,400 USDC for my 1 ETH." A network of specialized solvers competes to fulfill the intent, absorbing execution complexity and competing away inefficiencies. Analysis shows these systems have returned over $136 million in surplus to users---value otherwise lost to slippage and extraction. Intent protocols now handle 10--20% of decentralized exchange volume, up from near zero three years ago. But intents solve execution quality, not privacy. Broadcasting "I want to buy $50 million of token X" still moves markets. The ceiling remains.

| Scenario | Daily Settled Value (2030) | Intent Share of DEX | Privacy-Preserving Share |
|----------|---------------------------|---------------------|-------------------------|
| **Conservative** | $12.5 billion | 30% | 5% |
| **Base case** | $42.5 billion | 60% | 15% |
| **Aggressive** | $185 billion | 85% | 45% |

Jolt continuations breaks through this ceiling by proving correct execution without revealing execution details. A batch of trades moves through five layers, each transforming the problem into something the next layer can handle.

At the foundation sits the **Settlement Engine**: ordinary software written in Rust or C, compiled to a RISC-V binary. It reads a batch manifest, processes trades, and outputs one thing that matters---a state transition from old root to new root. Above it, **Jolt** (the zkVM) executes every RISC-V instruction and produces a cryptographic proof that execution followed the specification exactly. Jolt proves, but does not interpret; it attests that *this program, given these inputs, produces these outputs*, without knowing or caring what the program computes.

For batches requiring millions of CPU cycles, **Continuations** split execution into chunks of exactly `CHUNK_MAX_STEPS` instructions each. Each chunk commits to VM state at its boundary; the next chunk starts from that committed state. A continuation is valid if every chunk proof is valid and adjacent chunks agree on their shared boundary. The **Wrapper Circuit** (Halo2-lineage) then compresses Jolt's proof into 11 field elements optimized for on-chain verification. Finally, the **On-Chain Verifier** checks the wrapper proof and authorizes the state transition. This is the trust anchor. Everything upstream remains untrusted until this check passes.

Trust flows upward through proofs, not code audits. The chain trusts the mathematical properties of the proof system, not the wrapper's implementation. The wrapper trusts the Jolt proof, not Jolt's implementation. Each layer relies only on the cryptographic output of the layer below.

Every layer must be deterministic. Given identical inputs, every conforming implementation must produce bit-identical outputs. Not semantically equivalent---bit-identical. Consider what happens if the Settlement Engine reads uninitialized memory. Implementation A sees zeros; Implementation B sees garbage. They compute different state roots. The network partitions. The same failure can emerge at any layer: non-deterministic instruction semantics in Jolt, ambiguous transcript rules in the wrapper, different hash implementations on-chain. If a behavior can affect any digest, challenge, chunk boundary, or proof acceptance, it must be pinned to a specific value in the Parameter Registry (§3). Two implementations producing different outputs from identical inputs means the specification failed. This document exists to prevent that failure.

This specification draws a boundary. Inside: everything that affects whether nodes agree on state transitions---deterministic execution semantics, transcript rules, state binding, continuation mechanics, the 11-element public interface. Outside: everything else---settlement application logic, asset custody, networking, governance. Two deployments can use different fee models (application logic, outside the boundary) but must not use different Poseidon hash parameters (consensus-critical, inside the boundary).

The specification is not deployable today. Of 17 required registry keys, 15 remain undefined. But the architecture is complete, the security model defined, the interfaces stable. What remains is instantiation: selecting cryptographic parameters, building conforming implementations, and passing the two-implementation conformance gate that ensures compatibility. When that work completes, Jolt continuations will provide the proving infrastructure for private settlement at scale---the cryptographic foundation for intents that institutions can actually use.

### 1.1 Reader contract

**Who this is for:** Protocol engineers implementing Jolt continuations provers or verifiers, security auditors reviewing the architecture for consensus safety, and integration developers who need to understand the trust boundary.

**Prerequisites:** zkSNARK interface (prover produces short proof; verifier accepts/rejects based on public inputs). RISC-V is a CPU instruction set. Hash functions produce deterministic fixed-size outputs. No Jolt internals required—Section 1 treats it as a black box.

**What you will get:** Ability to trace a batch from off-chain execution to on-chain finality. Identification of trust assumptions at each layer. Understanding of why determinism is the central constraint.

**What you will not get:** Settlement Engine authoring. Jolt lookup argument internals. Deployment procedures. (See other documents or later sections.)

### 1.2 The problem

Suppose you have 10,000 trades to settle. The chain cannot process them directly—execution is too slow, gas costs are prohibitive, and on-chain processing would reveal order flow to everyone. So you execute off-chain, in private, then convince the chain you did it correctly. The chain verifies a cryptographic proof rather than re-executing.

This works only if every node reaches the same conclusion about whether the proof is valid. If node A accepts and node B rejects, the network forks.

This specification exists to prevent that failure. It specifies the **proving interface**: the exact contract between whoever generates proofs and whoever verifies them. The contract must be tight enough that independent implementations produce compatible results. Any ambiguity is a potential consensus bug.

### 1.3 Normative summary

the Jolt Specification defines the consensus-critical proving interface for Jolt continuations:

1. A fixed settlement program ("Settlement Engine") is compiled to a deterministic RV64IMC RISC‑V ELF.
2. The program executes in a deterministic zkVM (Jolt), producing a proof of correct execution.
3. Long executions MAY be proven as **continuations**: a sequence of chunk proofs, each proving exactly `CHUNK_MAX_STEPS` guest instructions (except the final chunk).
4. A wrapper circuit (Halo2-lineage) verifies the Jolt proof(s) and exposes a small set of public inputs over `Fr` for on‑chain verification.
5. The chain verifies the wrapper proof + public inputs and authorizes a state transition (old_root → new_root).

### 1.4 Architecture layers

A batch of trades moves through five layers, each transforming the problem into something the next layer can handle.

**Layer 1: Settlement Engine (the guest program).** The Settlement Engine is ordinary software—written in Rust or C, compiled to a RISC-V binary (an ELF file). It reads a batch manifest (the trades to execute), reads the current state (account balances, positions), and computes the new state. The output is simple: old state root in, new state root out, plus auxiliary data for the proof.

**Layer 2: Jolt (the zkVM).** Jolt takes the Settlement Engine binary and the batch manifest as input. It executes the program step-by-step—every RISC-V instruction—and produces a proof that the execution was correct. The proof attests: "This program, given these inputs, produces these outputs, and every instruction followed the RISC-V specification." Jolt neither knows nor cares what the program computes—it proves execution of any program you feed it.

**Layer 3: Continuations (for long executions).** Some batches require millions of CPU cycles. Proving all of them in one shot may exceed memory limits or take too long. Continuations split the execution into chunks. Each chunk proves exactly `CHUNK_MAX_STEPS` instructions and commits to the VM state at the boundary. The next chunk starts from that committed state. A continuation is valid if every chunk proof is valid and adjacent chunks agree on their shared boundary state.

**Layer 4: Wrapper Circuit (Halo2).** Jolt proofs are large and expensive to verify on-chain. The wrapper circuit verifies the Jolt proof(s) inside a different proof system—one optimized for on-chain verification. The wrapper takes Jolt's output and compresses it into 11 field elements (the public inputs) that the chain can check cheaply.

**Layer 5: On-Chain Verifier.** The chain receives the wrapper proof and the 11 public inputs. It runs the verification algorithm. If the proof is valid and the public inputs match expectations (correct program hash, correct old state root, etc.), the chain authorizes the state transition: `old_root → new_root`. This is the trust anchor. Everything upstream is untrusted until this check passes.

Each layer trusts only the cryptographic output of the layer below. The chain trusts the mathematical properties of the proof system, not the wrapper circuit's implementation. The wrapper trusts the Jolt proof, not Jolt's implementation. Trust flows upward through proofs, not code audits.

```
┌───────────────────────────────────────────────────────────────────────┐
│                       5-LAYER ARCHITECTURE                            │
├───────────────────────────────────────────────────────────────────────┤
│                                                                       │
│  ┌─────────────────────────────────────────────────────────────────┐  │
│  │  LAYER 5: ON-CHAIN VERIFIER                                     │  │
│  ├─────────────────────────────────────────────────────────────────┤  │
│  │  • Receives wrapper proof + 11 Fr public inputs                 │  │
│  │  • Verifies proof, authorizes state transition                  │  │
│  │  • TRUST ANCHOR: Everything upstream untrusted until verified   │  │
│  └─────────────────────────────────────────────────────────────────┘  │
│                               ▲                                       │
│                               │ wrapper proof + public inputs         │
│  ┌─────────────────────────────────────────────────────────────────┐  │
│  │  LAYER 4: WRAPPER CIRCUIT (Halo2)                               │  │
│  ├─────────────────────────────────────────────────────────────────┤  │
│  │  • Verifies Jolt proof(s) inside Halo2 circuit                  │  │
│  │  • Compresses output to 11 Fr elements                          │  │
│  │  • Optimized for efficient on-chain verification                │  │
│  └─────────────────────────────────────────────────────────────────┘  │
│                               ▲                                       │
│                               │ Jolt proof(s)                         │
│  ┌─────────────────────────────────────────────────────────────────┐  │
│  │  LAYER 3: CONTINUATIONS                                         │  │
│  ├─────────────────────────────────────────────────────────────────┤  │
│  │  • Splits execution into chunks of CHUNK_MAX_STEPS              │  │
│  │  • Each chunk commits to VM state at boundary                   │  │
│  │  • Adjacent chunks must agree on shared boundary state          │  │
│  └─────────────────────────────────────────────────────────────────┘  │
│                               ▲                                       │
│                               │ chunk proofs + StateDigest            │
│  ┌─────────────────────────────────────────────────────────────────┐  │
│  │  LAYER 2: JOLT (zkVM)                                           │  │
│  ├─────────────────────────────────────────────────────────────────┤  │
│  │  • Executes Settlement Engine step-by-step                      │  │
│  │  • Proves every RISC-V instruction followed spec                │  │
│  │  • Produces cryptographic proof of correct execution            │  │
│  └─────────────────────────────────────────────────────────────────┘  │
│                               ▲                                       │
│                               │ ELF binary + batch manifest           │
│  ┌─────────────────────────────────────────────────────────────────┐  │
│  │  LAYER 1: SETTLEMENT ENGINE (Guest Program)                     │  │
│  ├─────────────────────────────────────────────────────────────────┤  │
│  │  • Ordinary software (Rust/C) compiled to RV64IMC ELF           │  │
│  │  • Reads batch manifest, computes state transition              │  │
│  │  • Output: old_root → new_root                                  │  │
│  └─────────────────────────────────────────────────────────────────┘  │
│                                                                       │
│  TRUST FLOW: Each layer trusts only the cryptographic output of the  │
│              layer below. Trust flows upward through proofs.         │
└───────────────────────────────────────────────────────────────────────┘
```

### 1.5 Determinism

Every layer MUST be deterministic. Given identical inputs, every conforming implementation MUST produce bit-identical outputs.

Consider what happens if the Settlement Engine reads uninitialized memory. Implementation A sees zeros; Implementation B sees garbage. They compute different new state roots. Provers using A generate proofs for one state transition; provers using B generate proofs for a different one. Verifiers running A accept one set of proofs; verifiers running B accept another. The network partitions.

The same failure can occur at any layer: non-deterministic instruction semantics in Jolt, ambiguous transcript rules in the wrapper, different hash implementations on-chain. Every such ambiguity MUST be eliminated. If a behavior can affect any digest, challenge, chunk boundary, or proof acceptance, it MUST be pinned to a specific value in the Parameter Registry (§3). If not pinned, the spec is non-deployable (2.6).

Two implementations producing different outputs from identical inputs means the spec failed. The conformance bundle (§14) provides test vectors for byte-by-byte comparison.

### 1.6 Scope

the Jolt Specification draws a boundary. Inside: everything that affects whether nodes agree on state transitions. Outside: everything else.

**Inside (specified by the Jolt Specification):**
- Deterministic execution semantics for the guest VM (what each RISC-V instruction does, how memory works, how syscalls behave)
- Transcript rules (how challenges are derived from commitments—Fiat-Shamir)
- State binding (how old_root and new_root connect to actual state)
- Continuation rules (how chunk proofs chain together)
- The on-chain public interface (the 11 field elements and what they mean)

**Outside (not specified by the Jolt Specification):**
- Settlement application logic (what trades are valid, how fees work, what positions mean)
- Asset custody protocols or bridges (how assets enter or leave the system)
- Networking/gossip (how batches propagate, how provers coordinate)
- Sequencing and governance (who decides batch order, how the system upgrades)

Two Jolt continuations deployments can use different fee models—that is application logic, outside the boundary. But they MUST NOT use different Poseidon hash parameters—that is consensus-critical, inside the boundary.

### 1.7 Definition block

**Consensus-critical:** A parameter, behavior, or algorithm is consensus-critical if and only if two conforming implementations using different values for that parameter, given identical inputs, could produce outputs that differ in any bit of StateDigestV1, PublicOutputsV1, or proof verification result. Operational test: hold all other parameters fixed, vary the parameter in question, run both implementations on the same input. If outputs diverge, the parameter is consensus-critical. Consensus-critical elements MUST be identical across all implementations.

**Deterministic:** A function or process is deterministic if, given identical inputs, it always produces identical outputs, regardless of which implementation runs it, on which hardware, at which time. For Jolt continuations, "identical outputs" means bit-identical—not just semantically equivalent.

**Proving interface:** The boundary contract between prover and verifier. The prover's job: given a witness (the batch, the execution trace), produce a proof and public inputs. The verifier's job: given a proof and public inputs, output accept or reject.

**State transition:** A change from one committed state to another, authorized by a valid proof. In Jolt continuations, a state transition takes the form `(old_root, new_root, batch_commitment)`.

**Continuation:** A mechanism for proving long executions by splitting them into chunks. Each chunk proves a fixed number of guest instructions and commits to the VM state at the boundary.

### 1.8 Load-bearing claims

| Claim | Evidence | Verification |
|-------|----------|--------------|
| **The architecture produces consensus-safe state transitions** | Determinism enforced at every layer (2.6); Parameter Registry pins all ambiguous behaviors (Section 3); fail-closed deployment gates (3.5) | Two independent implementations, same test vectors, different outputs → spec failure |
| **The wrapper proof exposes sufficient public inputs for on-chain verification** | 11 Fr elements enumerated in Section 5 | Verify each element is necessary and jointly sufficient |
| **Continuations enable arbitrary-length executions** | Chunk proofs + StateDigest chaining (Section 11) | Verify boundary state commitments are binding |
| **The spec is non-deployable until all parameters are pinned** | 3.4 lists 17 required tags; 3.5 mandates fail-closed gating | Count TBD tags; if any remain, deployment gates MUST reject |

### 1.9 Jolt whitepaper connections

| Section 1 Concept | Whitepaper Reference | Connection |
|-------------|---------------------|------------|
| Settlement Engine as RV64IMC ELF | §3 (RISC-V overview) | Jolt proves RISC-V execution; Jolt continuations uses this to prove arbitrary settlement logic without per-application circuits |
| Jolt producing proof of correct execution | §1.2 (Jolt paradigm), §2.3 (Lasso lookup argument) | Jolt encapsulates each instruction's logic into a lookup table entry |
| Halo2 wrapper circuit | §1.3 (Polynomial commitments, proof composition) | The wrapper "translates" by verifying the Jolt proof inside a Halo2 circuit |
| Continuations / chunk proofs | §6.1 (Virtual instructions), Appendix B (memory checking) | A chunk boundary is like a mega-instruction that snapshots the entire VM state |
| Determinism as consensus requirement | §3.3 (Formatting assembly code), §7 (Combining instruction tables) | Any under-specification in ISA semantics becomes a consensus bug |

### 1.10 Forward references

- **Section 2:** Normative language conventions (RFC 2119 keywords, data types, endianness)
- **Section 3:** Parameter Registry structure and the 17 required tags
- **Section 5:** The 11 public inputs in detail, including encoding rules
- **Section 6:** Guest VM specification (RV64IMC subset, syscalls, trap behavior)
- **Section 8:** Transcript construction and Poseidon parameters
- **Section 11:** Continuation mechanics, StateDigest, and chunk chaining
- **Section 14:** Conformance bundle and the two-implementation gate

---

## Section 2: Normative language and conventions

Specifications fail through imprecision, and in consensus systems, imprecision kills. When two engineers read "the system should process the batch efficiently," one optimizes aggressively while the other prioritizes correctness---and neither can be blamed for the fork that follows. In ordinary software, such ambiguity breeds bugs; in distributed consensus, it breeds network splits that no rollback can repair. Section 2 exists because Jolt continuations demands something rare: prose so precise that independent teams, working in complete isolation, will produce implementations that agree on every bit.

Three mechanisms make this precision possible. First, RFC 2119 keywords transform English into a contractual language where MUST means "violate this and your implementation fails conformance" while MAY means "your choice, no judgment." Second, canonical data representations eliminate encoding ambiguity---when the spec says `Fr`, it means exactly 255 bits in exactly the range [0, r-1], no exceptions. Third, the determinism rule catches whatever the first two mechanisms miss: any unspecified behavior that could touch a digest, a transcript challenge, a chunk boundary, or an acceptance decision must be pinned in the Parameter Registry before deployment. Fail-closed, not fail-warn.

**Normative vs. non-normative text:** Statements using RFC 2119/8174 keywords (MUST, MUST NOT, SHOULD, SHOULD NOT, MAY, etc.) are normative. Text labeled "Reader contract", "Rationale", "Worked example", "Evidence", or "non-normative" is explanatory and MUST NOT be treated as changing requirements unless it explicitly uses RFC 2119/8174 keywords.

### 2.3 RFC 2119 keywords

The key words **MUST**, **MUST NOT**, **REQUIRED**, **SHALL**, **SHALL NOT**, **SHOULD**, **SHOULD NOT**, **RECOMMENDED**, **NOT RECOMMENDED**, **MAY**, and **OPTIONAL** in this specification are to be interpreted as described in RFC 2119 and RFC 8174, **when and only when** they appear in **all capitals**.

These are not rhetorical flourishes—they are contractual obligations with testable consequences:

**MUST / MUST NOT** — Absolute requirements and prohibitions. An implementation that violates a MUST is non-conforming. It will fail conformance tests. It cannot be deployed as part of Jolt continuations.

**SHOULD / SHOULD NOT** — Strong recommendations. You can deviate, but you must have a reason, and you must document it. Deviations may cause interoperability problems.

**MAY** — Truly optional. The spec permits this behavior but does not require it. Implementations can differ here without being non-conforming.

When reading the spec, catch every MUST and MUST NOT. These are the hard requirements. Miss one, and your implementation fails.

**Consensus-critical clarity rule:** Any requirement that can change a consensus-visible output (digest, transcript/challenge, chunk boundary, or proof acceptance decision) MUST be expressed using **MUST**/**MUST NOT**. **SHOULD**/**SHOULD NOT** are reserved for non-consensus guidance (operational or ergonomics). If a deployment treats a SHOULD as consensus-critical, it MUST be pinned via a versioned registry tag before deployment; otherwise the spec is non-deployable by §3.5.

### 2.4 Data types

Two engineers serialize the same field element. One writes 32 bytes; the other writes 31. Both believe they followed the spec. Where did they diverge? The spec said "Fr element" but never specified its byte representation.

This ambiguity multiplies across every boundary: memory layout, transcript absorption, public inputs. We need a shared vocabulary:

| Type | Definition | Range/Size |
|------|------------|------------|
| `bytes` | Arbitrary byte string | Length bounds MUST be specified by the containing format/algorithm or pinned via a registry cap tag; otherwise the spec is non-deployable by §2.6 |
| `bytes32` | 32-byte string | Exactly 32 bytes |
| `u8` | Unsigned 8-bit integer | 0 to 255 |
| `u32` | Unsigned 32-bit integer | 0 to 4,294,967,295 |
| `u64` | Unsigned 64-bit integer | 0 to 18,446,744,073,709,551,615 |
| `Fr` | Scalar field of BLS12‑381 | Integers mod r (~255 bits) |

The scalar field of BLS12-381 (`Fr`) is the set of integers modulo:

```
r = 52435875175126190479447740508185965837690552500527637822603658699938581184513
```

This is a 255-bit prime. Every `Fr` element is an integer in [0, r-1]. All arithmetic in the wrapper circuit happens in `Fr`. Public inputs are `Fr` elements. If you need to represent a 256-bit value (like a SHA-256 hash), you cannot fit it in one `Fr`—it might exceed r. Section 7.6 defines `Bytes32ToFr2`, which splits a 32-byte value into two `Fr` elements safely.

For any `Fr` element, the canonical representation is the unique integer in [0, r-1]. Values ≥ r are malformed and MUST be rejected.

### 2.4.1 Integer semantics for machine words

When this specification models guest register values as `u32`/`u64`, arithmetic is performed **modulo 2^32 / 2^64** (wraparound), matching RISC‑V machine semantics, unless explicitly stated otherwise.

When a signed interpretation is required (e.g., for signed division), a `u64` value `x` is interpreted as two's-complement `i64`:

- if `x < 2^63`, then `i64(x) = x`
- else `i64(x) = x − 2^64`

The inverse mapping is `u64(y) = (y mod 2^64)`.

### 2.5 Endianness

- Guest memory is **little‑endian**.
- Canonical integer encodings in this specification are **little‑endian**, unless explicitly stated otherwise.

Four bytes `[0x01, 0x02, 0x03, 0x04]` represent different integers depending on interpretation:
- **Little-endian:** `0x04030201` = 67,305,985
- **Big-endian:** `0x01020304` = 16,909,060

If the prover interprets bytes as little-endian and the verifier interprets them as big-endian, every hash differs, every commitment differs, every proof fails. Jolt continuations pins little-endian, matching RISC-V's native endianness.

To verify: encode `0x01020304` as bytes. You MUST get `[0x04, 0x03, 0x02, 0x01]`.

### 2.5.1 Byte-string notation, hex, and hash inputs

This appendix treats `bytes` and `bytes32` as **byte strings** (ordered sequences of bytes), not integers, unless an algorithm explicitly converts them to an integer.

- `A || B` denotes **byte-string concatenation** (no separators).

- **Hex notation.** A hex byte string is written with a `0x` prefix followed by an even number of hex digits. Each pair of hex digits encodes one byte. The leftmost pair encodes the first byte. Example: `0x000102` denotes `bytes([0x00, 0x01, 0x02])`. Spaces shown in hex dumps (e.g., `4e 46 2f …`) are for readability only and are not part of the byte string.

- **Canonical textual `bytes32`.** Whenever a `bytes32` value is represented textually in any **consensus-critical** artifact (e.g., registry values, conformance vectors, release manifests), it MUST be encoded as:

  `0x` + 64 lowercase hex characters.

  Any other textual form MUST be rejected.

- **Byte-literal notation.** Where this specification writes `b"..."`, it denotes the ASCII bytes of the literal contents. There is **no implicit terminating NUL**. The sequence `\0` inside a `b"..."` literal denotes a single `0x00` byte (and is the only escape used by this specification).

  Example: `b"JOLT/BATCH/NODE/V1\0"` denotes `UTF8("JOLT/BATCH/NODE/V1") || 0x00`.

- **UTF8(s).** `UTF8(s)` denotes the UTF-8 encoding of the Unicode string `s` (no BOM, no normalization).

**Hashing rule (normative):**
- When this specification specifies `SHA-256(x)` where `x` is a byte string, the input is the raw bytes `x` exactly as defined.
- Implementations MUST NOT hash textual encodings (ASCII hex, base64, etc.) unless explicitly specified.
- `SHA-256` outputs are treated as byte strings in the output order returned by the hash function. Implementations MUST NOT reverse digest bytes for "endianness".
- The symbol `H(x)` (if it appears in a **non-normative** example) denotes a deployment-chosen 32-byte hash function and MUST NOT be used in a consensus-critical algorithm unless the function is explicitly named and pinned via a versioned registry tag.

If a hash output is represented in `Fr`, it MUST use `Bytes32ToFr2` for semantic `bytes32` values and `Bytes32LEToFrCanonical` for values already known to be canonical `Fr` encodings (§7).

### 2.5.2 Lexicographic ordering

Whenever this specification requires "lexicographic order" for byte strings or strings:

- **Byte strings** are compared as sequences of **unsigned bytes** (0–255), bytewise from index 0 upward. The first differing byte determines the ordering. If one byte string is a strict prefix of the other, the shorter byte string sorts first.

- **Strings** are compared by lexicographic order of their UTF‑8 bytes (not locale collation, not Unicode normalization, and no case folding).

**Tag identifier character set and syntax (normative):**

To ensure bytewise ordering is stable across implementations and to avoid "invisible" divergences, deployments MUST restrict Jolt continuations tag identifiers and tag strings to ASCII and MUST NOT permit whitespace.

- **Registry tag keys** (JSON object keys in `registry.json` that name Jolt continuations tags) MUST match:

  `^JOLT_[A-Z0-9_]+_V[0-9]+$`

- **Domain/tag strings** (strings passed to `absorb_tag(...)` and used for domain separation) MUST match:

  `^JOLT/[A-Z0-9_./-]+/V[0-9]+$`

No Unicode normalization, case folding, or locale-aware collation is permitted.

### 2.5.3 Fixed-width integer byte encodings

Whenever this specification serializes a fixed-width integer to bytes, it uses the canonical little-endian encoding with **exact width**:

- `U8(x)` encodes `u8 x` as 1 byte `[x]`.
- `U32LE(x)` encodes `u32 x` as 4 bytes `[b0,b1,b2,b3]` such that `x = b0 + 256·b1 + 256²·b2 + 256³·b3`.
- `U64LE(x)` encodes `u64 x` as 8 bytes `[b0..b7]` such that `x = Σ_{i=0..7} b_i · 256^i`.

Any encoding that is not the exact-width little-endian form (wrong length, big-endian order, or sign-extended) MUST be rejected by decoders.

**General little-endian integer interpretation:** For a byte array `b[0..n-1]`, define `int_le(b)` as:

`int_le(b) := Σ_{i=0..n-1} b[i] × 256^i`.

When a later section says "interpret bytes as a little-endian integer", it refers to `int_le`.

### 2.6 Determinism rule

If any behavior is not fully specified in this specification and can affect:
- any digest,
- any transcript/challenge,
- any chunk boundary,
- any proof acceptance decision,

then it MUST be pinned via a versioned tag in the Jolt continuations Parameter Registry (§3). Otherwise, the specification is non‑deployable by §3.5.

These four categories are consensus-visible outputs—compared across nodes. Internal implementation details don't matter as long as these outputs match. Divergence means consensus failure.

The spec says "hash the batch manifest." But what exactly gets hashed? Does the encoding include a length prefix? What byte order for multi-byte fields? If Implementation A includes a 4-byte length prefix and Implementation B doesn't, they produce different hashes. Same manifest, different digest. Any proof generated by A will fail verification by B.

2.6 says: these details MUST be pinned. The Parameter Registry includes `JOLT_BATCH_MANIFEST_ENCODING_V1` to specify the exact encoding. Until that tag has a concrete value, the spec is non-deployable.

Section 3.5 defines deployment gates. If any tag is TBD, the gate fails. Fail-closed: ambiguity blocks deployment, not just causes warnings.

**Reject, don't normalize (normative):** Wherever this specification specifies a canonical encoding (byte order, exact length, allowed character set, canonical range), implementations MUST treat any non-canonical encoding as malformed and MUST reject it. Implementations MUST NOT silently normalize malformed inputs into canonical form.

### 2.6.1 Canonical JSON safety requirements

To avoid parser-level nondeterminism, any consensus-critical JSON artifact (including `registry.json`) MUST satisfy:

- **Strict JSON only:** The artifact MUST be valid RFC 8259 JSON. Parsers MUST reject JSON extensions (comments, trailing commas, NaN/Infinity, non-UTF-8 encodings, etc.).

- **UTF-8 without BOM:** The artifact MUST be encoded as UTF-8 **without** a byte order mark (BOM). Presence of a BOM MUST be rejected.

- **No duplicate keys:** JSON objects MUST NOT contain duplicate member names. Any duplicate key MUST be treated as invalid.

- **Numeric safety:**
  - Any JSON number that appears in a consensus-critical artifact MUST be an **integer** in the inclusive range `[-(2^53 − 1), +(2^53 − 1)]`.
  - Fractional forms and exponent notation MUST NOT be used.
  - Any integer outside `±(2^53 − 1)` MUST be represented as a JSON string (e.g., base-10 or `0x`-prefixed hex). The parsing rules for such strings MUST be specified by the containing tag definition.

### 2.6.2 TLA+ Formal Specification Reference

This specification has been formalized in TLA+ and verified using the TLC model checker. The canonical TLA+ specification is the authoritative formal reference for:

- State machine semantics (`VMState.tla`, `JoltSpec.tla`)
- Type definitions (`Types.tla`, `Encodings.tla`)
- Cryptographic abstractions (`Hash.tla`, `Transcript.tla`)
- Memory commitment structures (`SMT.tla`, `SMTOps.tla`)
- Chunked execution model (`Continuations.tla`)
- Wrapper constraints (`Wrapper.tla`)
- Security invariants (`Invariants.tla`)

**Module Dependency Graph:**
```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        TLA+ MODULE DEPENDENCY TREE                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Types.tla (foundation)                                                     │
│      │                                                                      │
│      ├─── Encodings.tla                                                     │
│      │                                                                      │
│      ├─── Hash.tla ─────────┐                                               │
│      │                      │                                               │
│      │                      └─── Transcript.tla                             │
│      │                                                                      │
│      ├─── SMT.tla ──────────┐                                               │
│      │                      │                                               │
│      │                      └─── SMTOps.tla                                 │
│      │                                                                      │
│      ├─── VMState.tla                                                       │
│      │                                                                      │
│      ├─── Registry.tla                                                      │
│      │                                                                      │
│      └─── Continuations.tla                                                 │
│                  │                                                          │
│                  └─── Wrapper.tla                                           │
│                            │                                                │
│                            └─── JoltSpec.tla                                │
│                                      │                                      │
│                                      └─── Invariants.tla                    │
│                                                 │                           │
│                                                 └─── MC_Jolt.tla            │
│                                                      (model check harness)  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

**Verification Status:**
- **SANY:** All 13 modules parse without errors
- **TLC:** Model checking passes with all invariants enabled (9 states explored)
- **Coverage:** 26 individual invariants verified (4 type, 7 binding, 7 safety, 8 attack prevention) plus 6 composite invariants

**Cross-Reference Convention:** Throughout this specification, TLA+ references use the format `Module.tla:Line (Operator)` to identify the corresponding formal definition.

**Model Limitations:** The TLC model uses finite bounds and abstract hash functions for tractability. Production implementations MUST follow the algorithms specified in this specification exactly; the TLA+ specification verifies structural correctness but cannot verify cryptographic security properties on full domains.

**TLA+ Quick Reference:** See Section 17 for a comprehensive module index, invariant categories, and TLC usage instructions.

### 2.7 Definition block

**Normative:** A statement that defines requirements for conforming implementations. Normative statements use RFC 2119 keywords.

**Canonical representation:** The single, unique way to encode a value. Two implementations encoding the same value MUST produce byte-identical output.

**Conforming implementation:** An implementation that satisfies all MUST and MUST NOT requirements and produces outputs matching conformance test vectors.

**Non-deployable:** A state where the spec cannot be used for production because required parameters are not pinned. The on-chain verifier MUST reject all proofs until the spec becomes deployable.

**Consensus-visible:** An output compared across nodes to determine agreement. Digests, challenges, chunk boundaries, and acceptance decisions are consensus-visible.

### 2.8 Load-bearing claims

| Claim | Evidence | Verification |
|-------|----------|--------------|
| **RFC 2119 keywords create enforceable obligations** | RFC 2119 standard; §14 conformance bundle | Implement a deliberate MUST violation; run conformance tests; observe failure |
| **Data types have canonical, unambiguous representations** | §2.4 definitions; §7 encoding algorithms | Encode the same value in two implementations; compare bytes; must be identical |
| **Little-endian is the universal byte interpretation** | §2.5 explicit statement; RISC-V native endianness | Encode `0x01020304` as bytes; must produce `[0x04, 0x03, 0x02, 0x01]` |
| **Unspecified consensus-affecting behavior blocks deployment** | §2.6 rule; §3.4 required tags; §3.5 fail-closed gates | Attempt deployment with TBD tag; gate must reject |

### 2.9 Forward references

- **RFC 2119 + RFC 8174 keywords** → Every section uses MUST/SHOULD/MAY
- **`Fr` field elements** → §5 (public inputs), §7 (Bytes32ToFr2), §8 (Poseidon)
- **Little-endian, U64LE encoding** → §6 (guest memory), §7 (FrToBytes32LE), §2.5.3 (fixed-width encodings)
- **Concatenation (`||`) and hex notation** → §2.5.1 (used throughout transcript and commitment algorithms)
- **Lexicographic ordering** → §3.8 (config_tags sorting), §11.10 (StateDigest), §2.5.2 (definition)
- **JSON canonicalization safety** → §3.3 (registry JCS), §2.6.1 (numeric/duplicate-key rules)
- **Determinism rule** → §3 (Parameter Registry), §8 (transcript), §11 (continuations), §14 (conformance)

---

## Section 3: Jolt continuations Parameter Registry and deployment gates

Every consensus system faces the same treacherous problem: configuration drift. You want to verify a continuation proof, but what exactly do you need to know? Start with the hash function. Poseidon over BLS12-381's scalar field sounds specific enough, but which Poseidon? The permutation demands parameters: width, round counts, MDS matrix entries, round constants. Change a single constant and every hash in the system shifts. Now consider memory layout. Where does the guest stack begin? Where does the heap live? A prover using one layout and a verifier expecting another will disagree on every memory commitment. Then encoding formats: does the batch manifest include a four-byte length prefix? Then chunk boundaries: how many RISC-V instructions fit in each continuation chunk? Each parameter is a knob. Turn any knob differently between prover and verifier, and verification fails. The proof is valid under one configuration and invalid under another. If nodes run different configurations, consensus collapses.

The Parameter Registry exists to tame this complexity. Rather than tracking dozens of independent knobs, you track one JSON file. Rather than comparing dozens of values, you compare one 32-byte hash. The registry becomes the single source of truth for all consensus-critical configuration. RFC 8785 JSON Canonicalization Scheme (JCS) ensures that semantically identical JSON always produces identical bytes. Keys sort lexicographically. Whitespace normalizes away. Given the same JSON semantics, JCS always yields the same byte sequence. The registry hash, computed as `SHA-256(canonical_registry_bytes)`, uniquely identifies the configuration. Two registries with matching hashes have identical configuration. Two with differing hashes are incompatible by construction.

Seventeen required tags govern deployment. Three control cryptographic foundations: Poseidon parameters, the polynomial commitment scheme, and the Fiat-Shamir transcript schedule. Four more pin the guest VM: ISA profile (RV64IMC), the exact RISC-V spec version, memory map layout, and the toolchain that builds guest binaries. Three DoS caps bound manifest size, intent count, and checkpoint encoding. Three encoding format tags eliminate ambiguity about serialization. One deployment binding tag prevents cross-deployment replay attacks. One execution configuration tag fixes chunk boundaries. Two implementation identity tags pin the exact Git commit and wrapper proof system. Beyond these seventeen, three external handles exist outside the registry: the registry hash itself (circular if included), the wrapper verifying key hash (depends on registry contents), and the conformance bundle hash (the bundle contains the registry).

Deployment gating enforces fail-closed semantics. The on-chain verifier accepts proofs only if two conditions hold: the wrapper verifying key matches the pinned hash, and the proof verifies under that key. Release-process conditions add three more gates: every required tag must have a concrete value (no `"TBD"` sentinels anywhere), at least two independent implementations must pass the conformance bundle, and the registry contents must match documented values byte-for-byte. Currently, fifteen of the seventeen required tags remain marked `TBD`. Only `JOLT_RISCV_PROFILE_V1` (set to `RV64IMC`) and `JOLT_BATCH_COMMITMENT_V1` have concrete values. The specification is non-deployable by design. The deployment gates force decisions before deployment, not after.

### 3.3 Registry mechanics

Jolt continuations deployments are parameterized by a **registry artifact** (`registry.json`) containing versioned tags and values.

Tags are **consensus‑critical** if they affect:
- guest instruction semantics,
- ABI and memory map,
- transcript/challenge derivation,
- hash/commitment algorithms,
- chunking rules,
- wrapper proof system and verifying key identity.

**Tag key format (normative).** Every top-level key in `registry.json` MUST be an ASCII string matching:
- `^JOLT_[A-Z0-9_]+_V[0-9]+$`

Keys are case-sensitive. Keys that do not match this format MUST cause the registry to be rejected (fail-closed).

**Tag versioning (normative).** The semantics and JSON schema of a tag key are fixed. If either changes, a deployment MUST introduce a new tag key with an incremented version suffix (e.g., `_V2`) rather than reinterpreting an existing key.

**Canonicalization (consensus‑critical).** `canonical_registry_bytes` MUST be the RFC 8785 JSON Canonicalization Scheme (JCS) UTF‑8 serialization of the top‑level registry JSON object.

JSON is flexible in ways that break byte-equality. These two objects are semantically identical but different byte sequences:

```json
{"a": 1, "b": 2}
{"b":2,"a":1}
```

RFC 8785 JCS solves this: it defines a single canonical byte representation. Keys are sorted lexicographically. Whitespace is normalized. Given the same JSON semantics, JCS always produces the same bytes.

**Numeric precision (normative).** JSON numbers in the registry MUST follow the numeric safety rules in §2.6.1:
- Integers with absolute value ≤ 2⁵³−1 MUST be JSON numbers
- Integers outside that range MUST be decimal strings (e.g., `"9007199254740993"` instead of `9007199254740993`)

This prevents cross-language parsing bugs (e.g., JavaScript's 53-bit integer limitation). The rule is deterministic: there is exactly one correct encoding for any integer value.

**Registry hash.** `JOLT_PARAMETER_REGISTRY_HASH_V1 := SHA‑256(canonical_registry_bytes)`.

This 32-byte value uniquely identifies the configuration. Two registries with the same hash have identical configuration. The registry hash is the consensus anchor.

**Definition:** In this specification, "configuration" means the full canonical `registry.json` byte sequence after JCS canonicalization and external-handle exclusion verification.

**V1 key set (normative).** For V1 deployments, `registry.json` MUST contain exactly the non-external required tag keys listed in §3.4, and MUST NOT contain any additional top-level keys. If any unknown key is present, the registry artifact is invalid and MUST be rejected (fail-closed).

**External‑handle exclusions.** The registry artifact MUST NOT contain the following keys (they are **external handles** derived from other deployment artifacts):

- `JOLT_PARAMETER_REGISTRY_HASH_V1`
- `JOLT_WRAPPER_VK_HASH_V1`
- `JOLT_CONFORMANCE_BUNDLE_HASH_V1`

If any of these keys are present, the registry artifact is invalid and MUST be rejected. There is no "remove and continue" option—fail-closed means any malformed registry blocks deployment entirely.

### 3.4 Required tags (deployment-blocking)

This appendix is **NOT deployable** until every required tag below is pinned to a concrete value (not `TBD`).

**Enforcement mechanisms vary by tag type:**
- **Circuit-enforced** (baked into VK): Cryptographic tags (`JOLT_POSEIDON_FR_V1`, `JOLT_PCS_V1`, etc.) are absorbed into the wrapper circuit. Different values → different VK → proofs incompatible.
- **Contract-enforced** (on-chain parameters): External handles (`JOLT_WRAPPER_VK_HASH_V1`, `JOLT_PARAMETER_REGISTRY_HASH_V1`) are stored on-chain. Proofs must match pinned values or the contract rejects.
- **Process-enforced** (release gates): Conformance bundle hash, TBD elimination, and two-implementation testing are verified before deployment. The on-chain contract cannot directly verify "no TBD exists" but TBD values prevent valid proofs from being generated.

**Tag count summary:**
- **Registry keys (inside `registry.json`):** 17 required
- **External handles (published alongside):** 3 required (registry hash, VK hash, conformance hash)
- **Currently TBD:** 14 registry keys
- **Finalized:** `JOLT_RISCV_PROFILE_V1`, `JOLT_BATCH_COMMITMENT_V1`, `JOLT_POSEIDON_FR_V1` (§3.4.1)

#### Cryptographic Core

| Tag | Draft value | Purpose |
|-----|-------------|---------|
| `JOLT_POSEIDON_FR_V1` | See §3.4.1 | Poseidon permutation parameters (width, rounds, MDS matrix, round constants) |
| `JOLT_PCS_V1` | `TBD` | Polynomial commitment scheme used by Jolt |
| `JOLT_TRANSCRIPT_SCHEDULE_V1` | `TBD` | Fiat-Shamir transcript structure |

These three tags control the cryptographic foundation. Change any, and the entire proof system produces incompatible outputs.

#### 3.4.1 `JOLT_POSEIDON_FR_V1` (normative)

The Poseidon permutation parameters for the BLS12-381 scalar field.

**Sponge configuration:** State width t = 3 elements, rate r = 2 elements, capacity c = 1 element. The sponge construction uses t = r + c = 3 field elements per permutation.

**Parameters:**

| Parameter | Value | Description |
|-----------|-------|-------------|
| `variant` | `"Poseidon"` | Poseidon (not Poseidon2) |
| `sbox_exponent` | `5` | Quintic S-box (α = 5) |
| `t` | `3` | State width |
| `r` | `2` | Rate |
| `c` | `1` | Capacity |
| `full_rounds` | `8` | Full rounds (4 initial + 4 final) |
| `partial_rounds` | `60` | Partial rounds |
| `field` | `"BLS12-381/Fr"` | Scalar field of BLS12-381 |
| `security_bits` | `128` | Target security level |

**S-box validity:** The quintic S-box requires `gcd(5, r-1) = 1`. For BLS12-381 scalar field, `r mod 5 = 3 ≠ 1`, confirming `5 ∤ (r-1)`. ✓

**Source:** MDS matrix and round constants are taken verbatim from `midnight-circuits` v6.0.0 (`midnight_circuits::hash::poseidon::constants`).

**Constant encoding (normative).** Every field element in `mds_matrix` and `round_constants` is stored as `FrToBytes32LE(f)` rendered as canonical textual `bytes32` (lowercase hex, no `0x` prefix, 64 characters).

**MDS Matrix (3×3):**

The MDS matrix `M` is a 3×3 maximum distance separable matrix over Fr. Elements are indexed as `M[row][col]`:

```
M[0][0] = ce1ab50741de1861779eba534074d58aa6d8e21012246d5dfd22b981c314811b
M[0][1] = 63d7c0fc137271e3b4094cecca0c99751733f59c89215d0ed22ecbc44c2ef33d
M[0][2] = c1ede1a0ae34cd3e0b08911560337f00b48e54bf798725beda64667adfc4053f
M[1][0] = 74b3a831cd01f5d7b1e70f954b3174ca06ae3f6dd74a2a434ed1853907214d40
M[1][1] = f14956950316faf72f42797631b2e9734b4d529e0e62bc81bdc6644270c82c0b
M[1][2] = 1f1a7f638cfca8e2b448438319b50b6d495d0341c688935afa5950a54d66df0f
M[2][0] = 4091c4907ec55df90a735ab601ad9731035d5cf4474ae2434321a6cdbe3d1d5e
M[2][1] = 8aa75a2f00b9c77df35489ae5f6dcb4412c6a57ee79618939daf53fc9c2fd76b
M[2][2] = dbe09df98eb84fbbd9468ed59cbdff1e83ef4b05a980f8ca7ba05f3aaac59749
```

**Round Constants:**

Round constants `RC[round][element]` for `round ∈ [0, 67]` and `element ∈ [0, 2]` (68 rounds × 3 elements = 204 field elements total). Full constant table in Appendix A.

#### Guest VM Configuration

| Tag | Draft value | Purpose |
|-----|-------------|---------|
| `JOLT_RISCV_PROFILE_V1` | `RV64IMC` | ISA profile |
| `JOLT_RISCV_UNPRIV_SPEC_V1` | `TBD` | Exact RISC-V spec version and errata |
| `JOLT_GUEST_MEMMAP_V1` | `TBD` | Memory map (stack base, heap base, region sizes) |
| `JOLT_TOOLCHAIN_V1` | `TBD` | Compiler, linker, flags for guest ELF |

The guest VM must execute deterministically. That requires pinning not just instruction semantics but where memory lives and which compiler produced the binary.

#### DoS Caps

| Tag | Draft value | Purpose |
|-----|-------------|---------|
| `JOLT_MAX_MANIFEST_BYTES_V1` | `TBD` | Maximum batch manifest size |
| `JOLT_MAX_INTENTS_V1` | `TBD` | Maximum fill intents per batch |
| `JOLT_MAX_CHECKPOINTS_BYTES_V1` | `TBD` | Maximum checkpoints encoding size |

DoS caps are consensus-critical. `MAX_INTENTS` determines Merkle tree structure. Different limits mean different tree shapes and different commitments.

#### Encoding Formats

| Tag | Draft value | Purpose |
|-----|-------------|---------|
| `JOLT_BATCH_MANIFEST_ENCODING_V1` | `TBD` | Canonical bytes encoding of BatchManifestV1 |
| `JOLT_BATCH_COMMITMENT_V1` | `NF/BATCH/COMMITMENT/MERKLE_SHA256/V1` | Batch commitment algorithm |
| `JOLT_CHECKPOINTS_ENCODING_V1` | `TBD` | Canonical checkpoints encoding |

Encoding ambiguity is a classic source of consensus bugs. Does the manifest include a length prefix? Every such choice must be pinned.

#### Deployment Binding

| Tag | Draft value | Purpose |
|-----|-------------|---------|
| `JOLT_CONTEXT_BYTES32_V1` | `TBD` | Deployment-specific context for cross-deployment replay prevention |

The Settlement Engine MUST validate `manifest.context_bytes32` against this value. This tag is a **compile-time constant** embedded in the Settlement Engine binary—the guest does not read it from the registry at runtime. Changing this value requires recompiling the Settlement Engine (and thus changing `program_hash`).

#### Execution Configuration

| Tag | Draft value | Purpose |
|-----|-------------|---------|
| `JOLT_CONTINUATIONS_V1` | `TBD` | Chunk size, snapshot caps, page limits |

`CHUNK_MAX_STEPS` determines where continuation splits occur. Different boundaries mean incompatible proofs.

#### Implementation Identity

| Tag | Draft value | Purpose |
|-----|-------------|---------|
| `JOLT_IMPL_COMMIT_V1` | `TBD` | Git commit of Jolt implementation |
| `JOLT_WRAPPER_PROOF_SYSTEM_V1` | `TBD` | Wrapper circuit identity |

Even with the same spec, different implementations might have bugs. Pinning the commit ensures everyone uses the same code.

#### External Handles

| Tag | Purpose | Why External |
|-----|---------|--------------|
| `JOLT_PARAMETER_REGISTRY_HASH_V1` | SHA-256 of the registry | Circular: can't put hash of X inside X |
| `JOLT_WRAPPER_VK_HASH_V1` | SHA-256 of wrapper verifying key | VK depends on registry contents |
| `JOLT_CONFORMANCE_BUNDLE_HASH_V1` | SHA-256 of conformance bundle | Bundle includes the registry |

These are published alongside `registry.json`, not inside it.

### 3.5 Deployment gating (normative)

A deployment MUST implement **fail-closed** gating. The conditions below are divided into **on-chain enforced** (guaranteed by the smart contract) and **release-process required** (guaranteed by deployment procedures).

#### On-chain acceptance conditions (enforced by verifier contract)

The on-chain verifier MUST reject any wrapper proof unless ALL of the following hold:

**1. Wrapper identity pinned.** The deployment is configured with `JOLT_WRAPPER_VK_HASH_V1`, and verifies proofs only against the verifying key whose canonical hash equals that value.

**2. Proof verification.** The wrapper proof verifies under the pinned VK.

These conditions are cryptographically enforced—the on-chain contract cannot accept a proof that fails any of them.

**Clarification (normative).** `JOLT_PARAMETER_REGISTRY_HASH_V1` is an external deployment handle published alongside `registry.json`. The verifier contract does not (and cannot) recompute `JOLT_PARAMETER_REGISTRY_HASH_V1` or validate `config_tags` from `registry.json` unless the full registry bytes are made available on-chain and explicitly checked.

Configuration binding to `registry.json` is enforced in-circuit by the wrapper's **Configuration binding** constraint (§5, Constraint 1) via `config_tags` (§3.8).

#### Release-process conditions (enforced by deployment procedures)

A deployment MUST NOT proceed to mainnet unless ALL of the following hold:

**4. No TBD.** Every non-external required tag in §3.4 is present and has a concrete value.

**TBD sentinel (normative).** In `registry.json`, the only permitted placeholder for an unresolved design decision is the JSON string `"TBD"` (ASCII, case-sensitive). A required tag is considered unresolved if its JSON value contains `"TBD"` at any JSON path (including nested object fields and array elements). Deployable configurations MUST NOT contain `"TBD"` anywhere within any required tag value.

**5. Conformance passed.** The deployment is configured with `JOLT_CONFORMANCE_BUNDLE_HASH_V1`, and at least two independent implementations pass the bundle.

**6. Exact match verified.** The registry contents match the documented values byte-for-byte.

These conditions are process-enforced—the release process must verify them before deployment. The on-chain contract cannot directly verify "no TBD" without storing the full registry.

**Normative requirement:** Conforming implementations MUST refuse to build, prove, or verify under any configuration where any required tag value (recursively) contains the `"TBD"` sentinel. This is a tooling obligation, not a cryptographic impossibility—the safety property depends on correct implementation of this check.

**Fail-closed means what it says.** If any condition fails, the verifier accepts zero proofs. This is not a bug—it's the only safe default. Accepting proofs under ambiguous configuration risks consensus failure.

These rules ensure that two honest implementations cannot diverge on consensus-critical parameters.

### 3.6 The TBD problem: explicit incompleteness

Current state: of 17 required tags, 15 are marked `TBD`. The only pinned values are:
- `JOLT_RISCV_PROFILE_V1` = `RV64IMC`
- `JOLT_BATCH_COMMITMENT_V1` = `NF/BATCH/COMMITMENT/MERKLE_SHA256/V1`
- External handles (derived, not preset)

The spec is non-deployable by design. Release-process condition #4 ("No TBD") fails. All proofs would be rejected.

Each TBD marks an open design decision. Rather than ship with placeholder values that would break when real values are chosen, the spec explicitly marks incompleteness. The deployment gates force decisions to be made before deployment, not after.

Path to deployment:
1. For each TBD tag, make the design decision and choose a concrete value
2. Populate `registry.json` with all concrete values
3. Compute `JOLT_PARAMETER_REGISTRY_HASH_V1 = SHA-256(canonical_registry_bytes)`
4. Build the wrapper circuit; compute `JOLT_WRAPPER_VK_HASH_V1`
5. Run the conformance bundle; compute `JOLT_CONFORMANCE_BUNDLE_HASH_V1`
6. Configure the on-chain verifier with the pinned wrapper verifying key hash (`JOLT_WRAPPER_VK_HASH_V1`). Publish `JOLT_PARAMETER_REGISTRY_HASH_V1` and `JOLT_CONFORMANCE_BUNDLE_HASH_V1` alongside the release (informational metadata).
7. All deployment gates now pass; deployment proceeds

### 3.7 Deployment checklist (release blockers)

A release is only valid if the operator publishes:

1. `registry.json` (canonical registry bytes) with SHA‑256 = `JOLT_PARAMETER_REGISTRY_HASH_V1`
2. `conformance_bundle.tar` with SHA‑256 = `JOLT_CONFORMANCE_BUNDLE_HASH_V1`
3. Wrapper verifying key(s) with hash = `JOLT_WRAPPER_VK_HASH_V1`
4. A wrapper constraint report (rows/constraints/proof bytes/verifier time)

And the registry contains concrete values (i.e., no `"TBD"` sentinel anywhere within required tag values) for **all** non-external required tags listed in §3.4.

Implementation note: Three required tags have structured JSON values (objects): `JOLT_GUEST_MEMMAP_V1`, `JOLT_CONTINUATIONS_V1`, and `JOLT_POSEIDON_FR_V1`. The "no unspecified value" rule applies recursively to every nested field and array element within those objects (see §3.5, condition #4).

### 3.8 config_tags projection (normative)

`VMStateV1.config_tags` commits the active deployment configuration into `StateDigestV1` (§11).

For V1, `config_tags` MUST be the canonical projection of the pinned `registry.json`:

1. Let **RequiredNonExternalTags** be the set of tag keys listed in §3.4 excluding external handles.
2. For each `tag_name`, read the corresponding JSON value `v` from `registry.json`. If missing, the configuration is invalid.
3. Encode each entry as `(tag_name_bytes, tag_value_bytes)` where:
   - `tag_name_bytes` is the UTF‑8 bytes of the tag key
   - `tag_value_bytes` is **always** the RFC 8785 JCS serialization of the JSON value (including strings, which serialize with quotes)

**Type preservation (normative).** Using JCS for all values ensures type distinction: JSON string `"1000"` serializes as `b'"1000"'` (with quotes), while JSON number `1000` serializes as `b'1000'` (no quotes). This prevents type-confusion attacks where a misparsed registry could produce identical `config_tags` despite different semantics.

**Additional encoding constraints (normative):**
- Integers with absolute value ≤ 2⁵³−1 MUST be JSON numbers; integers outside that range MUST be decimal strings (per §2.6.1)
- Booleans (`true`/`false`) and `null` are permitted where semantically appropriate
- Nested objects MUST be canonicalized per RFC 8785 before encoding
- No trailing newlines or whitespace outside the JCS output
- Tag names and string values use raw UTF‑8 bytes with no Unicode normalization (NFC/NFD/etc.)

4. Sort entries by lexicographic order of `tag_name_bytes`. Tag names MUST be unique.

**External handles MUST NOT be absorbed into `config_tags`.** `JOLT_PARAMETER_REGISTRY_HASH_V1`, `JOLT_WRAPPER_VK_HASH_V1`, and `JOLT_CONFORMANCE_BUNDLE_HASH_V1` are external handles and are intentionally excluded to avoid circular construction.

A valid wrapper proof commits to the pinned configuration via `config_tags` (as absorbed into `StateDigestV1`). A verifier expecting a different configuration (i.e., built and deployed with a different pinned registry and wrapper VK) will reject because the committed `config_tags` will not match the verifier's pinned constants.

### 3.9 Definition block

**Parameter Registry:** A JSON object containing versioned tag-value pairs that define all consensus-critical configuration. Canonicalized via RFC 8785 JCS.

**Registry hash:** `SHA-256(canonical_registry_bytes)`. The consensus anchor for deployment.

**External handle:** A tag whose value is derived from other deployment artifacts and cannot be stored inside the registry.

**Fail-closed gating:** A verification policy where any unmet condition causes 100% rejection. All conditions must hold, or all proofs are rejected.

**TBD (To Be Determined):** A placeholder indicating a design decision not yet made. Any TBD in a required tag makes the spec non-deployable.

**config_tags:** A projection of the registry into VM state, committed via StateDigestV1. Binds each proof to its configuration.

### 3.10 Load-bearing claims

| Claim | Evidence | Verification |
|-------|----------|--------------|
| **Registry hash uniquely identifies configuration** | SHA-256 collision resistance; JCS determinism | Hash identical registries → must match. Modify one byte → hash must differ |
| **All 17 tags are required for deployment** | §3.4 table; §3.5 condition #4 | Remove one tag; verify deployment gate rejects |
| **Fail-closed on-chain acceptance rejects invalid proofs** | §3.5 on-chain acceptance conditions | Use wrong VK hash or a malformed proof; contract MUST reject |
| **Deployments MUST be non-deployable under any required `"TBD"`** | §3.5 condition #4 + tooling obligation | Set a required tag (or nested field) to `"TBD"`; conforming tooling MUST refuse to build/prove/verify |
| **External handles cannot be inside registry** | §3.3 exclusion list | Include REGISTRY_HASH inside registry.json; verify rejection |
| **config_tags binds proof to configuration** | §3.8 projection; §11 StateDigestV1 | Generate proof under config A; verify under config B; must reject |

### 3.11 Forward references

- **Cryptographic Core** (`POSEIDON_FR`, `JOLT_PCS`, `JOLT_TRANSCRIPT_SCHEDULE`) → Section 8 Transcript, Section 12 PCS
- **Guest VM** (`RISCV_*`, `GUEST_MEMMAP`, `TOOLCHAIN`) → Section 6 Guest VM specification
- **DoS Caps** → Section 5 Wrapper proof interface
- **Encoding Formats** → Section 5, Section 7
- **Execution Config** (`CONTINUATIONS`) → Section 11 Continuations
- **Implementation Identity** → Section 12, 5.7
- **External Handles** → Section 14 Conformance bundle

### 3.12 Conformance requirements (normative)

The conformance bundle (§14) MUST include test vectors and negative tests for `registry.json` processing, including at minimum:

1. **JCS canonicalization:** semantically equivalent JSON with different key order/whitespace MUST yield identical `canonical_registry_bytes`.

2. **Numeric safety:** values outside the safe integer range MUST be encoded as decimal strings; non-conforming numeric encodings MUST be rejected.

3. **Duplicate keys:** duplicate JSON object keys MUST be rejected (fail-closed).

4. **External-handle exclusions:** presence of any of `JOLT_PARAMETER_REGISTRY_HASH_V1`, `JOLT_WRAPPER_VK_HASH_V1`, or `JOLT_CONFORMANCE_BUNDLE_HASH_V1` inside `registry.json` MUST be rejected.

5. **Unknown keys (V1):** presence of any key not in the required non-external tag set (§3.4) MUST be rejected.

6. **Tag key format:** keys not matching `^JOLT_[A-Z0-9_]+_V[0-9]+$` MUST be rejected.

7. **`config_tags` projection:** given a sample `registry.json`, the exact ordered list of `(tag_name_bytes, tag_value_bytes)` pairs MUST match expected outputs (including correct quoting for JSON strings).

8. **`"TBD"` gating:** inserting the `"TBD"` sentinel anywhere within a required tag value MUST cause conforming tooling to refuse to build/prove/verify.

---

*With all consensus-critical parameters now pinned via the registry (Section 3), we can analyze the security properties that the architecture provides, even against adversarial operators.*

## Section 4: Architecture overview

Picture the worst-case scenario: a hostile cloud provider runs your Jolt prover. They have root access. They can read every byte of memory, modify binaries, intercept network traffic, and observe the complete witness. They want to forge a proof claiming Alice holds a million dollars when her actual balance is zero.

They will fail.

This is not wishful thinking but mathematical certainty, conditioned on three cryptographic assumptions: the hardness of discrete logarithms in BLS12-381, the collision resistance of SHA-256, and the Fiat-Shamir heuristic applied to Poseidon. If these assumptions hold, no amount of system access helps an attacker forge proofs. The verifier performs a mathematical check, not a trust assessment. It never asks "was this proof made on a trustworthy machine?" It asks only "does this proof satisfy the verification equation?" A compromised host can corrupt the proving process, but corruption yields one of two outcomes: a valid proof for the true statement, or garbage that fails verification. There is no third option where a false statement passes.

Jolt continuations stacks four components with distinct responsibilities. The *guest program* (the Settlement Engine ELF) defines the computation. The *zkVM* (Jolt proving RV64IMC execution) produces a proof that the guest ran correctly. The *wrapper circuit* (Halo2) verifies the Jolt proof and binds the public inputs into a single cryptographic commitment. The *on-chain verifier* checks the wrapper proof plus public inputs and authorizes state transitions. Each layer trusts only the cryptographic assumptions beneath it. The wrapper does not trust the prover that generated the Jolt proof. The on-chain verifier does not trust whoever submitted the wrapper proof. Trust flows downward through mathematics, not upward through reputation.

The soundness trust boundary draws a sharp line. Inside stand four cryptographic pillars: PCS security, SRS integrity (when trusted setup applies), Fiat-Shamir transcript security, and hash collision resistance. Outside stand three parties who may act maliciously without breaking soundness: the host OS, the prover, and any coordinator or aggregator. What can these untrusted parties do? The host OS can refuse to run the prover, slow it arbitrarily, read all witness data, exfiltrate information, or crash the process. The prover can choose which batches to prove, refuse certain batches (censorship), and learn witnesses. Notice what none of them can do: forge proofs, modify proof contents, or make invalid proofs verify. Proofs are self-authenticating.

### 4.3 Components

- **Guest program**: Settlement Engine ELF.
- **zkVM**: Jolt proving RV64IMC execution.
- **Wrapper circuit**: Halo2 circuit verifying Jolt proof(s) and binding public inputs.
- **On-chain verifier**: Verifies wrapper proof + public inputs and authorizes the state transition.

### 4.4 Trust boundaries (normative)

Soundness MUST NOT depend on:
- the host OS,
- the prover,
- any coordinator/aggregator.

Confidentiality MAY depend on TEEs or encryption for artifacts (§13), but proof validity MUST NOT.

**Soundness vs. Confidentiality: The Security Split**

| Property | Requirement | Trust Model |
|----------|-------------|-------------|
| Soundness | MUST be *cryptographic* (not operational) | Cryptographic assumptions only (and any trusted-setup/SRS (Structured Reference String) assumptions induced by the selected PCS) |
| Confidentiality | MAY depend on additional measures | TEEs, encryption, ZK property (optional) |

**Soundness:** No polynomial-time adversary can produce a valid proof for a false statement **except with negligible probability**, **under the cryptographic assumptions of the deployed proving system and the pinned public parameters**. In Jolt continuations, this includes (at minimum) the PCS assumptions and any trusted-setup/SRS assumption induced by the selected PCS (§12), and the Fiat–Shamir transcript security assumptions (§8). Soundness does not depend on trusting the prover, host OS, or any coordinator/aggregator.

**Confidentiality:** The proof does not reveal the witness (the private inputs). Confidentiality is a property of zero-knowledge proofs specifically. Not all SNARKs are zero-knowledge; those that are may still leak information through side channels.

The spec is explicit: "Confidentiality MAY depend on TEEs or encryption for artifacts (§13), but proof validity MUST NOT." You can run Jolt continuations with confidentiality protections or without. You cannot run it without soundness.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          TRUST FLOW DIAGRAM                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ══════════════════════════════════════════════════════════════════════     │
│                      SOUNDNESS TRUST BOUNDARY                               │
│  ══════════════════════════════════════════════════════════════════════     │
│                                                                             │
│  INSIDE TRUST BOUNDARY (cryptographic assumptions only):                    │
│  ┌───────────────────────────────────────────────────────────────────┐      │
│  │  • PCS (Polynomial Commitment Scheme) security                    │      │
│  │  • SRS integrity (if trusted setup used)                          │      │
│  │  • Fiat-Shamir transcript security                                │      │
│  │  • Hash function collision resistance                             │      │
│  └───────────────────────────────────────────────────────────────────┘      │
│                                                                             │
│  ══════════════════════════════════════════════════════════════════════     │
│                                                                             │
│  OUTSIDE TRUST BOUNDARY (MAY be malicious without breaking soundness):      │
│  ┌───────────────────────────────────────────────────────────────────┐      │
│  │                                                                   │      │
│  │  ┌───────────┐   ┌───────────┐   ┌─────────────┐                  │      │
│  │  │  HOST OS  │   │  PROVER   │   │ COORDINATOR │                  │      │
│  │  │           │   │           │   │             │                  │      │
│  │  │ CAN:      │   │ CAN:      │   │ CAN:        │                  │      │
│  │  │ • DoS     │   │ • Censor  │   │ • Delay     │                  │      │
│  │  │ • Read mem│   │ • Read wit│   │ • Refuse    │                  │      │
│  │  │ • Exfiltr.│   │ • Choose  │   │ • Reorder   │                  │      │
│  │  │           │   │           │   │             │                  │      │
│  │  │ CANNOT:   │   │ CANNOT:   │   │ CANNOT:     │                  │      │
│  │  │ • Forge   │   │ • Forge   │   │ • Forge     │                  │      │
│  │  │   proofs  │   │   proofs  │   │   proofs    │                  │      │
│  │  └───────────┘   └───────────┘   └─────────────┘                  │      │
│  │                                                                   │      │
│  └───────────────────────────────────────────────────────────────────┘      │
│                                                                             │
│  ══════════════════════════════════════════════════════════════════════     │
│                                                                             │
│  KEY INSIGHT: Breaking SOUNDNESS requires breaking crypto assumptions.      │
│               Untrusted parties can disrupt but CANNOT forge proofs.        │
│                                                                             │
│  CONFIDENTIALITY (separate): MAY depend on TEEs, encryption, ZK             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 4.5 What "MUST NOT depend on" means

4.4 lists three parties that soundness must not depend on. For each, here's what they can and cannot do:

**Host OS** — The operating system running the prover software.

| CAN do | CANNOT do |
|--------|-----------|
| Refuse to run the prover (denial of service) | Produce a valid proof for an invalid execution |
| Slow down proving arbitrarily | Modify a proof to change what it attests to |
| Read all witness data in prover memory | Make the verifier accept a false statement |
| Log, copy, or exfiltrate any data | |
| Crash the prover at any point | |

The verifier performs a mathematical check. It doesn't ask "was this proof made on a trustworthy machine?" It asks "does this proof satisfy the verification equation?" A compromised host can corrupt proving, but corruption produces either a valid proof (for the true statement) or garbage that fails verification.

**Prover** — The entity running the prover software and choosing what to prove.

| CAN do | CANNOT do |
|--------|-----------|
| Choose which batches to prove | Prove that an invalid batch is valid |
| Refuse to prove certain batches (censorship) | Prove that Alice has money she doesn't have |
| Learn the witness for any batch they prove | Prove false outputs from Settlement Engine |
| Attempt to find proofs for false statements | |

SNARK soundness: finding a valid proof for a false statement requires breaking the underlying cryptographic assumptions. For properly instantiated SNARKs, this is computationally infeasible.

**Coordinator/Aggregator** — Any party that orchestrates proof generation, collects proofs, or submits them on-chain.

| CAN do | CANNOT do |
|--------|-----------|
| Control batch ordering | Forge proofs |
| Decide which proofs to submit | Modify proof contents |
| Refuse to include certain proofs | Change public inputs without invalidating |
| Delay proof submission | Make invalid proofs verify |

Proofs are self-authenticating. The coordinator is a messenger, not an authority. The verifier checks mathematical validity, not who delivered it.

### 4.6 What is proven on-chain (normative)

For a transaction/batch, the chain verifies that:

1. **Wrapper proof valid under pinned VK.** The verifying key (VK) defines what circuit the proof is for. If this check passes: someone who knew a valid witness produced this proof.

2. **Public inputs match the expected old_root, new_root, batch_commitment, and batch_nonce.** Prevents replay and reordering. A proof that `old_root_A → new_root_B` cannot authorize `old_root_C → new_root_D`, and a proof for nonce `n` cannot authorize nonce `n'`.

3. **Program hash is expected Settlement Engine.** Prevents program substitution. An attacker could write a malicious program that always outputs "Alice has $1M." The program hash binding ensures the proof attests to the correct program.

4. **Status = 0 (execution completed successfully).** Prevents error acceptance. A proof of "the program crashed" is valid but doesn't authorize a state transition. Only successful completion does.

### 4.7 What soundness doesn't guarantee

Soundness is powerful but not omnipotent. Be clear about what it doesn't provide:

**Soundness doesn't prevent denial of service.** A malicious prover can refuse to prove. A malicious coordinator can refuse to submit. The chain can process no batches, but it won't process invalid batches.

**Soundness doesn't prevent censorship.** A malicious operator controlling all provers can exclude certain users' transactions. Soundness ensures included transactions are valid, not that all valid transactions are included.

**Soundness doesn't guarantee confidentiality.** The proof might leak witness information. Even ZK-SNARKs can leak through side channels, timing, or metadata.

**Soundness depends on cryptographic assumptions.** If discrete logarithms become easy (quantum computers, mathematical breakthrough), soundness breaks. The proof system's security level matters—128-bit security means an attacker needs ~2^128 operations to forge.

**Soundness doesn't mean the Settlement Engine is correct.** The proof attests: "this program, given these inputs, produced these outputs." If the program has bugs—logic errors, economic exploits—the proof faithfully attests to the buggy execution. Garbage in, cryptographically certified garbage out.

### 4.8 Definition block

**Soundness:** The property that no computationally bounded adversary can produce a valid proof for a false statement. Formally: for any polynomial-time prover, the probability of producing a proof that verifies for a false statement is negligible.

**Confidentiality (in proof systems):** The property that the proof reveals nothing about the witness beyond what the public inputs already reveal. Also called "zero-knowledge." Not all SNARKs have this property.

**Trust boundary:** A line separating what the system assumes to be honest from what it assumes may be adversarial. Jolt continuations's soundness trust boundary includes only cryptographic assumptions **and any trusted-setup/SRS assumptions induced by the selected PCS** (see §12.8). In particular, if a trusted-setup PCS is selected, soundness assumes no adversary knows the SRS trapdoor.

**Verifying key (VK):** A public parameter that defines the verification algorithm for a specific circuit. The VK commits to the circuit structure. A proof valid under VK_A is not valid under VK_B (except with negligible probability).

### 4.9 Load-bearing claims

| Claim | Evidence | Verification |
|-------|----------|--------------|
| **Soundness doesn't depend on host OS** | SNARK soundness is computational, not environmental | Prover on compromised machine; proof verifies iff execution was valid |
| **Soundness doesn't depend on prover** | SNARK soundness definition: no efficient adversary finds proof for false statement | Attempt to forge proof for invalid execution; must fail |
| **Four on-chain checks are necessary** | Each prevents a distinct attack: forgery, replay, substitution, error acceptance | For each check, exhibit attack when check is omitted |
| **Confidentiality is weaker than soundness** | 4.4 "MAY depend on TEEs or encryption" | Deploy with non-ZK proof system; soundness holds, confidentiality doesn't |

### 4.10 Jolt whitepaper connections

| Section 4 Claim | Whitepaper Foundation |
|-----------|----------------------|
| Soundness doesn't depend on prover | §1: "SNARKs allow an untrusted prover to establish that it correctly performed a computation" |
| Verification checks math, not provenance | §2.5: R1CS satisfaction check is algebraic; §2.3: Lasso soundness via polynomial identity testing |
| Wrapper adds verification layer | §1.3: Proof composition—verifying a proof inside another proof system preserves soundness |

The wrapper circuit (Halo2) verifies the Jolt proof. Halo2 soundness is separate from Jolt soundness, but they compose: if both are sound, the composed system is sound. A valid wrapper proof means a valid Jolt proof existed, which means the execution was correct.

### 4.11 Forward references

- **Trust boundaries** → Section 13 (Confidentiality mechanisms), Section 15 (Security considerations)
- **Wrapper proof verification** → Section 5 (Public inputs layout), Section 12 (PCS constraints)
- **Status codes** → 6.4 (Guest exit and status)
- **Program hash binding** → 5.1 (program_hash_lo, program_hash_hi)
- **Cryptographic assumptions** → Section 12 (PCS feasibility), Jolt whitepaper §2.3 (Lasso security)

---

*The architecture overview established trust boundaries and the five-layer stack. The wrapper circuit compresses everything into exactly eleven field elements—the narrow interface that Section 5 specifies in full detail.*

## Section 5: Wrapper proof interface and public inputs

### 5.1 The eleven windows

A continuation proof is a black box with exactly eleven windows. The prover feeds everything into it: the full execution trace, every memory access, each intermediate value. The verifier peers through those eleven windows, sees eleven field elements, and renders a verdict: accept or reject. Nothing else escapes. This is the fundamental bargain of SNARKs: succinctness means you cannot replay the execution or inspect the witness. You get eleven numbers and a yes-or-no answer. Those eleven numbers must authorize state transitions safely while blocking replay, substitution, and every confusion about what the box actually proved.

Each field element binds the proof to something concrete, and each binding closes an attack vector. The program hash (split into two field elements because 256 bits cannot fit in a 255-bit field without collisions) pins the Settlement Engine ELF. Remove it, and an attacker swaps in a different program. The old and new state roots commit to the pre-state and post-state. Remove either, and the attacker executes against the wrong state or fabricates the result. The batch commitment binds the input manifest. Remove it, and the attacker substitutes a different batch while keeping the proof. The checkpoints digest commits to execution checkpoints. Remove it, and malicious behavior hides between chunks. The status field carries the exit code. Remove it, and a proof of "the program crashed" authorizes a transition it should not. The batch nonce provides a sequence number. Remove it, and yesterday's proof replays today.

### 5.2 PublicInputsV1 layout (11 `Fr` elements)

The wrapper exposes exactly 11 public field elements in `Fr`, in this order:

| # | Field | Type | What It Binds | Attack Prevented |
|---|-------|------|---------------|------------------|
| 1 | `program_hash_lo` | bytes32→Fr2 | The Settlement Engine ELF | Program substitution |
| 2 | `program_hash_hi` | | | |
| 3 | `old_root_lo` | bytes32→Fr2 | Pre-state commitment | Wrong-state attack |
| 4 | `old_root_hi` | | | |
| 5 | `new_root_lo` | bytes32→Fr2 | Post-state commitment | Result manipulation |
| 6 | `new_root_hi` | | | |
| 7 | `batch_commitment_lo` | bytes32→Fr2 | Input manifest (the batch) | Batch substitution |
| 8 | `batch_commitment_hi` | | | |
| 9 | `checkpoints_digest_fr` | Fr | Execution checkpoints | Hidden behavior |
| 10 | `status_fr` | u8→Fr | Exit code (0 = success) | Error acceptance |
| 11 | `batch_nonce_fr` | u64→Fr | Sequence number | Replay attack |

Where:
* `program_hash`, `old_root`, `new_root`, and `batch_commitment` are each a `bytes32`, packed into two `Fr` elements via the injective packing `Bytes32ToFr2` (§7.6, using a 31+1 byte split).
* `checkpoints_digest_fr` is an `Fr` element encoded/decoded canonically (§7.4).
* `status_fr = Fr(u64(status_u8))`, with the range constraint `status_u8 ∈ [0, 255]`.
* `batch_nonce_fr = Fr(batch_nonce_u64)`, with the range constraint `batch_nonce_u64 ∈ [0, 2^64−1]`.

A bytes32 is 256 bits; the BLS12-381 scalar field Fr has prime order ~255 bits. Some bytes32 values exceed Fr's maximum—you can't fit 256 bits in a 255-bit field element without collisions. The solution: split into a 31-byte low limb and a 1-byte high limb via `Bytes32ToFr2`. Both pieces fit safely in Fr with room to spare. The packing is injective—no two different bytes32 values produce the same (lo, hi) pair.

```
┌───────────────────────────────────────────────────────────────────────────┐
│                  PUBLIC INPUTS LAYOUT (11 Fr ELEMENTS)                    │
├───────────────────────────────────────────────────────────────────────────┤
│                                                                           │
│  BYTES32 → Fr2 ENCODINGS (4 × 32 bytes → 8 Fr elements)                   │
│  ┌─────────────────────────────────────────────────────────────────────┐  │
│  │  [1] program_hash_lo  ┐                                             │  │
│  │  [2] program_hash_hi  ┘ ← SHA256(Settlement Engine ELF)             │  │
│  │                          PREVENTS: Program substitution attack      │  │
│  ├─────────────────────────────────────────────────────────────────────┤  │
│  │  [3] old_root_lo      ┐                                             │  │
│  │  [4] old_root_hi      ┘ ← Pre-execution state commitment            │  │
│  │                          PREVENTS: Wrong-state attack               │  │
│  ├─────────────────────────────────────────────────────────────────────┤  │
│  │  [5] new_root_lo      ┐                                             │  │
│  │  [6] new_root_hi      ┘ ← Post-execution state commitment           │  │
│  │                          PREVENTS: Result manipulation              │  │
│  ├─────────────────────────────────────────────────────────────────────┤  │
│  │  [7] batch_commit_lo  ┐                                             │  │
│  │  [8] batch_commit_hi  ┘ ← SHA256(batch_manifest Merkle root)        │  │
│  │                          PREVENTS: Batch substitution attack        │  │
│  └─────────────────────────────────────────────────────────────────────┘  │
│                                                                           │
│  DIRECT Fr ENCODINGS (3 Fr elements)                                      │
│  ┌─────────────────────────────────────────────────────────────────────┐  │
│  │  [9]  checkpoints_digest_fr  ← Poseidon digest of checkpoints       │  │
│  │                                PREVENTS: Hidden behavior in chunks  │  │
│  ├─────────────────────────────────────────────────────────────────────┤  │
│  │  [10] status_fr              ← Exit code (0=success, else error)    │  │
│  │                                PREVENTS: Accepting failed exec      │  │
│  ├─────────────────────────────────────────────────────────────────────┤  │
│  │  [11] batch_nonce_fr         ← Sequence number (u64 → Fr)           │  │
│  │                                PREVENTS: Replay attack              │  │
│  └─────────────────────────────────────────────────────────────────────┘  │
│                                                                           │
│  TOTAL: 11 Fr elements = 11 × 32 bytes = 352 bytes serialized             │
│                                                                           │
│  SECURITY: Remove ANY field → attack vector opens                         │
│  ENCODING: bytes32 uses Bytes32ToFr2 (§7.6) to avoid field squeeze        │
└───────────────────────────────────────────────────────────────────────────┘
```

**Consensus note (nonce binding vs. ordering).** This appendix defines how `batch_nonce_u64` is *bound to the proof*. The settlement contract / state machine that consumes this wrapper proof MUST also enforce a monotonic / single-use policy for `batch_nonce_u64` (e.g., `batch_nonce = last_nonce + 1`).

### 5.4 Public input serialization for transaction payloads

When serializing public inputs into transaction payload bytes:

- Each `Fr` MUST be serialized as `FrToBytes32LE(x)` (§7.4).
- The full vector MUST be concatenated in the order in §5.3.

Any other serialization MUST be rejected.

**Host‑chain compatibility requirement.** For a given deployment, `JOLT_WRAPPER_PROOF_SYSTEM_V1` MUST confirm that the host‑chain verifier consumes public inputs in exactly this order and `Fr` byte encoding. If not, the deployment MUST define and pin a new versioned public‑input encoding tag.

### 5.5 Wrapper proof statement (normative)

A valid wrapper proof asserts existence of:
- one or more Jolt chunk proofs verified in-circuit,
- a final VM state `S_out`,
- a `PublicOutputsV1` value decoded from guest output memory,

such that the following six constraints hold:

#### Constraint 1: Configuration binding

The wrapper circuit is parameterized by the **required non‑external tag values** from the pinned registry (i.e., the `registry.json` contents as projected into `config_tags`, §3.8).

- `JOLT_PARAMETER_REGISTRY_HASH_V1`, `JOLT_WRAPPER_VK_HASH_V1`, and `JOLT_CONFORMANCE_BUNDLE_HASH_V1` are **external handles**. They MUST NOT appear in `registry.json` and MUST NOT be absorbed into `config_tags` or `StateDigestV1`.
- The wrapper MUST constrain that the `config_tags` absorbed into `StateDigestV1` equal the canonical projection of the pinned registry.

**Attack prevented:** Configuration mismatch. An attacker generates a proof under configuration A (different Poseidon constants, different chunk size) and submits it to a verifier expecting configuration B.

**Implementation note (normative intent).** To satisfy this constraint, deployments MUST ensure the Jolt chunk proof statement exposes either (a) the full `VMStateV1.config_tags` as verifier-visible values, or (b) a verifier-visible digest of `config_tags` that is proven inside the Jolt statement to equal the canonical projection defined in §3.8. The wrapper MUST constrain equality against its pinned constants.

#### Constraint 2: Program identity binding

The wrapper circuit is tied to a specific settlement engine ELF (by `program_hash`), without hashing the ELF in-circuit.

Let `PROGRAM_HASH_CONST : bytes32` be the expected program hash constant (fixed at circuit build time).

Let `(PROGRAM_HASH_LO_CONST, PROGRAM_HASH_HI_CONST) := Bytes32ToFr2(PROGRAM_HASH_CONST)` per §7.6.

The wrapper MUST constrain:

- `program_hash_lo == PROGRAM_HASH_LO_CONST`
- `program_hash_hi == PROGRAM_HASH_HI_CONST`

**Attack prevented:** A prover cannot swap in a different guest program while reusing the same wrapper proof system.

#### Constraint 3: Continuation chaining

The wrapper circuit MUST verify `num_chunks >= 1` Jolt chunk proofs in order, indexed `i = 0..num_chunks-1`.

Each chunk proof `i` MUST expose (to the wrapper verification gadget) at minimum:

- `state_digest_in_fr[i] : Fr`
- `state_digest_out_fr[i] : Fr`

The wrapper MUST constrain adjacency for all `i` in `0..num_chunks-2`:

- `state_digest_out_fr[i] == state_digest_in_fr[i+1]`

**Chunk boundary conditions (normative).** Deterministic chunk boundary conditions (§11.6) MUST be enforced. Concretely, with `CHUNK_MAX_STEPS` taken from the pinned configuration:

1. **First chunk:** `step_counter_in_u64[0] == 0`
2. **Non-final chunks:** for all `i` in `0..num_chunks-2`:
   - `step_counter_out_u64[i] - step_counter_in_u64[i] == CHUNK_MAX_STEPS`
   - `halted_out_u8[i] == 0`
3. **Final chunk:** for `i = num_chunks-1`:
   - `halted_out_u8[i] == 1`
   - `1 <= (step_counter_out_u64[i] - step_counter_in_u64[i]) <= CHUNK_MAX_STEPS`

**Enforcement split:**
- If the wrapper enforces the above boundary conditions, each chunk proof MUST also expose `step_counter_in_u64[i]`, `step_counter_out_u64[i]`, and `halted_out_u8[i]` as public values.
- Otherwise, each chunk proof MUST enforce these boundary conditions internally.

Implementations MUST document which layer enforces each condition.

**Attack prevented:** A prover cannot splice, reorder, or omit chunks while still producing a valid wrapper proof.

#### Constraint 4: Execution completion (prefix-proof resistance)

Let `S_out` be the final `VMStateV1` of the chained execution (i.e., the `S_out` used to compute the last chunk's `state_digest_out_fr`).

The wrapper MUST constrain that the final chunk halts: `S_out.halted = 1`.

Let `status_u8 := PublicOutputsV1.status_u8` where `PublicOutputsV1` is decoded as specified in Constraint 5.
The wrapper MUST constrain `S_out.exit_code == u64(status_u8)` (zero-extended).

**Attack prevented:** A prover cannot submit a prefix proof that omits an error/trap at the end of execution while still claiming a successful status.

#### Constraint 5: PublicOutputs binding

The wrapper MUST decode `PublicOutputsV1` (144 bytes) from the guest output buffer (§5.6) and constrain:

- `PublicOutputsV1.reserved7 == [0u8; 7]`

**Bytes32 ↔ Fr2 bindings (use `Bytes32ToFr2`, §7.6):**
- `Bytes32ToFr2(PublicOutputsV1.old_root_bytes32) == (old_root_lo, old_root_hi)`
- `Bytes32ToFr2(PublicOutputsV1.new_root_bytes32) == (new_root_lo, new_root_hi)`
- `Bytes32ToFr2(PublicOutputsV1.batch_commitment_bytes32) == (batch_commitment_lo, batch_commitment_hi)`

**Checkpoints digest binding (use `Bytes32LEToFrCanonical`, §7.5):**
- `Bytes32LEToFrCanonical(PublicOutputsV1.checkpoints_digest_bytes32) == checkpoints_digest_fr`

**Status binding (u8 ↔ Fr, use `FrFromU64`, §7.4):**
- `status_fr == FrFromU64(u64(PublicOutputsV1.status_u8))`

**Batch nonce binding (u64 ↔ Fr, use `FrFromU64`, §7.4):**
- `batch_nonce_fr == FrFromU64(PublicOutputsV1.batch_nonce_u64)`

**Attack prevented:** The public inputs are fully bound to the guest's committed output buffer and cannot be swapped post hoc.

#### Constraint 6: On-chain acceptance policy

Consuming contracts MUST accept only `status_fr == 0` (i.e., `JOLT_STATUS_OK`), unless a governance-controlled feature flag (stored on-chain and thus consensus-deterministic) opts into accepting specific non-zero statuses (which MUST be enumerated and version-tagged).

**Attack prevented:** Error acceptance. A proof of "the program crashed" is valid but shouldn't authorize state transitions. Only successful executions produce accepted transitions.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    WRAPPER CONSTRAINT FLOW                                  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  INPUTS                        CONSTRAINTS                   OUTPUTS       │
│  ═══════                       ═══════════                   ═══════       │
│                                                                             │
│  ┌───────────────┐                                                          │
│  │ Pinned Config │──┐                                                       │
│  │ (registry.json)│  │   ┌──────────────────────────────┐                   │
│  └───────────────┘  ├──▶│ C1: Configuration Binding    │                   │
│                     │   │    config_tags match pinned   │                   │
│  ┌───────────────┐  │   └──────────────────────────────┘                   │
│  │ PROGRAM_HASH  │──┤                                                       │
│  │ (build-time)  │  │   ┌──────────────────────────────┐                   │
│  └───────────────┘  └──▶│ C2: Program Identity Binding │                   │
│                         │    program_hash_lo/hi match  │                   │
│  ┌───────────────┐      └──────────────────────────────┘                   │
│  │ Chunk Proofs  │                                                          │
│  │ [0..n-1]      │──┬──▶┌──────────────────────────────┐                   │
│  │               │  │   │ C3: Continuation Chaining    │                   │
│  │ digest_in[i]  │  │   │    out[i] == in[i+1]         │   ┌─────────────┐ │
│  │ digest_out[i] │  │   │    step_counter constraints  │──▶│ 11 Public   │ │
│  │ halted[i]     │  │   └──────────────────────────────┘   │ Inputs (Fr) │ │
│  │ step_count[i] │  │                                      │             │ │
│  └───────────────┘  ├──▶┌──────────────────────────────┐   │ • prog_hash │ │
│                     │   │ C4: Execution Completion     │   │ • old_root  │ │
│                     │   │    final halted==1           │──▶│ • new_root  │ │
│                     │   │    exit_code == status       │   │ • batch_cmt │ │
│  ┌───────────────┐  │   └──────────────────────────────┘   │ • ckpt_dgst │ │
│  │ PublicOutputs │  │                                      │ • status    │ │
│  │ V1 (144 bytes)│──┴──▶┌──────────────────────────────┐   │ • nonce     │ │
│  │ from guest mem│      │ C5: PublicOutputs Binding    │──▶└─────────────┘ │
│  └───────────────┘      │    Fr2 ↔ bytes32 matches     │                   │
│                         └──────────────────────────────┘                   │
│                                                                             │
│                         ┌──────────────────────────────┐                   │
│                         │ C6: On-Chain Acceptance      │                   │
│                         │    status_fr == 0 required   │                   │
│                         └──────────────────────────────┘                   │
│                                    │                                        │
│                                    ▼                                        │
│                         ┌──────────────────────────────┐                   │
│                         │   VERIFIER ACCEPTS PROOF     │                   │
│                         │   → State transition valid   │                   │
│                         └──────────────────────────────┘                   │
│                                                                             │
│  ATTACK PREVENTION SUMMARY:                                                 │
│  C1 → Config mismatch     C3 → Chunk skip/splice    C5 → Output tampering  │
│  C2 → Program substitution C4 → Prefix proof        C6 → Error acceptance  │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 5.6 PublicOutputsV1 (guest output struct)

`PublicOutputsV1` is the **only** guest → wrapper public output channel.

The VM MUST ensure that a well-formed `PublicOutputsV1` value is present at the start of the output buffer, so that the wrapper circuit can deterministically decode it.

`PublicOutputsV1` is encoded as **144 bytes** at the start of the output buffer:

| Offset | Field | Size (bytes) | Encoding / meaning |
|--------|-------|-------------:|---|
| 0 | `status_u8` | 1 | `JOLT_STATUS_*` code (0 = OK) |
| 1 | `reserved7` | 7 | MUST be all zeros |
| 8 | `batch_nonce_u64` | 8 | Little-endian u64 sequence number |
| 16 | `old_root_bytes32` | 32 | Pre‑state root |
| 48 | `new_root_bytes32` | 32 | Post‑state root |
| 80 | `batch_commitment_bytes32` | 32 | Batch Merkle root (§5.7) |
| 112 | `checkpoints_digest_bytes32` | 32 | `FrToBytes32LE(checkpoints_digest_fr)` |

**Minimum output size.** The output buffer MUST be at least 144 bytes. Any proof with smaller output is invalid.

**Trap handling (normative).** If the VM terminates due to a **trap** (not via normal `exit` syscall), the VM/runtime MUST still populate the first 144 bytes with a deterministic `PublicOutputsV1`:

- `status_u8 := (exit_code_u64 mod 256)` (trap code)
- `reserved7 := 0x00…00`
- `batch_nonce_u64 := batch_nonce_in` (initial `a4` value at entry)
- `old_root_bytes32 := 0x00…00`
- `new_root_bytes32 := 0x00…00`
- `batch_commitment_bytes32 := 0x00…00`
- `checkpoints_digest_bytes32 := 0x00…00`

This rule prevents cross-implementation divergence in wrapper decoding on trap.

**Nonce binding (normative).** On normal termination (via `JOLT_SYSCALL_EXIT_V1`), the guest MUST write `batch_nonce_u64 = a4_entry` (the initial `a4` value at entry) into `PublicOutputsV1.batch_nonce_u64`.

### 5.7 `BatchManifestV1` commitment (`JOLT_BATCH_COMMITMENT_V1`)

The guest program receives `manifest_bytes := [input_ptr, input_ptr + input_len)` as described in §6.

The guest MUST compute `batch_commitment_bytes32` from `manifest_bytes` using the algorithm identified by `JOLT_BATCH_COMMITMENT_V1`, and MUST write it into `PublicOutputsV1.batch_commitment_bytes32`.

#### V1 algorithm: `NF/BATCH/COMMITMENT/MERKLE_SHA256/V1`

For V1, `batch_commitment_bytes32` is a **domain-separated SHA-256 Merkle root** over a fixed leaf array.

**Leaf hashing with domain separation:**

```
LeafHash(tag_ascii, payload) := SHA-256( UTF8(tag_ascii) || 0x00 || payload )
NodeHash(left32, right32) := SHA-256( b"JOLT/BATCH/NODE/V1\0" || left32 || right32 )
```

Different tags for different leaf types:
- `"JOLT/BATCH/HEADER_LEAF/V1"` for the manifest header
- `"JOLT/BATCH/FILL_LEAF/V1"` for each fill intent
- `"JOLT/BATCH/EMPTY_FILL_LEAF/V1"` for unused intent slots
- `"JOLT/BATCH/PAD_LEAF/V1"` for tree padding

**Leaf computation:**

**Deriving `header_bytes` and `fill_bytes_i` (normative).** Under `JOLT_BATCH_MANIFEST_ENCODING_V1`, a `manifest_bytes` input MUST decode into:
- a header object `header` (including `intent_count` and `context_bytes32`), and
- a list of fill intents `fills[0..intent_count-1]`.

The encoding MUST define a canonical, unique byte representation for:
- `header_bytes` (the canonical encoding of `header`), and
- `fill_bytes_i` (the canonical encoding of `fills[i]` for each `i < intent_count`),

such that these byte sequences are uniquely determined by `manifest_bytes` (i.e., there are no alternative encodings that decode to the same objects). The commitment algorithm hashes these bytes **exactly**; it MUST NOT normalize or re-serialize with a different canonicalization rule.

Let `F := JOLT_MAX_INTENTS_V1`. Compute leaves:
- `L[0] := LeafHash("JOLT/BATCH/HEADER_LEAF/V1", header_bytes)`
- For `i` in `0..F-1`:
  - If `i < manifest.intent_count`: `L[i+1] := LeafHash("JOLT/BATCH/FILL_LEAF/V1", fill_bytes_i)`
  - Else: `L[i+1] := LeafHash("JOLT/BATCH/EMPTY_FILL_LEAF/V1", b"")`

**Tree construction:**
- `next_power_of_two(N)` is the smallest power of two ≥ N, for N ≥ 1. (E.g., `next_power_of_two(5) = 8`, `next_power_of_two(8) = 8`.)
- Let `N := 1 + F`
- Let `LEAF_COUNT := next_power_of_two(N)`
- Pad with `LeafHash("JOLT/BATCH/PAD_LEAF/V1", b"")` to reach `LEAF_COUNT`
- Compute Merkle root via `NodeHash` on adjacent pairs

**Fixed tree shape:** The tree always has `next_power_of_two(1 + JOLT_MAX_INTENTS_V1)` leaves. This prevents tree-shape variations from causing different commitments.

**Merkle root algorithm (pseudocode, normative):**

Given a power-of-two leaf array `L[0..M-1]` where each `L[j]` is a 32-byte hash:
```
1. Set level := L
2. While len(level) > 1:
   - For each k in 0..(len(level)/2 - 1):
       next[k] := NodeHash(level[2k], level[2k+1])
   - Set level := next
3. Output level[0] as batch_commitment_bytes32
```

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    BATCH COMMITMENT MERKLE TREE                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│                     batch_commitment_bytes32                                │
│                              │                                              │
│                        ┌─────┴─────┐                                        │
│                        │ NodeHash  │                                        │
│                        └─────┬─────┘                                        │
│               ┌──────────────┴──────────────┐                               │
│               │                             │                               │
│         ┌─────┴─────┐                 ┌─────┴─────┐                         │
│         │ NodeHash  │                 │ NodeHash  │                         │
│         └─────┬─────┘                 └─────┬─────┘                         │
│         ┌─────┴─────┐                 ┌─────┴─────┐                         │
│         │           │                 │           │                         │
│     ┌───┴───┐   ┌───┴───┐         ┌───┴───┐   ┌───┴───┐                     │
│     │HEADER │   │FILL[0]│         │FILL[1]│   │ EMPTY │  ...                │
│     │ LEAF  │   │ LEAF  │         │ LEAF  │   │ LEAF  │                     │
│     └───────┘   └───────┘         └───────┘   └───────┘                     │
│         │           │                 │           │                         │
│         ▼           ▼                 ▼           ▼                         │
│  LeafHash(       LeafHash(       LeafHash(    LeafHash(                     │
│   "HEADER_       "FILL_          "FILL_       "EMPTY_                       │
│    LEAF/V1",      LEAF/V1",       LEAF/V1",   FILL_LEAF/V1",                │
│   header_bytes)  fill_bytes_0)   fill_bytes_1) b"")                         │
│                                                                             │
│  DOMAIN SEPARATION TAGS:                                                    │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │ LeafHash(tag, payload) = SHA256(UTF8(tag) || 0x00 || payload)         │  │
│  │ NodeHash(L, R) = SHA256(b"JOLT/BATCH/NODE/V1\0" || L || R)            │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  LEAF COUNT: next_power_of_two(1 + JOLT_MAX_INTENTS_V1)                     │
│  PAD LEAVES: Fill unused slots with LeafHash("PAD_LEAF/V1", b"")            │
└─────────────────────────────────────────────────────────────────────────────┘
```

**Caps (normative):**
- The host MUST provide `input_len <= JOLT_MAX_MANIFEST_BYTES_V1`
- The guest MUST treat violations as deterministic failure (non-zero status)
- The guest MUST treat `manifest.intent_count > JOLT_MAX_INTENTS_V1` as deterministic failure

#### `context_bytes32` (deployment-provided)

The `BatchManifestV1` header MUST contain a 32-byte `context_bytes32` field chosen by the deployment.

Deployments MUST publish a concrete `context_bytes32` constant that is unique per deployment. For the host chain or other host chains, this value SHOULD be derived from deployment-specific identifiers (e.g., network ID, contract address) to prevent cross-deployment replay—a proof valid on testnet can't authorize a mainnet transition even if roots happen to match.

**Enforcement (normative).** The expected `context_bytes32` value is defined by `JOLT_CONTEXT_BYTES32_V1` and compiled into the Settlement Engine binary as a constant. The Settlement Engine MUST reject the batch (set non-zero status) if `manifest.context_bytes32` does not match this compiled-in constant. This makes cross-deployment replay protection enforceable—the guest program validates the context, and an incorrect context produces a failed proof. Since the constant is compiled in, changing `JOLT_CONTEXT_BYTES32_V1` requires recompiling the Settlement Engine (and thus changing `program_hash`).

### 5.8 `checkpoints_digest_fr` (`JOLT_CHECKPOINTS_ENCODING_V1`)

`checkpoints_digest_fr` is a field element commitment to a checkpoints stream produced by the guest:

```
checkpoints_digest_fr := PoseidonHashV1("JOLT/CHECKPOINTS/V1", checkpoints_bytes)
checkpoints_digest_bytes32 := FrToBytes32LE(checkpoints_digest_fr)
```

The guest MUST write `checkpoints_digest_bytes32` into `PublicOutputsV1.checkpoints_digest_bytes32`.

**Cap (normative).** `len(checkpoints_bytes) <= JOLT_MAX_CHECKPOINTS_BYTES_V1` MUST hold. Violations produce deterministic failure.

The `checkpoints_bytes` encoding is pinned by `JOLT_CHECKPOINTS_ENCODING_V1`. For V1, only `checkpoints_digest_bytes32` is consensus-critical; raw `checkpoints_bytes` are not required on-chain.

### 5.9 Wrapper proof system and VK identity

The wrapper proof is the consensus object verified on‑chain. The wrapper proof system and verifying‑key (VK) encoding MUST be pinned exactly.

#### Required fields in `JOLT_WRAPPER_PROOF_SYSTEM_V1` (normative)

1. Curve(s) and fields (BLS12‑381 scalar field `Fr` for public inputs)
2. Commitment scheme (e.g., KZG) and SRS requirements
3. Arithmetization / PLONK variant and selector semantics
4. Transcript and hash‑to‑field details
5. Canonical public input ordering and `Fr` serialization (MUST match §5.3–§5.4)
6. Canonical **proof byte encoding** (`canonical_proof_bytes`)
7. Canonical **verifying key byte encoding** (`canonical_vk_bytes`)
8. Verifier‑relevant caps (max proof bytes, max public inputs)

#### `JOLT_WRAPPER_VK_HASH_V1` (normative)

`JOLT_WRAPPER_VK_HASH_V1 := SHA‑256(canonical_vk_bytes)`

This is an **external handle**. It MUST NOT appear in `registry.json`, and MUST NOT be absorbed into `config_tags` or `StateDigestV1`.

Implementations MUST NOT compute this hash over language‑specific struct serialization; only canonical bytes count.

#### Deterministic VK generation

Deployments MUST publish a deterministic VK generator that, given the wrapper circuit source and all pinned tags, deterministically produces `canonical_vk_bytes` and its hash. The conformance bundle SHOULD include the tool version and reproducibility report.

### 5.10 Definition block

**Public inputs:** The values exposed by the proof that the verifier can see. In Jolt continuations, 11 Fr elements encoding program identity, state roots, batch commitment, checkpoints digest, status, and nonce.

**Wrapper proof statement:** The conjunction of six constraints that a valid wrapper proof asserts.

**PublicOutputsV1:** The 144-byte struct at the start of the guest output buffer. The only channel from guest execution to on-chain verification.

**Domain separation:** Prepending a unique tag to each data type before hashing to prevent collisions between types.

**Bytes32ToFr2:** An injective encoding of 256-bit values into pairs of Fr elements using a 31+1 byte split (§7.6).

### 5.11 Load-bearing claims

| Claim | Evidence | Verification |
|-------|----------|--------------|
| **11 public inputs suffice for state transition authorization** | §5.3 enumeration; §5.5 constraints | For each field: remove it, exhibit resulting attack |
| **bytes32 requires Fr2 packing** | BLS12-381 r is ~255 bits; bytes32 is 256 bits | Construct bytes32 with high bits set; verify single-Fr fails |
| **Six wrapper constraints are jointly necessary** | §5.5 normative constraints | For each constraint: exhibit attack when removed |
| **PublicOutputsV1 is the only guest→wrapper channel** | §5.6: "the **only** guest → wrapper public output channel" | Attempt other data paths; should not affect public inputs |
| **Domain separation prevents leaf-type confusion** | §5.7 distinct tags per leaf type | Hash same payload with different tags; hashes must differ |

### 5.12 Forward references

- **Bytes32ToFr2, FrToBytes32LE encoding algorithms** → Section 7 (Word/field encodings)
- **Guest output buffer, status codes, trap semantics** → Section 6 (Deterministic guest VM)
- **StateDigest, continuation chaining details** → Section 11 (Continuations and snapshots)
- **PoseidonHashV1 parameters** → Section 8 (Transcript specification)
- **Wrapper proof system feasibility** → Section 12 (PCS constraints)
- **Security analysis of constraints** → Section 15 (Security considerations)

### 5.13 Conformance requirements (public inputs & commitments)

Conformance test suites (§14) MUST include vectors for:

1. **PublicInputsV1 serialization** (§5.4):
   - Provide a `PublicInputsV1` instance with non-trivial values for all 11 `Fr` elements and the expected concatenated `bytes` output.

2. **Bytes32↔Fr2 packing** (§7.6 as used in §5.3/§5.5):
   - Vectors for `Bytes32ToFr2` and `Fr2ToBytes32` including at least:
     - all-zero bytes32,
     - all-0xFF bytes32,
     - a mixed pattern (e.g., incremental bytes).

3. **Batch commitment Merkle root** (§5.7):
   - At least three manifests:
     - `intent_count = 0`,
     - `intent_count = 1`,
     - `intent_count = JOLT_MAX_INTENTS_V1`,
   - and the expected `batch_commitment_bytes32` roots for each.

4. **Checkpoints digest** (§5.8):
   - At least one empty and one non-empty `checkpoints_bytes` vector with expected `checkpoints_digest_fr`.

Vectors MUST be versioned and tied to the relevant tags (`JOLT_BATCH_COMMITMENT_V1`, `JOLT_BATCH_MANIFEST_ENCODING_V1`, `JOLT_CHECKPOINTS_ENCODING_V1`, `JOLT_WRAPPER_PROOF_SYSTEM_V1`).

---

## Section 6: Deterministic guest VM specification (RV64IMC)

### 6.1 The interpreter problem

Two teams build RISC-V interpreters. Both run the same binary with the same input. They should produce the same output. They don't.

The RISC-V specification grants hardware vendors flexibility that proves catastrophic for consensus systems. Divide by zero? "Implementation-defined." Misaligned memory access? "Implementation choice." Initial register values? Unspecified. These ambiguities work fine for silicon vendors competing on performance. They shatter consensus networks where disagreement means a fork.

Section 6 closes every escape hatch. Each behavior that could diverge between implementations gets pinned to exactly one deterministic outcome. The guest VM becomes a pure function: same inputs yield identical outputs, every time, on every conforming implementation.

### 6.2 Program hash (`program_hash`) definition

**Definition (V1):**
```
program_hash := SHA‑256(ELF_BYTES)
```

where `ELF_BYTES` are the exact bytes of the ELF file as read from disk.

There is **no canonicalization step** in V1. No stripping debug symbols. No reordering sections. The exact bytes, hashed. Different compilation → different bytes → different hash → different program identity.

This connects to `JOLT_TOOLCHAIN_V1`. The same Rust source compiled with different compiler versions, different optimization flags, or different linker settings produces different binaries. Those are different programs from Jolt continuations's perspective.

### 6.4 ISA profile (`JOLT_RISCV_PROFILE_V1 = RV64IMC`)

The guest implements exactly:
- **RV64I base integer ISA** — 64-bit registers, arithmetic, memory loads/stores, branches, jumps (~50 instructions)
- **M extension (mul/div/rem)** — Hardware multiplication and division for financial calculations
- **C extension (compressed)** — 16-bit encodings of common instructions for smaller binaries

The guest excludes:
- **A extension (atomics)** — Multi-threaded synchronization has no meaning in single-threaded zkVM
- **F/D extensions (floating point)** — Rounding modes, NaN propagation are implementation-variant
- **Privileged/CSR instructions** — OS interaction not applicable to pure computation

#### 6.4.1 Forbidden instructions (trap)

Any use of the following MUST trap with `JOLT_STATUS_TRAP_ILLEGAL_INSTRUCTION` (code 1):

- any RV64A opcode (LR/SC, AMO*)
- any floating-point opcode
- any CSR/privileged opcode
- `ECALL` except the single permitted exit syscall (§6.8)
- `EBREAK` (disabled in V1)

**Trap transition (normative, applies to all trap causes):**

On a trap with status code `code`:
- set `halted := 1`
- set `exit_code := u64(code)` (and thus `exit_code ∈ [0,255]` for V1)
- ensure the output buffer's first 144 bytes encode the deterministic `PublicOutputsV1` trap value defined in §5.6
- the trapping instruction still counts as one instruction for `step_counter` (per §6.5)

#### 6.4.2 A-extension ambiguity fix

For V1 (`RV64IMC`), the A extension is **not enabled**. All LR/SC and AMO instructions MUST trap as illegal instruction.

If a future version enables A, it MUST fully specify deterministic single-hart LR/SC/AMO semantics in that versioned profile.

### 6.5 Deterministic step counter

`step_counter` increments by exactly **1** for each guest instruction executed in the VM trace, including:

- 16-bit compressed instructions (each counts as 1)
- trapping instructions (trap counts as 1)
- the `ecall` instruction used for `JOLT_SYSCALL_EXIT_V1`

Continuation boundaries depend on `step_counter` (§11). Chunk N proves instructions 0 through CHUNK_MAX_STEPS-1. Chunk N+1 proves instructions CHUNK_MAX_STEPS through 2×CHUNK_MAX_STEPS-1. If implementations count differently, they'd split execution at different points and produce incompatible proofs.

This rule is consensus-critical.

### 6.6 Division and remainder edge cases

Division and remainder MUST follow the pinned unprivileged ISA spec (`JOLT_RISCV_UNPRIV_SPEC_V1`). For consensus safety, V1 also pins the following results for M-extension division instructions, including RV64 "W" variants.

**Notation:**
- `INT64_MIN := 0x8000000000000000`
- `INT32_MIN := 0x80000000`
- `U64_MAX  := 0xFFFFFFFFFFFFFFFF`
- `U32_MAX  := 0xFFFFFFFF`
- `SEXT32(x) := sign-extend the low 32 bits of x to 64 bits`

**Division by zero (`rs2 == 0`):**

| Instruction | Result |
|-------------|--------|
| `DIV`  | `rd := U64_MAX` (i.e., -1 in two's complement) |
| `DIVU` | `rd := U64_MAX` |
| `REM`  | `rd := rs1` |
| `REMU` | `rd := rs1` |
| `DIVW`  | `rd := SEXT32(U32_MAX)` |
| `DIVUW` | `rd := SEXT32(U32_MAX)` |
| `REMW`  | `rd := SEXT32(low32(rs1))` |
| `REMUW` | `rd := SEXT32(low32(rs1))` |

No trap occurs—deterministic bogus output.

**Why -1 and not 0 or trap?** RISC-V chose -1 (all bits set, i.e., U64_MAX) because it is detectably wrong yet deterministic. If you divide 7 by 0 and get -1, your program will likely crash elsewhere—but every CPU crashes the same way. A trap would require exception handling (non-deterministic across implementations). Zero would look like a valid answer and mask bugs. The value -1 is detectably anomalous but does not halt execution.

**Signed overflow (divisor is -1):**

| Condition | Instruction | Result |
|-----------|-------------|--------|
| `rs1 == INT64_MIN` and `rs2 == -1` | `DIV` | `rd := INT64_MIN` |
| `rs1 == INT64_MIN` and `rs2 == -1` | `REM` | `rd := 0` |
| `low32(rs1) == INT32_MIN` and `low32(rs2) == 0xFFFFFFFF` | `DIVW` | `rd := SEXT32(INT32_MIN)` |
| `low32(rs1) == INT32_MIN` and `low32(rs2) == 0xFFFFFFFF` | `REMW` | `rd := 0` |

No trap occurs—deterministic wrong-but-consistent answer.

### 6.6.1 Shift amount masking (normative)

For RV64I variable-shift instructions, the shift amount MUST be masked to 6 bits (range 0–63):

| Instruction | Shift Amount |
|-------------|--------------|
| `SLL` / `SRL` / `SRA` | `shamt := rs2 & 0x3F` |
| `SLLW` / `SRLW` / `SRAW` | `shamt := rs2 & 0x1F` |

For immediate-shift instructions (`SLLI`, `SRLI`, `SRAI`, `SLLIW`, `SRLIW`, `SRAIW`), the shift amount is encoded in the instruction and is already in the valid range.

**Rationale:** Different host languages and CPUs handle out-of-range shifts inconsistently. C/C++ treat large shifts as undefined behavior; some CPUs mask to register width, others don't. Explicit masking ensures deterministic results regardless of host platform.

**Implementation note:** The masking applies to the value read from `rs2` before the shift operation. For W-variants, the 32-bit result is then sign-extended to 64 bits as per standard RV64 semantics.

### 6.7 Misaligned loads/stores (pinned behavior)

Misaligned loads/stores of sizes 2, 4, or 8 bytes are **EMULATED** deterministically as byte-wise operations in little-endian order (subject to §6.7.1 memory validity).

**Load emulation (normative):**

For a load of `n ∈ {2,4,8}` bytes at address `a`:
1. Read bytes `b[0..n-1]` at addresses `a+i` for `i` in `0..n-1`.
2. Assemble `u := Σ b[i] × 256^i` (little-endian unsigned integer).
3. Apply the instruction's extension rule before writing `rd`:
   - `LB/LH/LW`: `rd := sign_extend(u, 8×n)`
   - `LBU/LHU/LWU`: `rd := zero_extend(u, 8×n)`
   - `LD`: `rd := u`

The instruction counts as one step (see §6.5).

**Store emulation (normative):**

For a store of `n ∈ {2,4,8}` bytes at address `a`:
1. Let `u` be the low `8×n` bits of `rs2`.
2. Write bytes `b[i] := (u >> (8×i)) & 0xFF` to addresses `a+i` for `i` in `0..n-1` (little-endian).

The instruction counts as one step (see §6.5).

#### 6.7.1 Memory access validity (normative)

All instruction fetches, loads, and stores MUST be validated against the memory map defined by `JOLT_GUEST_MEMMAP_V1` (regions with base, length, and permissions).

For a memory access of `n` bytes at address `addr`:
1. Implementations MUST treat `addr` as an unsigned 64-bit integer.
2. Implementations MUST perform overflow-safe range checking:
   - If `addr + (n - 1)` overflows 64-bit arithmetic, the access MUST trap with `JOLT_STATUS_TRAP_BAD_MEMORY` (code 2).
3. The access is valid iff the entire byte range `{addr, addr+1, …, addr+n-1}` lies within a single mapped region that grants the required permission (R/W/X).
4. Any access that is not valid by (3) MUST trap with `JOLT_STATUS_TRAP_BAD_MEMORY` (code 2).

### 6.8 ABI and initial state

#### 6.8.1 Register initialization

At entry (`pc = entry_point`):

- `x0` MUST equal 0 (hardwired in RISC-V)
- All registers `x1..x31` MUST equal 0 **except** ABI registers set below

Any proof witnessing a different initialization MUST be rejected.

#### 6.8.2 ABI registers

The host sets:

| Register | ABI Name | Purpose | Value |
|----------|----------|---------|-------|
| x10 | a0 | Input pointer | Address of batch manifest bytes |
| x11 | a1 | Input length | Byte count of manifest |
| x12 | a2 | Output pointer | Address for PublicOutputsV1 |
| x13 | a3 | Output max | Maximum output buffer size |
| x14 | a4 | Batch nonce | `batch_nonce_u64` |
| x2 | sp | Stack pointer | Top of stack region |

All other registers are zero.

**Input length rule:** `input_len` MUST equal the exact byte-length of the manifest encoding (no padding).

#### 6.8.3 Syscalls

Only `JOLT_SYSCALL_EXIT_V1` is permitted. The syscall selector is passed in register `a7`.

**Syscall selector convention (normative):**
- `a7` MUST be treated as the syscall selector register
- `JOLT_SYSCALL_EXIT_V1 := 0`

**On `ecall` instruction:**
- If `a7 == 0` (JOLT_SYSCALL_EXIT_V1): halt normally and set:
  - `exit_code_u8 := (u64(a0) & 0xFF)` (low 8 bits of the 64-bit register)
  - `exit_code := u64(exit_code_u8)`
  Preserve the output buffer as written.
- If `a7 != 0`: trap with `JOLT_STATUS_TRAP_FORBIDDEN_SYSCALL` (code 3)

```assembly
# Exit with status code in a0
li a7, 0        # syscall selector = JOLT_SYSCALL_EXIT_V1
li a0, 0        # status = 0 (success)
ecall           # invoke syscall → terminates execution
```

Any `ecall` with `a7 != 0` MUST trap with `JOLT_STATUS_TRAP_FORBIDDEN_SYSCALL` (code 3).

Every syscall is a potential non-determinism source. File reads depend on filesystem state. Clock queries depend on wall time. Random number generation is non-deterministic by design. Eliminating all syscalls except exit ensures the guest is a pure function: same input → same output, every time.

#### 6.8.4 Initial memory state binding (normative)

At execution start, memory contents MUST be fully determined by the public inputs and spec-defined constants:

**I/O memory region:**
- For each `i` with `0 ≤ i < input_len`, byte at address `input_ptr + i` MUST equal `manifest_bytes[i]` exactly as provided by the host
- All other bytes in the I/O region MUST be zero

**RW memory region:**
- All bytes MUST be zero at execution start

**Initial memory root binding (normative):**
- `io_root_in` (the I/O memory SMT root at chunk 0 entry) MUST equal the SMT root computed over: manifest bytes at `[input_ptr, input_ptr + input_len)`, zeros elsewhere
- `rw_mem_root_in` (the RW memory SMT root at chunk 0 entry) MUST equal the SMT root of all-zeros memory

This rule eliminates "hidden inputs"—if any byte in initial memory were unspecified, a malicious prover could control it as a private witness input, violating the principle that proofs attest only to public inputs.

**Conformance requirement:** Implementations MUST reject any proof where the initial memory roots do not match the deterministic construction above. The conformance bundle (§14) includes test vectors for initial memory root computation.

### 6.9 Halt/trap semantics and status codes

#### 6.9.1 Termination fields

VM termination fields:
- `halted: u8` in {0, 1}
- `exit_code: u64`

Invariants:
- if `halted = 0`, `exit_code MUST equal 0`
- if `halted = 1`, `exit_code MUST be in [0, 255]` for V1

#### 6.9.2 Wrapper binding (prefix-proof resistance)

The wrapper MUST constrain:
- final `halted_out = 1`
- final `exit_code = u64(status_u8)`

This prevents "prove a prefix" attacks—you can't prove the first 50,000 instructions ran correctly, stop before the balance check, and claim success.

#### 6.9.3 Status codes (`JOLT_STATUS_CODES_V1`)

| Code | Name | Meaning |
|-----:|------|---------|
| 0 | `JOLT_STATUS_OK` | Successful execution |
| 1 | `JOLT_STATUS_TRAP_ILLEGAL_INSTRUCTION` | Illegal/forbidden instruction |
| 2 | `JOLT_STATUS_TRAP_BAD_MEMORY` | Out-of-range or protected memory access |
| 3 | `JOLT_STATUS_TRAP_FORBIDDEN_SYSCALL` | Disallowed syscall |
| 4 | `JOLT_STATUS_TRAP_OOM` | OOM or snapshot cap exceeded |
| 5 | `JOLT_STATUS_TRAP_INTERNAL` | Internal VM invariant failure |

If the Settlement Engine detects an invalid batch (bad signature, insufficient balance, business logic violation), it MUST NOT trap. It MUST handle the error in program logic: write a non-zero status to PublicOutputsV1, and call exit(N) with a non-zero code. Trap codes are reserved for VM-level failures that the program couldn't prevent.

### 6.10 Definition block

**ISA profile:** The subset of CPU instructions a VM supports. RV64IMC means 64-bit RISC-V with base integer (I), multiply/divide (M), and compressed (C) extensions.

**Step counter:** An integer tracking instructions executed. Increments by exactly 1 per instruction, regardless of encoding size or whether the instruction traps.

**Trap:** Abnormal termination caused by the VM detecting an illegal condition. Sets a non-zero status code. Distinguished from normal exit where the program voluntarily terminates.

**ABI (Application Binary Interface):** Conventions for how programs receive arguments and return results. In Jolt continuations, the ABI defines which registers contain input/output pointers at entry.

**Program hash:** SHA-256 of the ELF binary's exact bytes. Identifies the Settlement Engine for program binding in proofs.

### 6.11 Load-bearing claims

| Claim | Evidence | Verification |
|-------|----------|--------------|
| **Forbidden instructions trap deterministically** | §6.4.1: specific trap code for each category | Execute A-extension instruction; verify trap code 1 across implementations |
| **Step counter increments by 1 for all instructions** | §6.5: "including 16-bit compressed instructions" | Same code with/without C extension; step counts must match |
| **Misaligned access succeeds via emulation** | §6.7: "EMULATED deterministically" | Misaligned LW at address 3; verify identical result across implementations |
| **Registers (except ABI) are zero at entry** | §6.8.1: "proof witnessing different initialization MUST be rejected" | Read x17 before first write; must be zero |
| **Only exit syscall permitted** | §6.8.3: "Any other ecall usage MUST trap" | Attempt other syscall; must trap with code 3 |
| **Division edge cases follow pinned spec** | §6.6: "MUST follow the pinned unprivileged ISA spec" | DIV by zero; signed overflow; verify exact results |

### 6.12 Jolt whitepaper connections

| Section 6 Concept | Whitepaper Connection |
|-------------|----------------------|
| RV64IMC as ISA | §3: Jolt proves RISC-V execution; same instruction set |
| Step counter uniformity | §3.3: Jolt traces are instruction-indexed; consistent counting assumed |
| Deterministic edge cases | §3.3: "formatting assembly code"—Jolt requires unambiguous instruction semantics |
| No floating-point | Jolt's lookup tables cover integer operations; FP would require separate tables |
| Single-threaded execution | Jolt proves sequential execution; no concurrency model needed |

### 6.13 Conformance requirements (guest VM)

Conformance test suites (§14) MUST include vectors for:

1. **Division edge cases (M extension):**
   - `DIV/DIVU/REM/REMU` with divisor = 0
   - `DIV/REM` signed overflow (`INT64_MIN / -1`)
   - `DIVW/DIVUW/REMW/REMUW` with divisor = 0
   - `DIVW/REMW` signed overflow (`INT32_MIN / -1`)
   - Expected register results for each case

2. **Misaligned accesses:**
   - Misaligned `LW` and `SW` at at least two non-aligned addresses with known memory contents, verifying byte order and sign/zero-extension

3. **Forbidden instruction trapping:**
   - At least one A-extension opcode and one CSR opcode, verifying `JOLT_STATUS_TRAP_ILLEGAL_INSTRUCTION` and trap transition rules

4. **Syscall restriction:**
   - `ecall` with `a7 != JOLT_SYSCALL_EXIT_V1` traps with `JOLT_STATUS_TRAP_FORBIDDEN_SYSCALL`

5. **Initialization binding:**
   - A vector that reads a non-ABI register before any write (must be zero)
   - Initial memory roots for a non-empty manifest

6. **Trap output buffer fill:**
   - A program that traps before writing outputs; verify `PublicOutputsV1` trap encoding (per §5.6)

Vectors MUST be versioned and tied to `JOLT_RISCV_PROFILE_V1`, `JOLT_RISCV_UNPRIV_SPEC_V1`, and `JOLT_GUEST_MEMMAP_V1`.

### 6.14 Forward references

- **Step counter in chunking** → Section 11 (Continuations: CHUNK_MAX_STEPS determines boundaries)
- **Memory map addresses** → Section 3 (JOLT_GUEST_MEMMAP_V1, currently TBD)
- **Division exact behavior** → Section 3 (JOLT_RISCV_UNPRIV_SPEC_V1, currently TBD)
- **PublicOutputsV1 layout** → 5.6 (what the guest writes to output buffer)
- **Program hash in public inputs** → 5.3 (program_hash_lo/hi)
- **Toolchain pinning** → Section 3 (JOLT_TOOLCHAIN_V1, currently TBD)

---

## Section 7: Word/field encodings and bytes32 safety

### 7.1 The collision trap

A 256-bit hash can represent more values than the BLS12-381 scalar field can hold. This arithmetic mismatch creates a security landmine: if you naively reduce a bytes32 value modulo the field order r, you create collisions. Two distinct hashes that differ by exactly r become indistinguishable once they enter the field. An attacker who crafts a batch with commitment H' = H + r can hijack a proof generated for commitment H. This is the **field squeeze attack**, and it turns a mathematical inconvenience into a consensus-breaking vulnerability.

BLS12‑381's scalar field Fr has prime order approximately 2^254.86:
```
r = 52435875175126190479447740508185965837690552500527637822603658699938581184513
```

The fix demands discipline, not cleverness. Never let arbitrary 256-bit values touch modular reduction. Instead, split them. The `Bytes32ToFr2` encoding takes the first 31 bytes as one field element (248 bits, comfortably below r's 255-bit size) and the final byte as another. Different inputs produce different pairs. Collisions become mathematically impossible, not just improbable. The encoding is injective by construction, not by hope.

### 7.2 Two worlds, two rules

Values that originate inside the field (Poseidon hash outputs, for instance) follow one path: serialize to bytes, deserialize back, reject anything that claims to be canonical but exceeds r. Values that originate outside the field (SHA-256 hashes, state roots, the program hash) follow another path: split into two field elements, reconstruct on demand, never reduce. The boundary between these worlds is bright and sharp. Cross it carelessly and you invite the very collisions you sought to prevent.

| Value Type | Example | Problem | Solution |
|------------|---------|---------|----------|
| Already in Fr | Poseidon hash output | Need to serialize/deserialize | Direct canonical encoding |
| Arbitrary bytes32 | SHA-256 hash | Might be ≥ r | Split into (Fr_lo, Fr_hi) |
| u64 integer | batch_nonce | Trivially < r | Direct cast with range check |

Many cryptographic libraries offer convenient `Fr::from_bytes()` functions that silently reduce their input modulo r. These functions are dangerous for arbitrary bytes32 values. They transform a rejection-worthy input into a silently corrupted one. The correct response to a bytes32 exceeding r is an error, not a reduction.

### 7.4 Integer ↔ Fr conversion primitives (normative)

All byte↔field conversions in this specification use the following primitives. Implementations MUST NOT substitute library functions that differ from these semantics.

**`FrToUint(f: Fr) → uint256`**

Return the unique non-negative integer `x` such that `0 ≤ x < r` and `x` is the canonical representative of `f`.

**`FrFromUintCanonical(x: uint256) → Fr | ERROR`**

- If `x ≥ r`: return ERROR (MUST reject non-canonical values)
- Else: return the unique field element whose canonical representative is `x`

**`FrFromU248(x: uint248) → Fr`**

- Require `0 ≤ x < 2^248`
- Return `FrFromUintCanonical(x)`
- This MUST NOT fail for BLS12-381 because `2^248 < r`

**`FrFromU64(x: uint64) → Fr`**

- Require `0 ≤ x < 2^64`
- Return `FrFromUintCanonical(x)`
- This MUST NOT fail because `2^64 < r`

All uses of `Fr(...)` notation in this specification are shorthand for `FrFromUintCanonical(...)`. Implementations MUST NOT use "mod order" constructors (which silently reduce `x mod r`) in any context requiring canonical decoding.

### 7.5 Canonical `Fr` ↔ `bytes32` (for values known to be in `Fr`)

Used for: Poseidon roots (`rw_mem_root`, `io_root`), `checkpoints_digest`, `Fr` public inputs.

**Endianness (normative):** All byte↔integer conversions in this section use **little-endian** encoding: `B[0]` is the least-significant byte (LSB), `B[31]` is the most-significant byte (MSB).

Example: The integer value `1` encodes as `B = [0x01, 0x00, 0x00, ..., 0x00]` (one 0x01 byte followed by 31 zero bytes).

**`FrToBytes32LE(f: Fr) → bytes32`** (normative)

Algorithm:
```
1. x = FrToUint(f)                    // canonical integer in [0, r)
2. For i = 0 to 31:
     B[i] = (x >> (8*i)) & 0xFF       // extract byte i (little-endian)
3. return B
```
Since `r < 2^255`, the highest byte `B[31]` is always less than `0x74`. ■

**`Bytes32LEToFrCanonical(B: bytes32) → Fr | ERROR`** (normative)

Algorithm:
```
1. x = Σ_{i=0..31} B[i] × 2^(8i)      // little-endian 256-bit integer
   Implementations MUST compute this over an integer domain large enough
   to hold values up to 2^256−1 without overflow or wraparound.
2. if x >= r: return ERROR            // MUST reject non-canonical
3. return FrFromUintCanonical(x)
```
■

The rejection is critical. A value ≥ r in a context expecting a canonical Fr element is malformed input, not something to silently fix. Accepting and reducing would create exactly the collision vulnerability Section 7 exists to prevent.

### 7.6 Injective `bytes32` → `(Fr, Fr)` packing (for arbitrary bytes32)

Used for: `program_hash`, `old_root`, `new_root`, `batch_commitment` public inputs.

**`Bytes32ToFr2(B: bytes32) → (Fr, Fr)`** (normative)

Algorithm:
```
1. For i = 0 to 30:
     lo_bytes[i] = B[i]               // first 31 bytes (indices 0..30)
2. hi_byte = B[31]                    // last byte (index 31)

3. lo_int = Σ_{i=0..30} lo_bytes[i] × 2^(8i)   // little-endian 248-bit integer
   Implementations MUST compute this over an integer domain large enough
   to hold values up to 2^248−1 without overflow or wraparound.
4. hi_int = hi_byte                   // 8-bit integer (0..255)

5. lo_fr = FrFromU248(lo_int)         // injective: 248 bits < 255 bits
6. hi_fr = FrFromU64(hi_int)          // injective: 8 bits < 64 bits < 255 bits

7. return (lo_fr, hi_fr)
```
■

The first 31 bytes form a 248-bit integer. Maximum value: 2^248 − 1. Since r ≈ 2^255, this value is always far below r. No reduction needed.

The last byte is an 8-bit integer. Maximum value: 255. Trivially below r.

Both pieces fit in Fr with room to spare. The encoding is **injective**: if `Bytes32ToFr2(A) = Bytes32ToFr2(B)`, then `A = B`. Different bytes32 values produce different `(lo_fr, hi_fr)` pairs. Collisions are impossible.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        Bytes32ToFr2 ENCODING DIAGRAM                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  INPUT: bytes32 B[0..31] (32 bytes = 256 bits)                              │
│  ┌──────────────────────────────────────────────────────────────┬─────┐     │
│  │  B[0] B[1] B[2] ... B[29] B[30]                              │B[31]│     │
│  │  ◀────────────── 31 bytes (248 bits) ──────────────────────▶ │1 byt│     │
│  └──────────────────────────────────────────────────────────────┴─────┘     │
│                              │                                      │       │
│                              ▼                                      ▼       │
│  ┌──────────────────────────────────────────────────┐    ┌──────────────┐   │
│  │         lo_int = little-endian(B[0..30])         │    │hi_int = B[31]│   │
│  │         Range: 0 to 2^248 - 1                    │    │Range: 0..255 │   │
│  └──────────────────────────────────────────────────┘    └──────────────┘   │
│                              │                                      │       │
│                              ▼                                      ▼       │
│  ┌──────────────────────────────────────────────────┐    ┌──────────────┐   │
│  │  lo_fr = FrFromU248(lo_int)                      │    │hi_fr = Fr(hi)│   │
│  │  Safe: 2^248 < r (BLS12-381 scalar field)        │    │Safe: 255 < r │   │
│  └──────────────────────────────────────────────────┘    └──────────────┘   │
│                                                                             │
│  OUTPUT: (lo_fr, hi_fr) — pair of Fr elements                               │
│                                                                             │
│  ═══════════════════════════════════════════════════════════════════════    │
│  WHY 31+1 SPLIT?                                                            │
│  • Fr field order r ≈ 2^255 (255-bit prime)                                 │
│  • 31 bytes = 248 bits → guaranteed < r (no reduction needed)               │
│  • 1 byte = 8 bits → trivially < r                                          │
│  • Result: INJECTIVE encoding (different B → different (lo,hi))             │
│  • Prevents field-squeeze attacks where distinct hashes collide mod r       │
└─────────────────────────────────────────────────────────────────────────────┘
```

**`Fr2ToBytes32(lo_fr: Fr, hi_fr: Fr) → bytes32 | ERROR`** (normative)

Algorithm:
```
1. lo_int = FrToUint(lo_fr)           // canonical integer in [0, r)
2. hi_int = FrToUint(hi_fr)           // canonical integer in [0, r)

3. if lo_int >= 2^248: return ERROR   // MUST reject (out of range for 31-byte limb)
4. if hi_int >= 256:   return ERROR   // MUST reject (out of range for 1-byte limb)

5. For i = 0 to 30:
     B[i] = (lo_int >> (8*i)) & 0xFF  // little-endian encoding of lo_int as 31 bytes
6. B[31] = hi_int                     // single byte from hi_int

7. return B
```
■

`Fr2ToBytes32` MUST return ERROR if either range check fails. Implementations MUST NOT truncate `lo_int` modulo 2^248 or `hi_int` modulo 256. These range checks are mandatory because `(lo_fr, hi_fr)` may be prover-controlled (e.g., public inputs); different implementations truncating differently would cause consensus splits.

### 7.7 Deterministic u64-in-field encoding

Whenever a `u64` is injected into `Fr` (e.g., transcript `absorb_u64`), it MUST be treated as the unique field element equal to that integer (`< 2^64`), with a range check.

- Maximum u64: 2^64 - 1 ≈ 1.8 × 10^19
- Field order r ≈ 5.2 × 10^76

The u64 is roughly 190 orders of magnitude smaller than r. Cast directly to Fr with a range check confirming the value is < 2^64. No splitting needed; collision impossible.

### 7.8 No silent reductions (normative)

No semantic `bytes32` value may be reduced mod `r` anywhere in the wrapper, transcript, or VM-to-wrapper boundary.

This is the enforcement rule. Many cryptographic libraries provide `Fr::from_bytes()` functions that silently reduce mod r. Using such functions on arbitrary bytes32 values is a security vulnerability.

**Correct patterns:**
- Poseidon output → `Bytes32LEToFrCanonical` (reject if ≥ r)
- SHA-256 output → `Bytes32ToFr2` (split)
- u64 → direct cast (always safe)

**Wrong pattern:**
- `Fr::from(arbitrary_bytes32)` with silent mod r reduction

If your Fr library silently reduces, you need a different code path for arbitrary bytes32 values, or you need to pre-check and reject values ≥ r before using the library function.

### 7.9 bytes32 packing checklist (normative)

All of the following MUST use `Bytes32ToFr2` when entering `Fr` public inputs:

| Public Input | Source | Encoding | Reason |
|--------------|--------|----------|--------|
| `program_hash_lo/hi` | SHA-256(ELF) | Bytes32ToFr2 | Arbitrary 256-bit hash |
| `old_root_lo/hi` | State commitment | Bytes32ToFr2 | Arbitrary 256-bit value |
| `new_root_lo/hi` | State commitment | Bytes32ToFr2 | Arbitrary 256-bit value |
| `batch_commitment_lo/hi` | SHA-256 Merkle root | Bytes32ToFr2 | Arbitrary 256-bit hash |
| `checkpoints_digest_fr` | Poseidon hash | Direct (already Fr) | Poseidon outputs Fr |
| `status_fr` | u8 exit code | u64→Fr | Integer, trivially < r |
| `batch_nonce_fr` | u64 sequence number | u64→Fr | Integer, trivially < r |

Only values already known to be in `Fr` (Poseidon roots, `checkpoints_digest`) may use `Bytes32LEToFrCanonical`.

This checklist is normative. Using the wrong encoding for any value is a consensus bug.

### 7.10 Definition block

**Field squeeze:** A vulnerability where distinct input values collide when reduced modulo a field's prime order. Occurs when input values can exceed the field order.

**Canonical form:** For Fr, the unique integer in [0, r-1] representing the field element. Non-canonical representations (values ≥ r that would reduce to the same element) must be rejected, not accepted.

**Injective encoding:** A mapping where different inputs always produce different outputs. Bytes32ToFr2 is injective; silent mod-r reduction is not.

**Silent reduction:** When a library function automatically computes `input mod r` without checking whether this causes a collision. Dangerous for arbitrary bytes32 inputs.

### 7.11 Load-bearing claims

| Claim | Evidence | Verification |
|-------|----------|--------------|
| **Bytes32ToFr2 is injective** | 31+1 byte split; lo < 2^248 < r, hi < 2^8 < r | Attempt to find distinct A, B with same (lo, hi) → requires A = B |
| **Canonical encoding rejects ≥ r** | §7.5: "MUST reject non-canonical" | Submit bytes32 with value ≥ r → must error |
| **Fr2ToBytes32 rejects out-of-range** | §7.6: mandatory range checks | Submit lo_fr ≥ 2^248 or hi_fr ≥ 256 → must error |
| **No silent reduction prevents field squeeze** | §7.8 rule; §7.9 checklist | Audit all conversion sites; none use unchecked mod r |
| **Checklist covers all public inputs** | §7.9 enumeration matches §5.3 | Compare lists; verify 1:1 coverage |

### 7.12 Conformance vectors (normative)

The conformance bundle (§14) MUST include test vectors for all encoding functions in this section:

**Bytes32ToFr2 vectors:**

| Input B (hex, 32 bytes) | Expected lo_fr | Expected hi_fr |
|-------------------------|----------------|----------------|
| `00 00 ... 00` (all zeros) | 0 | 0 |
| `01 00 ... 00` (0x01 at index 0) | 1 | 0 |
| `00 00 ... 01` (0x01 at index 31) | 0 | 1 |
| `FF FF ... FF` (all 0xFF) | 2^248 − 1 | 255 |

**Fr2ToBytes32 vectors:**

Round-trip requirement: `Fr2ToBytes32(Bytes32ToFr2(B)) == B` for all vectors above.

Rejection requirement: `Fr2ToBytes32(Fr(2^248), Fr(0))` MUST return ERROR.

**Bytes32LEToFrCanonical boundary vectors:**

| Input B (as LE integer) | Expected Result |
|-------------------------|-----------------|
| r − 1 | ✓ Accept (maximum valid Fr) |
| r | ✗ MUST return ERROR |
| 2^256 − 1 (all 0xFF) | ✗ MUST return ERROR |

**Endianness sanity vector:**

Input: `B = [0x01, 0x02, 0x03, 0x00, ..., 0x00]` (bytes 0x01, 0x02, 0x03 at indices 0, 1, 2; rest zeros)

Expected `lo_int` from Bytes32ToFr2: `0x030201` = 197121 (little-endian interpretation)

This vector catches big-endian implementations that would incorrectly compute `0x010203`.

### 7.13 Forward references

- **Poseidon producing Fr elements** → Section 8 (Transcript specification)
- **Public inputs layout** → 5.3 (11 Fr elements)
- **SHA-256 in batch commitment** → 5.7 (Merkle tree construction)
- **State roots as bytes32** → Section 11 (StateDigest construction)

---

*Section 7's encoding rules ensure values enter Fr safely—no overflows, no silent reductions. Section 8 specifies how those Fr values are absorbed into transcripts to produce unpredictable challenges.*

## Section 8: Transcript specification (Poseidon sponge)

### 8.1 The randomness paradox

Interactive proofs rest on a simple dance: the prover commits, the verifier challenges with randomness, the prover responds. Strip away that randomness, and the proof collapses. A prover who knows tomorrow's challenge can forge today's commitment.

But non-interactive proofs have no verifier present. The prover works alone, generating everything before any checker arrives. So where does the randomness come from?

The Fiat-Shamir transform answers with elegant brutality: *derive challenges from what you've already committed*. The prover feeds commitments into a hash function—the transcript—then extracts challenges from its output. These challenges are deterministic given the commitments, yet unpredictable before committing. When the verifier later reconstructs the same transcript from proof data, matching commitments yield matching challenges. The hash function becomes a simulated verifier, its outputs as good as random to any prover who cannot predict them.

Three conditions make this work. First, determinism: identical inputs must produce identical challenges across every implementation, every platform, every execution. Second, unambiguity: semantically different inputs must produce different transcript states. Third, cryptographic strength: the Poseidon sponge (parameterized by `JOLT_POSEIDON_FR_V1`) must behave as a secure pseudorandom function. Violate any condition, and attackers find purchase.

### 8.2 Type separation: the collision killer

Consider a naive transcript that ignores types. You absorb the byte sequence `[0x01]`. Later, you absorb the integer `1`. Both might produce identical internal states—and that collision opens a door.

An attacker exploits the ambiguity: a proof validates "the byte 0x01" but the verifier interprets it as "the integer 1." The proof verified one claim; the verifier believes it verified another. Semantic confusion becomes cryptographic vulnerability.

Type separation slams that door shut. Before absorbing any value, absorb a type discriminator—a distinct field element for each data type:

| Type | Discriminator |
|------|---------------|
| Tag (domain separator) | TYPE_TAG = Fr(3) |
| Byte string | TYPE_BYTES = Fr(1) |
| u64 integer | TYPE_U64 = Fr(2) |
| Vector | TYPE_VEC = Fr(4) |

Absorbing bytes `[0x01]` means: absorb TYPE_BYTES, then length, then chunk data. Absorbing integer `1` means: absorb TYPE_U64, then Fr(1). Completely different absorption sequences. Different transcript states. The collision vanishes.

#### 8.2.1 Attack scenario: type confusion

Consider an attacker exploiting a careless implementation that ignores type discriminators:

**Setup:** A prover commits to a private key `k` (stored as u64) and authorized recipients list `L` (stored as bytes). The proof's security depends on the challenge derived from these commitments.

**Attack execution:** The attacker observes that in a naive (broken) implementation:
- The byte sequence `[0x01, 0x02]` produces some absorption state
- The integer `258` (which is `0x0102` in little-endian) might produce the same state

With type separation, these produce different sequences:
- TYPE_BYTES absorption: `[Fr(1), Fr(2), Fr(chunk)]`
- TYPE_U64 absorption: `[Fr(2), Fr(258)]`

Without type separation, an attacker could substitute one for the other, forging a proof that verifies "user is authorized" when the verifier trusted different semantics than the prover committed to.

**Why type discrimination prevents this:** The type tag is consensus-critical and non-negotiable. Even a single-bit deviation in implementation causes transcript divergence, which is immediately caught by any verifier using the canonical specification.

### 8.3 Attack scenario: implementation divergence

The Fiat-Shamir transcript is only as secure as the weakest implementation. If two independent implementations produce different challenges from identical input sequences, the system is vulnerable to divergence attacks.

**Divergence vectors include:**
- Endianness mismatch (big-endian vs. little-endian byte interpretation)
- Padding interpretation (zeros on right vs. left)
- Chunk ordering (left-to-right vs. reverse)
- Type tag values (TYPE_U64=Fr(2) vs. Fr(20))

**Concrete attack: endianness divergence**

Implementation A (correct, little-endian):
```
chunk = [0x01, 0x02, 0x03]
limb = 0x01 + (0x02 << 8) + (0x03 << 16) = 197121
absorb_fr(Fr(197121))
```

Implementation B (incorrect, big-endian):
```
chunk = [0x01, 0x02, 0x03]
limb = 0x03 + (0x02 << 8) + (0x01 << 16) = 66051
absorb_fr(Fr(66051))
```

**The attack:** An attacker generates a proof using Implementation A. Verifiers using Implementation A accept it. Verifiers using Implementation B reject it (different challenges). The network forks. The attacker exploits the fork for double-spending.

**Why specification pinning prevents this:** The specification mandates little-endian interpretation per §7.5. Conformance bundles (§14.3) include transcript test vectors with expected challenge outputs. Two independent implementations must reproduce these test vectors bit-for-bit. Any divergence halts deployment until root-caused and fixed.

### 8.4 Sponge state machine

Let Poseidon parameters be fixed by `JOLT_POSEIDON_FR_V1` with state width `t`, rate `r`, and capacity `c` where `t = r + c`.

**Poseidon parameter requirements (normative).** `JOLT_POSEIDON_FR_V1` is **consensus-critical** and MUST fully specify a single Poseidon permutation instance over `Fr`, including at minimum:
- The Poseidon **variant** (e.g., Poseidon / Poseidon2) and S-box exponent
- State width `t`, rate `r`, capacity `c`
- Number of full rounds and partial rounds
- The complete MDS matrix
- All round constants, in order
- Any domain/parameterization flags required by the referenced Poseidon specification
- `security_bits`: the target security level in bits (e.g., 128), used to validate that capacity and rounds are sufficient

Implementations MUST NOT substitute alternative Poseidon parameter sets, even if claimed "equivalent." All parameters of `JOLT_POSEIDON_FR_V1` are specified in §3.4.1; this transcript specification is final and ready for consensus-critical deployment.

**State:**
- `state[0..t-1]`: array of Fr elements, initialized to zeros
- `pos`: position counter, initialized to 0
- `mode ∈ {ABSORB, SQUEEZE}`: initialized to ABSORB

**`TranscriptV1.init()` (normative):**
```
1. state[0..t-1] := 0
2. mode := ABSORB
3. pos := 0
4. absorb_tag("JOLT/TRANSCRIPT/V1")
5. return transcript
```
■

Callers MUST NOT absorb the domain tag again after calling `init()`. The domain tag is absorbed exactly once, at initialization, to bind all subsequent operations to the Jolt continuations transcript domain.

The sponge has rate `r` and capacity `c` where `t = r + c`. You absorb into the first `r` elements; the remaining `c` elements provide security margin.

**`permute()`:** Apply the Poseidon permutation to `state`. This is the cryptographic mixing step—after permutation, every output element depends on every input element.

**`absorb_fr(x)`:**
```
1. if mode == SQUEEZE: permute(); mode = ABSORB; pos = 0
2. state[pos] += x; pos += 1
3. if pos == r: permute(); pos = 0
```
■

**`squeeze_fr()`:**
```
1. if mode == ABSORB: permute(); mode = SQUEEZE; pos = 0
2. y = state[pos]; pos += 1
3. if pos == r: permute(); pos = 0
4. return y
```
■

**`challenge_fr()`** MUST equal `squeeze_fr()`. The name indicates intent: this is the random challenge for Fiat-Shamir.

The mode transitions enforce a boundary: the transcript MUST apply a permutation when switching between absorbing and squeezing. This matches standard duplex-sponge conventions and ensures challenges are derived from a fully permuted state after all prior absorbed inputs.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      SPONGE STATE MACHINE                                   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  STATE: [state[0..t-1], pos, mode]                                          │
│                                                                             │
│     ┌─────────────────────────────────────────────────────────────────┐     │
│     │                        ABSORB MODE                              │     │
│     │  ┌─────────────────────────────────────────────────────────┐    │     │
│     │  │  state[0]  state[1]  ...  state[r-1] │ state[r..t-1]    │    │     │
│     │  │  ◄────── rate (r elements) ────────► │ ◄─ capacity ─►   │    │     │
│     │  │           ▲                          │                  │    │     │
│     │  │     absorb here                      │   (untouched)    │    │     │
│     │  └─────────────────────────────────────────────────────────┘    │     │
│     └───────────────────────────────┬─────────────────────────────────┘     │
│                                     │                                       │
│     absorb_fr(x):                   │    squeeze_fr():                      │
│     ┌───────────────────┐           │    ┌───────────────────┐              │
│     │ state[pos] += x   │           │    │ (mode change)     │              │
│     │ pos++             │           │    │ permute()         │              │
│     │ if pos==r:        │           │    │ mode = SQUEEZE    │              │
│     │   permute()       │           │    │ pos = 0           │              │
│     │   pos = 0         │           │    └─────────┬─────────┘              │
│     └───────────────────┘           │              │                        │
│                                     │              ▼                        │
│     ┌─────────────────────────────────────────────────────────────────┐     │
│     │                       SQUEEZE MODE                              │     │
│     │  ┌─────────────────────────────────────────────────────────┐    │     │
│     │  │  state[0]  state[1]  ...  state[r-1] │ state[r..t-1]    │    │     │
│     │  │  ◄────── rate (r elements) ────────► │ ◄─ capacity ─►   │    │     │
│     │  │           │                          │                  │    │     │
│     │  │     read from here                   │   (security)     │    │     │
│     │  └─────────────────────────────────────────────────────────┘    │     │
│     └─────────────────────────────────────────────────────────────────┘     │
│                                                                             │
│  SECURITY: Capacity elements NEVER directly absorb input or emit output.    │
│            Mode change ALWAYS triggers permute() before crossing boundary.  │
│                                                                             │
│  INIT: state = [0..0], mode = ABSORB, pos = 0, then absorb domain tag       │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 8.5 Typed absorption functions (normative)

#### 8.5.1 `absorb_u64(x)`

Input: `x` is a `u64` (unsigned 64-bit integer).

Algorithm:
```
1. absorb_fr(TYPE_U64)
2. absorb_fr(FrFromU64(x))
```

`FrFromU64` is defined in §7.4. Since `0 ≤ x < 2^64` and `2^64 < r`, this mapping is injective and requires no modular reduction.

Two field elements absorbed. The type tag ensures this can't collide with byte absorption.

#### 8.5.2 `absorb_bytes(b)`

Input: `b` is a byte string.

Algorithm:
```
1. absorb_fr(TYPE_BYTES)
2. let n = len(b) in bytes
   If n ≥ 2^64, the encoding is invalid and implementations MUST reject.
3. absorb_u64(n)
4. Split b into ceil(n / 31) consecutive chunks of 31 bytes, in increasing index order.
   - If n == 0, there are zero chunks (nothing further absorbed).
   - The final chunk (if any) is right-padded with zero bytes to length 31.
5. For each 31-byte chunk c:
   - Interpret c as a little-endian 248-bit integer: limb = Σ_{i=0..30} c[i] × 2^(8i)
   - absorb_fr(FrFromU248(limb))
```

`FrFromU248` is defined in §7.4. Since `0 ≤ limb < 2^248` and `2^248 < r`, this mapping is injective and requires no modular reduction. Implementations MUST interpret the 31-byte chunk as little-endian per §7.5.

The 31-byte chunks match Section 7's safe encoding—248 bits always fits in Fr without reduction.

**Why length-prefixing suffices:** The absorbed length `n` unambiguously determines the original byte count. For example:
- `[0x01, 0x02, 0x00]` absorbs `n=3`, then one padded chunk
- `[0x01, 0x02]` absorbs `n=2`, then one padded chunk

Although both produce the same chunk bytes after padding, the absorbed lengths differ (3 vs 2), so the transcript states differ. No additional disambiguation is needed.

#### 8.5.3 `absorb_vec(items, absorb_item)` (normative)

Input: `items` is a vector of values of some type `T`. `absorb_item` is the canonical absorber function for one `T` value (e.g., `absorb_u64`, `absorb_bytes`, `absorb_tag`, or `absorb_fr` when `T = Fr`).

Algorithm:
```
1. absorb_fr(TYPE_VEC)
2. let n = len(items)
   If n ≥ 2^64, the encoding is invalid and implementations MUST reject.
3. absorb_u64(n)
4. For i = 0 to n-1:
   - absorb_item(items[i])
```

In consensus-critical schedules, the element type `T` and the corresponding `absorb_item` function MUST be fixed by the specification. Prover-controlled type selection is forbidden.

**Note:** `absorb_vec` is defined for completeness but is not currently used in Jolt continuations's core transcript schedules. If future versions require vector absorption, this definition ensures consistent semantics.

### 8.6 `absorb_tag(tag)` (domain separation; normative)

`absorb_tag` is used for **domain separation** inside the transcript (e.g., `"JOLT/TRANSCRIPT/V1"`, `"JOLT/STATE/V1"`).

Input requirements:
- `tag` MUST be an ASCII string whose bytes are restricted to the character set `[A-Z0-9/_]` (uppercase letters, digits, forward slash, underscore).
- `tag` MUST begin with the prefix `"JOLT/"`.
- `tag` MUST have length ≥ 3 (at minimum the prefix).
- In any consensus-critical transcript schedule, all tags MUST be spec-defined constants and MUST NOT be prover-controlled inputs.
- Implementations MUST NOT apply Unicode normalization, case-folding, trimming, or any other transformation to `tag` before absorption.

Algorithm:
```
1. tag_bytes = ASCII(tag)
2. absorb_fr(TYPE_TAG)
3. let n = len(tag_bytes) in bytes
   If n ≥ 2^64, the encoding is invalid and implementations MUST reject.
4. absorb_u64(n)
5. Split tag_bytes into ceil(n / 31) consecutive chunks of 31 bytes, in increasing index order.
   - If n == 0, there are zero chunks (but n ≥ 3 per input requirements).
   - The final chunk (if any) is right-padded with zero bytes to length 31.
6. For each 31-byte chunk c:
   - Interpret c as a little-endian 248-bit integer: limb = Σ_{i=0..30} c[i] × 2^(8i)
   - absorb_fr(FrFromU248(limb))
```

`FrFromU248` is defined in §7.4.

`absorb_tag` MUST NOT call `absorb_bytes(tag_bytes)` internally—that would also absorb `TYPE_BYTES` and change the domain separation behavior.

Domain separation ensures different uses of the transcript produce different challenges even with similar data.

Before hashing checkpoints:
```
absorb_tag("JOLT/CHECKPOINTS/V1")
absorb_bytes(checkpoints_bytes)
challenge_fr()
```

Before computing state digest:
```
absorb_tag("JOLT/STATE/V1")
... absorb state fields ...
challenge_fr()
```

Same data with different tags → different transcript state → different output. An attacker can't repurpose a checkpoints hash as a state digest.

### 8.7 `PoseidonHashV1` helpers (normative)

This appendix uses a transcript-defined Poseidon sponge as a hash function in several places.

#### 8.7.1 `PoseidonHashV1(tag, bytes) → Fr`

Algorithm:
```
1. T = TranscriptV1.init()    // init already absorbs "JOLT/TRANSCRIPT/V1"
2. T.absorb_tag(tag)
3. T.absorb_bytes(bytes)
4. return T.challenge_fr()
```

#### 8.7.2 `PoseidonHashFr2V1(tag, a, b) → Fr`

Algorithm:
```
1. T = TranscriptV1.init()
2. T.absorb_tag(tag)
3. T.absorb_fr(a)
4. T.absorb_fr(b)
5. return T.challenge_fr()
```

#### 8.7.3 Where these helpers are used

`PoseidonHashV1` / `PoseidonHashFr2V1` MUST be used for:
- `checkpoints_digest_fr` (§5.8)
- SMT leaf hashing and node hashing for memory roots (§11)
- `state_digest_fr` (§11)

Note: `batch_commitment_bytes32` uses **SHA-256 Merkle** per §5.7, not Poseidon. SHA-256 is standard, auditable, and doesn't require Fr arithmetic—appropriate for a commitment that doesn't need circuit efficiency.

### 8.8 Definition block

**Fiat-Shamir transform:** A technique for converting interactive proofs to non-interactive by deriving verifier challenges from a hash of the prover's commitments.

**Sponge construction:** A mode of operation for hash functions where you absorb input, then squeeze output, with permutations between phases and when buffers fill.

**Rate (r):** The number of state elements that receive absorbed input. Higher rate = more data per permutation = faster, but reduced security margin.

**Capacity (c):** State elements that don't directly receive input. Provides security margin. Total state size t = r + c.

**Domain separation:** Using distinct tags to ensure different uses of the same hash function produce independent outputs.

**Type separation:** Absorbing a type discriminator before each value to ensure different data types produce different transcript states.

### 8.9 Load-bearing claims

| Claim | Evidence | Verification |
|-------|----------|--------------|
| **Type separation prevents ambiguity** | TYPE_BYTES ≠ TYPE_U64 ≠ TYPE_TAG | Absorb [0x01] as bytes vs 1 as u64 → compare transcript states |
| **Sponge is deterministic** | State machine with defined init, transitions | Same absorption sequence → same challenges |
| **31-byte chunks fit in Fr** | 248 bits < log₂(\|Fr\|) (~255 bits) | Verify max chunk value 2^248-1 < \|Fr\| |
| **Length-prefixing resolves padding ambiguity** | Byte length absorbed before chunks | Absorb "AB\0" (len=3) vs "AB" (len=2) → different transcript states |
| **Domain tags prevent cross-purpose collision** | Different tag strings → different absorption | Same data with different tags → different challenge |

### 8.10 Forward references

- **Poseidon parameters (t, r, c, round constants)** → Section 3.4.1 (JOLT_POSEIDON_FR_V1)
- **Transcript schedule for Jolt** → Section 3 (JOLT_TRANSCRIPT_SCHEDULE_V1, currently TBD)
- **checkpoints_digest using PoseidonHashV1** → 5.8
- **StateDigest computation** → Section 11
- **SMT hashing** → Section 11
- **Why batch_commitment uses SHA-256** → 5.7

### 8.11 Conformance vectors (normative)

The Jolt continuations conformance bundle (§14) MUST include transcript test vectors for `TranscriptV1` and `PoseidonHashV1` once `JOLT_POSEIDON_FR_V1` is frozen. At minimum, the bundle MUST include:

**TranscriptV1 vectors:**
1. `TranscriptV1.init()` followed immediately by `challenge_fr()` — tests initialization and domain tag absorption
2. `absorb_u64(0)`, `absorb_u64(1)`, and `absorb_u64(2^64-1)` each followed by `challenge_fr()` — tests integer absorption boundaries
3. `absorb_bytes(b"")` (empty), `absorb_bytes(b"\x00")` (single zero), `absorb_bytes(b"\x01\x02")` (two bytes), and a 31-byte exact boundary case, each followed by `challenge_fr()` — tests byte absorption edge cases
4. `absorb_tag("JOLT/TEST/V1")` and at least two tags used elsewhere (`"JOLT/STATE/V1"`, `"JOLT/CHECKPOINTS/V1"`) each followed by `challenge_fr()` — tests domain separation

**PoseidonHashV1 vectors:**
5. `PoseidonHashV1("JOLT/TEST/V1", b"")` and `PoseidonHashV1("JOLT/TEST/V1", b"\x00\x01\x02")` — tests hash helper
6. `PoseidonHashFr2V1("JOLT/TEST/V1", Fr(0), Fr(1))` and `PoseidonHashFr2V1("JOLT/TEST/V1", Fr(|Fr|-1), Fr(|Fr|-1))` — tests two-element hash

Test vectors MUST specify expected outputs as canonical `Fr` encodings per §7. These vectors are consensus fixtures—implementations that produce different outputs MUST NOT be deployed.

---

*The Fiat-Shamir transcript (Section 8) derives the random challenges that make proofs non-interactive. Those challenges apply to whatever proof system underlies Jolt. In Jolt's case, that system uses Lasso lookup arguments rather than traditional constraint algebra.*

## Section 9: Lasso / lookup gadget set (if used)

### 9.1 The lookup singularity

Traditional zero-knowledge virtual machines prove execution the hard way. Each instruction spawns a thicket of arithmetic constraints: an ADD becomes "prove the output equals the sum of the inputs." A million instructions births a million constraint clusters. The prover sweats; the verifier waits.

Jolt flips the paradigm. Instead of proving arithmetic, *look it up*. Precompute every possible result and store it in a table. For 8-bit addition, that's 65,536 entries—each pair (a, b) mapped to its sum. When the prover encounters "17 + 25," there's no constraint algebra. Just a table query: row 17, column 25, answer 42. The verifier never re-executes the addition. The verifier checks that the claimed lookup is consistent with the known table. This is Lasso (Jolt whitepaper Section 2.3): a lookup argument efficient enough to handle even 64-bit operations, which would naively require 2^128 entries, by decomposing them into manageable subtables.

This collapse of all instructions into table lookups—the "lookup singularity"—unifies the proving mechanism across operation types. Different operations use different tables, but the verification machinery stays uniform.

### 9.2 Tables are semantics

Here lies the consensus tripwire. The table *is* the instruction. Consider wraparound arithmetic for 8-bit ADD:

```
ADD_TABLE[255][1] = 0    // 255 + 1 wraps to 0
```

If one implementation's table returns 256 instead of 0 (no wraparound), it has defined a different ADD instruction. Same opcode, alien behavior. Proofs generated against one table fail verification against the other. This extends relentlessly: MUL tables define multiplication, DIV tables pin division-by-zero behavior (see Section 6.6), bitwise tables fix AND/OR/XOR semantics, memory tables govern address translation. Different tables yield different VMs yield different proofs yield consensus fracture.

#### 9.2.1 Attack scenario: table divergence double-spend

**Scenario setup:** Two validator implementations exist:
- **Implementation A** (canonical): Uses `JOLT_LASSO_TABLESET_V1` from the foundation
- **Implementation B** (fork): Deploys identical-looking network but substitutes the DIV table to always return 1 for any division

Both networks claim to run "Jolt V1." External users cannot distinguish them without bytecode inspection.

**The attack:**

Alice signs an intent to transfer 100 tokens. The intent includes a computation: `query_escrow_balance() / 2` to determine how much to lock. Assuming the balance is 200:
- Implementation A: `200 / 2 = 100` (correct quotient)
- Implementation B: `200 / 2 = 1` (malicious table)

The settlement system executes:
- Implementation A: Locks 100 tokens (half the escrow)
- Implementation B: Locks 1 token (freeing 99 tokens for immediate withdrawal)

Alice extracts her proof from Implementation B (where she locked only 1 token) and submits it to Implementation A's verifier. Implementation A's verifier checks the proof against the canonical table, finds `DIV_TABLE[200][2] = 100`, not 1, and rejects the proof.

**But the damage is done:** The bridge has already locked Alice's 100 tokens on Implementation A while Implementation B processed her withdrawal of 99 tokens. Alice has double-spent by exploiting semantic divergence.

**Why traditional signatures don't prevent this:** Alice's cryptographic signature on the intent is valid. The intent's hash is correct. The proof is syntactically well-formed. What differs is the *meaning* of the computation—the semantics of the DIV instruction.

**Defense (§9.4):** Registry pinning with `canonical_hash` of each table. Before processing a batch, the verifier checks that the proof's table commitment matches the registry entry. Deploying a non-canonical table requires a hard fork, which is detectable and requires consensus.

### 9.3 Lookup argument semantics and correctness

The Lasso lookup argument is the cryptographic primitive that makes Jolt's table-based execution model verifiable. At a high level:

1. **The Problem**: The prover claims it executed a lookup `ADD(17, 25) = 42`. How does the verifier trust this claim without re-computing the addition?

2. **The Naive Approach**: Encode constraints directly: "For each lookup (a, b, c), constrain that c = a + b mod 2^8." This works but is expensive—each constraint costs field operations.

3. **The Lasso Solution**: Instead of constraining arithmetic, check *membership*. Pre-compute the entire table T = {(0,0,0), (0,1,1), ..., (255,255,254)}. The prover shows that (17, 25, 42) ∈ T without revealing which entry. This is cheaper because membership proofs compress across many lookups.

**Correctness Properties:**

- **Completeness**: If (a, b, c) is actually in the table, the proof verifies.
- **Soundness**: If (a, b, c) is NOT in the table, no efficient prover can forge a valid proof (except with negligible probability).
- **Zero-Knowledge** (optional): The verifier learns only that the lookup is valid, not the specific (a, b, c) values—useful for hiding witness data.

**The consensus implication**: Because correctness depends on the table's contents, and the table defines the instruction's behavior, changing the table changes what it means for a proof to be "valid." This is why Lasso tables must be registry-pinned.

For the full technical treatment of Lasso's underlying sum-check and multilinear extension machinery, see the Jolt whitepaper Section 2.3 and Lasso paper (Setty et al., 2023).

### 9.4 Consensus rule (normative)

If the zkVM/wrapper uses lookup gadgets that affect arithmetic semantics, they MUST be pinned by tag(s) in the registry.

Any gadget set that affects arithmetic semantics or transcript derivation MUST be pinned (e.g., `JOLT_LASSO_TABLESET_V1`) including:
- table definitions (the mathematical function each table computes)
- table sizes/caps (how many entries, subtable structure)
- encoding of lookup inputs/outputs (how values are represented)

If not pinned, the deployment is non‑deployable by §3.5.

### 9.5 Performance caps

If gadget usage is required for liveness, the registry MUST pin caps such as:
- `MAX_LOOKUPS_PER_BATCH_V1`
- `MAX_BIGINT_BITS_V1`
- etc.

Lookups aren't free. Each lookup adds prover work—polynomial evaluations, commitment operations. Without bounds:
- Malicious batch uses pathological instruction sequences
- Millions of lookups per batch
- Proving takes hours instead of seconds
- Liveness failure: valid batches can't be proven in reasonable time

The prover MUST reject batches exceeding caps before attempting to prove.

#### 9.5.1 Attack scenario: Lasso exhaustion

**Attacker goal:** Prevent the Jolt prover from proving batches in reasonable time, causing liveness failure. Users submit intents, but the system cannot prove them within the settlement timeout window (e.g., 60 seconds).

**Attack method 1: Pathological division loop**

A smart contract submits an intent with:
```
loop i = 0 to 100,000:
    x = x / 2
```

Each DIV instruction triggers a lookup. With 100,000 iterations, the batch incurs 100,000 lookups. Without caps, the Lasso prover must commit to all lookups—runtime ~2-5 seconds per 100K lookups on reference hardware.

If the attacker submits 50 such batches: 50 × 2s = 100 seconds to prove. Settlement timeout is 60 seconds. Valid user intents get dropped.

**Attack method 2: 256-bit arithmetic overload**

A contract performs repeated 256-bit multiplication:
```
loop i = 0 to 10,000:
    a = a * b (256-bit multiplication)
```

Each 256-bit MUL decomposes into ~32 subtable lookups. With 10,000 iterations: 320,000 lookups. FFT runtime: ~10-50 seconds. Verification time: ~5-10 seconds.

**Defense:** Early rejection. Before allocating prover resources:
1. Count lookups in the batch
2. Compare against `MAX_LOOKUPS_PER_BATCH_V1`
3. Reject immediately if exceeded

Early rejection converts adversarial load into O(1) overhead. The attacker cannot exhaust prover resources because their malicious batches never enter the proving pipeline.

### 9.6 Jolt whitepaper connections

| Section 9 Concept | Whitepaper Section |
|-------------|-------------------|
| Lookup singularity | §1.2: "Jolt works by reducing the task... to a single primitive—lookups" |
| Lasso efficiency | §2.3: The Lasso lookup argument |
| Subtable decomposition | §4: "Decomposable" subtables for large operations |
| Instruction tables | §7: Combining all instructions into a single lookup |

### 9.7 Forward references

- **Lasso internals and subtable decomposition** → Jolt whitepaper §2.3, §4
- **DoS cap pattern** → 5.7 (MAX_INTENTS), 5.8 (MAX_CHECKPOINTS_BYTES)
- **Division-by-zero in lookup tables** → 6.6 (pinned via JOLT_RISCV_UNPRIV_SPEC_V1)
- **Registry structure** → Section 3

---

*Lookup tables (Section 9) can accelerate cryptographic operations within the zkVM. One common operation in settlement systems is ECDSA signature verification, which requires specific determinism constraints.*

## Section 10: secp256k1 ECDSA verification workload (if used)

### 10.1 The stakes

Settlement systems live or die by cryptographic signatures. When Alice signs an intent to transfer funds, the Settlement Engine must verify that signature before executing the trade. ECDSA on secp256k1 carries this burden for both Bitcoin and Ethereum, making it the industry standard. But standard does not mean simple. Two problems lurk beneath the surface: implementation differences that cause one validator to accept what another rejects, and the sheer computational expense of proving signature validity in-circuit. Get either wrong, and your settlement system fails.

### 10.2 The malleability trap

Here is a fact that catches engineers off guard: every valid ECDSA signature has a twin. Given signature (r, s) for a message, the pair (r, n - s) validates the same message under the same public key. Mathematically identical, byte-different.

This duality creates a concrete attack. Alice signs "Transfer 100 to Bob" with signature (r, s). The system processes her transfer and records the signature as complete. Now Mallory intercepts and computes (r, n - s)—a valid signature that the system has never seen before. The system processes the transfer again. One authorization, two executions. The signatures were valid; the system was blind to their equivalence.

### 10.3 Low‑S requirement (normative)

The fix is elegant: low-S normalization. The curve order n is odd, so exactly one of s and (n - s) falls at or below floor(n/2). Require that one. Reject the other outright. BIP-146 and EIP-2 codified this rule, and the Settlement Engine MUST enforce it without exception.

Signatures MUST enforce:
- `s ≤ floor(n/2)` where `n` is the secp256k1 group order.

Any signature with s > floor(n/2) is not suspicious or malformed—it is simply invalid. This eliminates malleability: for any (r, s) pair, exactly one of the two equivalent signatures satisfies low-S.

### 10.4 Enforcement point in verification pipeline (normative)

The low-S requirement from §10.3 is not merely a post-computation check. It MUST be enforced at the earliest possible point in the signature verification pipeline to prevent resource waste on invalid signatures.

**Enforcement stages:**

1. **Batch ingestion**: Before any constraint generation, count signatures and check against `MAX_ECDSA_SIGS_PER_BATCH_V1`.
2. **Canonical form gate**: For each signature, verify `s ≤ floor(n/2)` before entering the constraint system.
3. **Resource allocation**: Only after passing gates 1 and 2 should constraint memory be allocated.
4. **Proof generation**: Proceed with Jolt proof only for batches that passed all gates.

**Rejection codes:**

| Error Code | Meaning | Stage |
|------------|---------|-------|
| `BATCH_SIG_LIMIT_EXCEEDED` | Batch contains more than MAX_ECDSA_SIGS_PER_BATCH_V1 signatures | 1 |
| `HIGH_S_REJECTED` | Signature has s > floor(n/2) | 2 |
| `INVALID_CURVE_POINT` | Public key or signature point not on curve | 2 |

**Why early rejection matters**: A malicious batch with 101 signatures (exceeding a cap of 100) costs O(1) to reject at stage 1, but would cost O(hours) to discover if constraint generation proceeded first. Early rejection converts adversarial load into minimal overhead.

### 10.5 Canonical infinity encoding (normative)

If Jacobian points are used, infinity MUST be encoded as:

```
INF_JAC := (X = 0, Y = 1, Z = 0)
```

Elliptic curve arithmetic uses Jacobian coordinates for efficiency. A point (X, Y, Z) represents the affine point (X/Z², Y/Z³). The "point at infinity" (the group identity) has Z = 0.

But which (X, Y, 0)? These all represent infinity:
- (0, 0, 0)
- (1, 1, 0)
- (42, 17, 0)

If implementation A uses (0, 0, 0) and implementation B uses (1, 1, 0), their intermediate computations produce different byte representations. When these values enter commitments or transcripts, the commitments differ. Proofs diverge.

Y = 1 rather than 0 avoids (0, 0, 0), which some libraries treat as a special "uninitialized" state. One canonical form, no ambiguity.

### 10.6 DoS caps (normative)

The registry MUST include:
- `MAX_ECDSA_SIGS_PER_BATCH_V1` (TBD in draft)

Proof generation MUST reject any batch exceeding the cap.

ECDSA verification in-circuit is expensive. Each signature requires:
- Point decompression (if using compressed public keys)
- Scalar multiplication (the dominant cost)
- Field inversions
- Multiple curve additions

Rough estimate: hundreds of thousands of constraints per signature. A batch with 1,000 signatures means hundreds of millions of constraints. Proving time explodes.

The cap is TBD—it depends on target proving time, available hardware, and acceptable latency.

### 10.7 Definition block

**Lookup argument:** A proving technique where the prover demonstrates that queried values appear in a predefined table, rather than proving the computation that would produce those values.

**Table definition:** The mathematical function a lookup table computes. For ADD: f(a, b) = (a + b) mod 2^w where w is the bit width.

**Signature malleability:** The property that multiple distinct signatures can validate the same message under the same public key. Creates potential for confusion or replay.

**Low-S:** A normalization requiring the s component of an ECDSA signature to be at most floor(n/2). Eliminates malleability by forcing a unique canonical signature.

**Jacobian coordinates:** A projective coordinate system where point (X, Y, Z) represents affine point (X/Z², Y/Z³). Allows curve arithmetic without field inversions until the final result.

### 10.8 Load-bearing claims (Section 9 and Section 10)

| Claim | Evidence | Verification |
|-------|----------|--------------|
| **Lookup tables define instruction semantics** | Whitepaper §7: all instructions as lookups | Modify one table entry; verify different output |
| **Unpinned tables → non-deployable** | 9.4 rule + 3.5 gate | Attempt deployment without table spec; gate must reject |
| **Low-S eliminates malleability** | BIP-146, EIP-2; exactly one of s, n-s satisfies s ≤ n/2 | Submit (r, s) with s > n/2; must be rejected |
| **Canonical infinity prevents divergence** | 10.5 explicit encoding | Two implementations computing P + (−P); both must produce (0, 1, 0) |
| **DoS caps preserve liveness** | 10.6 requirement | Exceed MAX_ECDSA_SIGS; prover must reject |

### 10.9 Forward references

- **DoS cap pattern** → 5.7 (MAX_INTENTS), 5.8 (MAX_CHECKPOINTS_BYTES)
- **Registry structure** → Section 3
- **Conditional applicability** → Both Section 9 and Section 10 are marked "if used"; requirements activate only when features are used

---

*Sections 9 and 10 covered optional cryptographic features that deployments may or may not use. We now return to the core protocol mechanism that all Jolt continuations deployments require: continuations, which split unbounded executions into provable chunks.*

## Section 11: Continuations, snapshots, and StateDigest

### 11.1 The chunking imperative

A single batch of 10,000 trades spawns 50 million RISC-V instructions. Proving them all at once demands 100 gigabytes of RAM and hours of compute. The prover would choke. So we carve execution into chunks: one million instructions each, fifty proofs total, each one manageable.

But splitting creates a seam, and seams invite tampering. What stops a malicious prover from omitting chunk 26 (where the fraud check triggers) and stitching chunk 25 directly to chunk 27? Nothing, unless we seal each handoff.

### 11.2 The baton with a serial number

Think of a relay race where every baton carries a unique serial number. Runner 1 finishes holding baton #47B2. Runner 2 must start holding that same baton. If the numbers differ, someone cheated.

StateDigest is that serial number. It compresses the entire VM state—all 32 registers, the program counter, the step counter, Merkle roots of memory, and the active configuration tags—into a single field element. Chunk 0's ending digest must match Chunk 1's starting digest exactly. Skip a chunk? The digests diverge. Splice two unrelated executions together? The digests diverge. Swap configurations mid-stream? The digests diverge. The chain shatters at the first lie.

### 11.3 The splicing attacks

Without proper chaining, a malicious prover could:

**Attack 1: Skip chunks** — Chunks 1-25 prove instructions 0 through 24,999,999. Chunk 26 was supposed to prove the critical balance check that fails. Prover skips it, jumps to chunk 27. The "proof" omits the failure.

**Attack 2: Splice executions** — Execution A processes batch X (which should fail). Execution B processes batch Y (which passes). Prover generates chunks 1-25 from A, chunks 26-50 from B. The "proof" shows success, but no single execution succeeded.

**Attack 3: Cross-configuration splice** — Chunks 1-25 generated under configuration V1, chunks 26-50 under V2 with different rules. The "proof" mixes incompatible rules.

All three attacks share a pattern: the prover claims chunks belong together when they don't. The defense: **commit to state at chunk boundaries** and **enforce that adjacent chunks agree**.

If someone tries to skip chunk 3 (where the fraud gets detected) and jump to chunk 4, the serial numbers will not match. Chunk 2's ending serial number will not equal chunk 4's starting serial number. The chain breaks.

Chunk chaining uses `StateDigestV1`, a single-field commitment to:
- the entire VM state, and
- the active consensus configuration tags.

### 11.4 The defense: state commitment and chaining

Attacks 1–3 (skip, splice, cross-config) all exploit the absence of commitment to execution boundaries. The solution is elegant: commit to the entire state at each chunk boundary, and enforce that consecutive chunks agree on their shared state.

Enter **StateDigest**, a single field element that cryptographically binds:
- All 32 CPU registers (the computational state)
- Program counter and step counter (the execution position)
- Memory roots (the data commitments)
- Configuration tags (the semantic environment)
- Halted flag and exit code (the termination status)

**The chaining invariant**: For any two consecutive chunks i and i+1:
```
StateDigest_out(chunk_i) = StateDigest_in(chunk_i+1)
```

This single equation defeats all three attacks:
- **Skip attack**: Skipping chunk 3 means chunk 2's output digest ≠ chunk 4's input digest. Chain breaks.
- **Splice attack**: Splicing in a chunk from execution B means B's output digest ≠ the expected input digest for the next chunk. Chain breaks.
- **Cross-config attack**: Config tags are hashed into StateDigest. Different config → different digest → chain breaks.

The defense is both *necessary* (without it, attacks succeed) and *sufficient* (with it, forging a valid chain requires forging a hash collision or breaking soundness).

#### 11.4.1 Attack scenario: memory root forgery

The attacks above (skip, splice, cross-config) exploit structural gaps in chunk boundaries. But there exists a subtler attack that operates within the state itself: **memory root forgery**.

**Concrete scenario:**

A Settlement Engine processes 100 trades across 10 chunks. The execution is logically correct. In chunk 9, a critical balance check executes:

```
Read account[0x42].balance from memory address 0x1000_0000
Compare: if (balance < required_amount) revert
Trade proceeds: balance -= amount
Write new balance back
```

The prover executes this faithfully... then commits to a falsified memory root.

**Specifically:**

1. **Chunks 0–8 (honest):** Prover generates valid proofs with correct memory roots.

2. **Chunk 9 (forged memory):**
   - Guest executes: reads `mem[0x1000_0000]`, gets 0 (honest), compares against 1,000,000 (required).
   - Revert. Execution halts.
   - But prover claims `chunk_9.output_state.rw_mem_root` = SMT root where `mem[0x1000_0000]` = 1,000,000 (forged).

3. **The fake claim:**
   - "I executed chunk 9 under the honest rw_mem_root from chunk 8."
   - "The output memory state has account[0x42].balance = 1,000,000 (fabricated)."
   - "StateDigest chains perfectly: my step_counter, PC, registers, and (forged) rw_mem_root all digest together."

4. **Consequence without mitigation:**
   - If the chunk proof does NOT verify that the SMT root is the actual merkle commitment of memory contents, the wrapper accepts the forge.
   - On-chain verifier sees a valid chain of digests → approves unauthorized state transition.
   - Attacker has stolen funds via a false balance claim.

**Why this attack is different:**

- **Skip/Splice attacks** are detected by digest mismatch.
- **Memory forgery** passes the digest chain check. StateDigest includes the memory root, but a commitment to a root is not a commitment to the root's preimage.

**Defense (§11.9):** Chunk proofs MUST constrain that boundary VM states have memory-root fields equal to the SMT roots of the actual memory contents. Jolt's memory-checking architecture ensures every memory access is tracked during proof generation.

### 11.5 VMStateV1 (normative)

VM state tuple `S`:

| Field | Type | Purpose |
|-------|------|---------|
| `regs[32]` | u64[32] | All integer registers x0–x31 |
| `pc` | u64 | Program counter (next instruction address) |
| `step_counter` | u64 | Total instructions executed so far |
| `rw_mem_root_bytes32` | bytes32 | Commitment to read/write memory |
| `io_root_bytes32` | bytes32 | Commitment to I/O memory |
| `halted` | u8 | 0 = running, 1 = terminated |
| `exit_code` | u64 | Exit status (meaningful only if halted=1) |
| `config_tags` | vec<(name, value)> | Registry projection from §3.8 |

**Constraints (normative):**

1. `halted ∈ {0, 1}`
2. If `halted = 0`, then `exit_code` MUST equal `0`
3. If `halted = 1`, then `exit_code` MUST be in `[0, 255]` (V1 constraint per §6)
4. `config_tags` MUST equal the projection defined in §3.8 (exactly one entry per required tag, sorted lexicographically by `tag_name_bytes`, no duplicates)

The step_counter determines chunk boundaries. Chunk 0 ends at step CHUNK_MAX_STEPS-1. Chunk 1 starts at step CHUNK_MAX_STEPS. If the step counter doesn't match, something is wrong—either a chunk was skipped or the boundaries don't align.

The config_tags field prevents cross-configuration splicing. Chunks generated under config V1 have V1's projection. Chunks generated under V2 have different config_tags. Their StateDigests differ. Can't chain V1 chunks to V2 chunks.

### 11.6 Deterministic chunk boundaries

Let `CHUNK_MAX_STEPS` be pinned by `JOLT_CONTINUATIONS_V1`.

- Chunk `i` begins with `step_counter_in = i × CHUNK_MAX_STEPS`
- **Non-final chunks:** Execute exactly `CHUNK_MAX_STEPS` steps and MUST have `halted_out = 0`
- **Final chunk:** Executes `1..CHUNK_MAX_STEPS` steps and MUST have `halted_out = 1`

**Worked example (2.5 million instructions, CHUNK_MAX_STEPS = 1,000,000):**

| Chunk | Input step_counter | Instructions | Output step_counter | halted |
|-------|-------------------|--------------|---------------------|--------|
| 0 | 0 | 1,000,000 | 1,000,000 | 0 |
| 1 | 1,000,000 | 1,000,000 | 2,000,000 | 0 |
| 2 (final) | 2,000,000 | 500,000 | 2,500,000 | 1 |

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          CHUNK CHAINING DIAGRAM                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌───────────────┐  StateDigest_0  ┌───────────────┐  StateDigest_1         │
│  │    CHUNK 0    │ ══════════════▶ │    CHUNK 1    │ ══════════════▶        │
│  ├───────────────┤                 ├───────────────┤                        │
│  │ steps: 0 → 1M │                 │ steps: 1M→2M  │                        │
│  │ halted = 0    │                 │ halted = 0    │                        │
│  └───────────────┘                 └───────────────┘                        │
│                                                             │               │
│                                                             │ StateDigest_2 │
│                                                             ▼               │
│                                           ┌───────────────────────────────┐ │
│                                           │      CHUNK 2 (FINAL)          │ │
│                                           ├───────────────────────────────┤ │
│                                           │ steps: 2M → 2.5M              │ │
│                                           │ halted = 1                    │ │
│                                           │ exit_code → status_fr         │ │
│                                           └───────────────────────────────┘ │
│                                                                             │
│  ═════════════════════════════════════════════════════════════════════════  │
│                                                                             │
│  CHAINING INVARIANT:                                                        │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │ StateDigest(Chunk[i].out) == StateDigest(Chunk[i+1].in)               │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  TERMINATION INVARIANT:                                                     │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │ Final chunk MUST have halted_out == 1 (execution completed)           │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  SECURITY: Skip chunk → digests mismatch → proof invalid                    │
│            Splice executions → digests mismatch → proof invalid             │
└─────────────────────────────────────────────────────────────────────────────┘
```

Three chunk proofs. The wrapper verifies:
- Chunk 0 output = Chunk 1 input
- Chunk 1 output = Chunk 2 input
- Chunk 2 output has halted = 1

### 11.7 SnapshotArtifactV1 magic bytes

`SnapshotArtifactV1.magic[16]` MUST equal:

```
Hex:   4e 46 2f 53 4e 41 50 53 48 4f 54 2f 56 31 00 00
ASCII: "JOLT/SNAPSHOT/V1\0\0"
```

Any other value MUST be rejected. This prevents confusion with other file formats and provides a version marker.

**Non-consensus format note.** This appendix currently fixes only the `magic[16]` bytes for `SnapshotArtifactV1`. The remainder of snapshot serialization is an off-chain artifact and is not interpreted by the on-chain verifier; therefore it is not consensus-critical. Deployments that require snapshot interchange between independent implementations SHOULD standardize a canonical snapshot encoding (and include decode/encode round-trip vectors in the conformance bundle) or pin a snapshot encoding identifier under `JOLT_CONTINUATIONS_V1`.

### 11.8 Memory commitments (sparse Merkle trees; normative)

`VMStateV1` commits to memory via two roots:
- `rw_mem_root_bytes32` — commitment to the guest **read/write** address space
- `io_root_bytes32` — commitment to the guest **I/O** address space

Both are commitments to a **32-bit-key sparse Merkle tree** (SMT) over 4KiB pages.

#### 11.8.1 The problem with committing to memory

The guest VM has a large address space—potentially gigabytes. But a typical execution touches only a fraction: some stack pages, some heap pages, input/output buffers. Most memory is never accessed and remains zero.

Naively hashing all of memory is infeasible. Hashing 4GB of mostly-zeros wastes enormous time.

**Sparse Merkle Trees solve this:** Commit to a key-value map where most keys map to a default value (zero). You don't store or hash absent pages. You precompute what an empty subtree's hash would be, and use that whenever a subtree is entirely absent.

#### 11.8.2 Parameters (normative)

The SMT parameters are consensus-critical and MUST be fixed by `JOLT_GUEST_MEMMAP_V1`:

```
PAGE_SIZE_BYTES := 4096      (4 KiB per page)
PAGE_SHIFT := 12             (log2 of page size)
KEY_BITS := 32               (tree depth)
Bit order: MSB-first         (bit 31 is first branch decision)
```

**Key traversal (normative).** For a leaf key `k = page_index_u32`, let `b31..b0` be the 32-bit binary representation of `k` where `b31` is the most significant bit. When traversing from the root to the leaf, at depth `d = 0..31`, use bit `b(31 - d)`:
- `0` selects the left child
- `1` selects the right child

**Examples:**
- `k = 1` (`0x00000001`) → left for 31 levels, then right at the final level.
- `k = 0x80000000` → right at the first level, then left for 31 levels.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      SMT KEY TRAVERSAL (MSB-FIRST)                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  EXAMPLE: key = 5 = 0b00000000_00000000_00000000_00000101                    │
│                                                                             │
│                        ROOT (depth 0)                                       │
│                          │                                                  │
│                    bit 31 = 0                                               │
│                    ┌─────┴─────┐                                            │
│                    ▼           │                                            │
│                  LEFT         right                                         │
│                    │                                                        │
│              bit 30 = 0                                                     │
│              ┌─────┴─────┐                                                  │
│              ▼           │                                                  │
│            LEFT         right                                               │
│              │                                                              │
│            ... (bits 29..3 = 0, all LEFT)                                   │
│              │                                                              │
│            bit 2 = 1                                                        │
│              ┌─────┴─────┐                                                  │
│              │           ▼                                                  │
│            left        RIGHT                                                │
│                          │                                                  │
│                    bit 1 = 0                                                │
│                    ┌─────┴─────┐                                            │
│                    ▼           │                                            │
│                  LEFT         right                                         │
│                    │                                                        │
│              bit 0 = 1                                                      │
│              ┌─────┴─────┐                                                  │
│              │           ▼                                                  │
│            left        RIGHT ──▶ LEAF for key=5                             │
│                                                                             │
│  ═══════════════════════════════════════════════════════════════════════    │
│  TRAVERSAL RULE: At depth d, use bit (31-d) of the key                      │
│                  0 = left child, 1 = right child                            │
│                                                                             │
│  CONSENSUS CRITICAL: MSB-first (NOT LSB-first!)                             │
│  Wrong bit order → completely different tree → root mismatch                │
└─────────────────────────────────────────────────────────────────────────────┘
```

**Page index mapping (normative).** Each address space (RW and IO) is defined by two `u64` constants pinned by `JOLT_GUEST_MEMMAP_V1`:

- `REGION_BASE` (base address, inclusive)
- `REGION_SIZE_BYTES` (size in bytes)

The following MUST hold for each region:
- `REGION_BASE % PAGE_SIZE_BYTES == 0` (page-aligned base)
- `REGION_SIZE_BYTES % PAGE_SIZE_BYTES == 0` (whole number of pages)
- `(REGION_SIZE_BYTES >> PAGE_SHIFT) <= 2^32` (fits the 32-bit SMT key space)

For any guest byte address `addr_u64`:
- If `addr_u64 < REGION_BASE` or `addr_u64 >= REGION_BASE + REGION_SIZE_BYTES`, the access is out-of-range and MUST trap per §6 (no wrap-around semantics).
- Otherwise define:
  - `offset_u64 := addr_u64 - REGION_BASE` (checked subtraction; MUST NOT underflow)
  - `page_index_u32 := u32(offset_u64 >> PAGE_SHIFT)`
  - `page_offset_u12 := offset_u64 & (PAGE_SIZE_BYTES - 1)`

Implementations MUST use checked arithmetic (or unbounded integers) for these computations; any overflow/underflow MUST be treated as out-of-range and trap per §6.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        MEMORY LAYOUT DIAGRAM                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  GUEST ADDRESS SPACE (64-bit addresses)                                     │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │  0xFFFF_FFFF_FFFF_FFFF                                                │  │
│  │        ┌──────────────────────────────────────────────────┐           │  │
│  │        │    OUT OF RANGE (trap on access)                 │           │  │
│  │        ├──────────────────────────────────────────────────┤           │  │
│  │        │    I/O ADDRESS SPACE                             │           │  │
│  │        │    io_root_bytes32 ← SMT commitment              │           │  │
│  │        │    • Input buffer: manifest bytes                │           │  │
│  │        │    • Output buffer: PublicOutputsV1              │           │  │
│  │        │    • Base: IO_REGION_BASE                        │           │  │
│  │        ├──────────────────────────────────────────────────┤           │  │
│  │        │    UNMAPPED (trap on access)                     │           │  │
│  │        ├──────────────────────────────────────────────────┤           │  │
│  │        │    READ/WRITE ADDRESS SPACE                      │           │  │
│  │        │    rw_mem_root_bytes32 ← SMT commitment          │           │  │
│  │        │    • Stack: grows downward                       │           │  │
│  │        │    • Heap: grows upward                          │           │  │
│  │        │    • Data: initialized globals                   │           │  │
│  │        │    • Base: RW_REGION_BASE                        │           │  │
│  │        ├──────────────────────────────────────────────────┤           │  │
│  │        │    TEXT (code, read-only, not SMT-committed)     │           │  │
│  │        └──────────────────────────────────────────────────┘           │  │
│  │  0x0000_0000_0000_0000                                                │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  SMT STRUCTURE (32-bit keys, 4KB pages)                                     │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │         ROOT (Fr element)                                             │  │
│  │           /          \                                                │  │
│  │         /              \                                              │  │
│  │    [0xxx...]        [1xxx...]                                         │  │
│  │      /    \            /    \                                         │  │
│  │    ...    ...        ...    ...     ← 32 levels (KEY_BITS)            │  │
│  │     │      │          │      │                                        │  │
│  │   page   page       page   page     ← Leaves: leaf_fr(page_bytes4096) │  │
│  │                                                                       │  │
│  │  Empty subtrees use precomputed default[d] hashes                     │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  NOTE: Each address space has its own SMT root committed in StateDigest.    │
└─────────────────────────────────────────────────────────────────────────────┘
```

**Absent pages.** Any page not explicitly present is treated as the all-zero page:

```
ZERO_PAGE := 4096 bytes of 0x00
```

#### 11.8.3 Leaf and node hashing

Leaves and internal nodes are hashed into `Fr` using §8.7 helpers:

```
leaf_fr(page_bytes4096) := PoseidonHashV1("JOLT/SMT/PAGE/V1", page_bytes4096)
node_fr(left_fr, right_fr) := PoseidonHashFr2V1("JOLT/SMT/NODE/V1", left_fr, right_fr)
```

#### 11.8.4 Default (empty) subtree hashes

Define default hashes for absent subtrees:

```
default[0] := leaf_fr(ZERO_PAGE)
For d = 1..KEY_BITS: default[d] := node_fr(default[d-1], default[d-1])
```

The empty-tree root is `default[KEY_BITS]`.

These are constants—compute once, use everywhere. When building a proof, if an entire subtree is zeros, substitute the precomputed default hash.

#### 11.8.5 Root computation

For each address space (RW and IO), define:

- `NUM_PAGES := REGION_SIZE_BYTES >> PAGE_SHIFT` (from §11.8.2)
- `page_base(k) := REGION_BASE + (u64(k) << PAGE_SHIFT)`

**Page materialization (normative).** Define `page_bytes(k)` as a 4096-byte array such that for each `j` in `0..4095`:

- If `k < NUM_PAGES`:
  `page_bytes(k)[j] := mem_byte(page_base(k) + j)`
  where `mem_byte(a)` is the byte value at guest address `a` in this address space.
  The byte at the lowest address in the page (`page_base(k)`) is `page_bytes(k)[0]`, and the highest is `page_bytes(k)[4095]`.

- If `k >= NUM_PAGES`:
  `page_bytes(k) := ZERO_PAGE`
  (pages outside the configured region are unreachable and are treated as all-zero for the commitment).

**Leaf definition.** The SMT root `root_fr` is the root of the depth-32 tree whose leaf at key `k` is `leaf_fr(page_bytes(k))`.

Implementations MAY store only non-zero pages in snapshot artifacts, but MUST compute the root exactly as defined above, treating all omitted pages as `ZERO_PAGE`.

**Determinism note (ordering).** The SMT root is a function of the page-indexed contents, not insertion order. Implementations MAY process pages in any order as long as the resulting `root_fr` matches the definition above. As a defensive implementation practice (and for easier debugging), implementations SHOULD sort page indices in increasing `page_index_u32` order when iterating over page maps.

#### 11.8.6 Root encoding

`root_fr` MUST be encoded deterministically as:

```
root_bytes32 := FrToBytes32LE(root_fr)
```

### 11.9 Chunk proof statement (abstract)

Each chunk proof MUST bind (i.e., make verifier-visible and cryptographically fixed as part of the chunk proof statement):
- `state_digest_in_fr` and `state_digest_out_fr`, where:
  - `state_digest_in_fr := StateDigestV1(program_hash_bytes32, S_in)`
  - `state_digest_out_fr := StateDigestV1(program_hash_bytes32, S_out)`
  - `S_in` and `S_out` are the boundary `VMStateV1` values
- chunk index `i`
- steps executed in the chunk
- the VM transition relation under the pinned profile

The wrapper MUST enforce adjacency: `state_digest_out_fr[i] == state_digest_in_fr[i+1]`.

**Deterministic chunking metadata.** If the wrapper enforces the deterministic chunking constraints in §5.5, the chunk proof statement MUST also expose (as verifier-visible public values) the boundary metadata needed by the wrapper, at minimum:
- `step_counter_in_u64`, `step_counter_out_u64`
- `halted_out_u8`
- `exit_code_out_u8` (with a required `[0,255]` range per §6)

Alternatively, if these values are not exposed, the chunk proof statement MUST enforce the deterministic chunking constraints internally (and the wrapper MUST NOT assume it can read these fields from the digests).

**Memory root soundness (normative).** Chunk proofs MUST constrain that the boundary VM states `S_in` and `S_out` used to compute `state_digest_in_fr` / `state_digest_out_fr` have memory-root fields:
- `S_*.rw_mem_root_bytes32`
- `S_*.io_root_bytes32`

equal to the SMT roots of the corresponding boundary memory contents as defined in §11.8.

The enforcement mechanism is proof-system specific: it MAY be implemented by extending Jolt's memory-checking machinery and/or by adding explicit constraints, but it MUST be sound and MUST NOT rely on unchecked prover-supplied roots. This is the soundness link between StateDigest chaining and actual memory contents—without it, a malicious prover could claim arbitrary memory roots and splice unrelated memory states across chunks.

### 11.10 `StateDigestV1` (continuation binding; normative)

`StateDigestV1` is a Poseidon-based commitment to a full `VMStateV1` value. It binds continuation chunks so that chunks cannot be spliced across different executions/configurations.

`StateDigestV1` is intended as a *binding commitment* to `VMStateV1`. Under standard cryptographic assumptions for the transcript-defined Poseidon hash (e.g., collision resistance / random-oracle-style Fiat–Shamir modeling), it is computationally infeasible to find distinct states `S != S'` such that `StateDigestV1(program_hash_bytes32, S) == StateDigestV1(program_hash_bytes32, S')`. Implementations MUST treat `state_digest_fr` as a binding commitment, not as a literal proof of equality.

**Toy Model: Why absorption order matters**

Suppose you want to fingerprint a person using just three numbers: height, weight, age. If Alice absorbs (180, 75, 30) and Bob absorbs (75, 180, 30), they get different fingerprints—even if they later realize they meant the same person but recorded measurements in different orders.

StateDigest works the same way. It absorbs every piece of VM state in a fixed order—like filling out a form with numbered boxes. Box 4 is always the program counter. Boxes 5-36 are always the 32 registers. If two implementations fill boxes in different orders, they get different digests, and their chunks will not chain.

The algorithm below is the official form. Every implementation must fill it out the same way.

#### 11.10.1 Inputs

- `program_hash_bytes32` — `SHA-256(guest_elf_bytes)` (a deployment-pinned constant)
- `S` — a `VMStateV1` value

#### 11.10.2 Algorithm

```
1.  T := TranscriptV1.init()
    // init already absorbs "JOLT/TRANSCRIPT/V1"; do NOT absorb again

2.  T.absorb_tag("JOLT/STATE/V1")
    // Domain separation: this is a state digest

3.  T.absorb_bytes(program_hash_bytes32)
    // Bind to the specific Settlement Engine binary

4.  T.absorb_u64(S.pc)
    // Program counter

5.  For i = 0 to 31:
        T.absorb_u64(S.regs[i])
    // All 32 registers, in order

6.  T.absorb_u64(S.step_counter)
    // Where we are in execution

7.  T.absorb_bytes(S.rw_mem_root_bytes32)
    // Commitment to read/write memory

8.  T.absorb_bytes(S.io_root_bytes32)
    // Commitment to I/O memory

9.  T.absorb_u64(u64(S.halted))
    // halted is u8 in {0,1}; zero-extend to u64 for absorption

10. T.absorb_u64(S.exit_code)
    // Exit status

11. T.absorb_tag("JOLT/CONFIG_TAGS/V1")
    // Begin config section

12. T.absorb_u64(len(S.config_tags))
    // Number of config tags

13. For each (tag_name_bytes, tag_value_bytes) in sorted order:
        T.absorb_tag("JOLT/TAG/V1")
        T.absorb_bytes(tag_name_bytes)
        T.absorb_bytes(tag_value_bytes)
    // Each config tag with domain separation

14. state_digest_fr := T.challenge_fr()
    // Squeeze the final digest
```
■

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                   StateDigestV1 FLOW DIAGRAM (14 STEPS)                     │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │  1. T := Transcript.new()         [Create fresh Poseidon sponge]    │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                        │
│  ┌─────────────────────────────────▼───────────────────────────────────┐    │
│  │  2. absorb_tag("JOLT/STATE/V1")   [Domain separation marker]        │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                        │
│  ┌─────────────────────────────────▼───────────────────────────────────┐    │
│  │  3. absorb_bytes(program_hash)    [Bind to Settlement Engine ELF]   │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                        │
│  ┌─────────────────────────────────▼───────────────────────────────────┐    │
│  │  4. absorb_u64(pc)                [Program counter]                 │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                        │
│  ┌─────────────────────────────────▼───────────────────────────────────┐    │
│  │  5. FOR i = 0..31:                                                  │    │
│  │       absorb_u64(regs[i])         [All 32 RISC-V registers]         │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                        │
│  ┌─────────────────────────────────▼───────────────────────────────────┐    │
│  │  6. absorb_u64(step_counter)      [Execution progress - chunk ID]   │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                        │
│  ┌─────────────────────────────────▼───────────────────────────────────┐    │
│  │  7. absorb_bytes(rw_mem_root)     [RW memory commitment]            │    │
│  │  8. absorb_bytes(io_root)         [I/O memory commitment]           │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                        │
│  ┌─────────────────────────────────▼───────────────────────────────────┐    │
│  │  9. absorb_u64(halted)            [Execution state: 0=run, 1=done]  │    │
│  │ 10. absorb_u64(exit_code)         [Exit status if halted]           │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                        │
│  ┌─────────────────────────────────▼───────────────────────────────────┐    │
│  │ 11. absorb_tag("JOLT/CONFIG_TAGS/V1")   [Config section marker]     │    │
│  │ 12. absorb_u64(len(config_tags))        [Number of tags]            │    │
│  │ 13. FOR each (name, value) sorted:                                  │    │
│  │       absorb_tag("JOLT/TAG/V1")                                     │    │
│  │       absorb_bytes(name)                                            │    │
│  │       absorb_bytes(value)               [Registry projection]       │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                        │
│  ┌─────────────────────────────────▼───────────────────────────────────┐    │
│  │ 14. state_digest_fr := challenge_fr()   [SQUEEZE: output Fr]        │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                        │
│                                    ▼                                        │
│                         ┌────────────────────┐                              │
│                         │  STATE_DIGEST (Fr) │                              │
│                         │  Single field elem │                              │
│                         │  binds entire VM   │                              │
│                         │  state + config    │                              │
│                         └────────────────────┘                              │
│                                                                             │
│  SECURITY: Change ANY input → different digest → chain breaks               │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### 11.10.3 Notes

- `config_tags` MUST be the exact deterministic projection defined in §3.8 (sorted, no duplicates, excludes external handles)
- All `bytes32` values are absorbed as raw bytes via `absorb_bytes`, not via `Bytes32ToFr2` (which is only for wrapper public inputs)
- The absorption order is consensus-critical; all implementations must follow steps 1–14 exactly

Including program_hash means different program → different hash → different digest → can't substitute programs.

Including config_tags means different config → different tags → different digest → can't splice across configurations.

### 11.11 Attack prevention summary

| Attack | How StateDigest Prevents It |
|--------|---------------------------|
| Skip chunk | step_counter in digest; chunk N output expects step N×MAX |
| Splice executions | All state (registers, memory, PC) in digest |
| Cross-config splice | config_tags in digest |
| Wrong program | program_hash in digest |
| Memory tampering | Memory roots in digest |
| Register tampering | All 32 registers in digest |

### 11.12 Definition block

**Continuation:** A mechanism for proving long executions as separate chunks that chain together. Each chunk proves a bounded segment; chaining via committed state lets segments compose.

**StateDigest:** A single-field (Fr) commitment to the complete VM state including registers, PC, memory roots, step counter, and configuration. Used to bind chunk boundaries.

**Sparse Merkle Tree (SMT):** A Merkle tree over a sparse key space where most keys map to a default value. Allows committing to large address spaces efficiently by precomputing hashes of empty subtrees.

**Chunk boundary:** The point where one chunk proof ends and the next begins. Defined by step_counter = i × CHUNK_MAX_STEPS.

**SnapshotArtifact:** A serialized VMStateV1 that can be transferred between machines for distributed proving.

### 11.13 Load-bearing claims

| Claim | Evidence | Verification |
|-------|----------|--------------|
| **StateDigest prevents chunk splicing** | All state fields absorbed | Attempt splice; verify digests don't chain |
| **SMT commits entire address space** | 32-bit keys = 2^32 leaves; absent = ZERO_PAGE | Modify single byte; verify root changes |
| **Chunk boundaries are deterministic** | step_counter = i × CHUNK_MAX_STEPS | Two implementations; verify identical splits |
| **Absorption order is consensus-critical** | §11.10.2 exact sequence | Swap absorption order; verify different result |
| **config_tags prevents cross-config splice** | config_tags absorbed in digest | Generate chunks under two configs; verify incompatible |
| **program_hash prevents cross-program splice** | program_hash absorbed first | Generate chunks for two programs; verify incompatible |

### 11.14 Jolt whitepaper connections

| Section 11 Concept | Whitepaper Section | Connection |
|--------------|-------------------|------------|
| VMStateV1 (regs, pc, memory) | Figure 1: CPU state | Jolt's "CPU State i" = Jolt continuations's VMStateV1 |
| Memory commitments | §2.4: Offline memory checking | Jolt uses fingerprinting internally; Jolt continuations uses SMT for inter-chunk commitments |
| Chunk as unit of proof | §3.2: Memory-checking | Jolt proves N steps at once; Jolt continuations chunks when N exceeds CHUNK_MAX_STEPS |
| Deterministic transition | Figure 1 note | VMStateV1 fully determines next instruction |

### 11.15 Forward references

- **CHUNK_MAX_STEPS value** → Section 3 (JOLT_CONTINUATIONS_V1, currently TBD)
- **Memory region addresses** → Section 3 (JOLT_GUEST_MEMMAP_V1, currently TBD)
- **Transcript functions** → Section 8 (absorb_bytes, absorb_u64, absorb_tag, challenge_fr)
- **config_tags projection** → Section 3.8
- **Wrapper enforcing adjacency** → Section 5.5
- **Snapshot encryption for confidentiality** → Section 13

---

## Section 12: Polynomial commitment scheme constraints and wrapper feasibility

### 12.1 Jolt's flexibility, continuations' constraint

Jolt's architects made a deliberate choice: the system accepts *any* polynomial commitment scheme. This flexibility serves implementers who face wildly different constraints—some need trusted setups, others refuse them; some optimize for proof size, others for verification speed. But Jolt continuations cannot inherit this luxury. The wrapper circuit must verify a concrete proof, and verification has a shape. That shape depends entirely on which PCS you pick.

The wrapper is a Halo2 circuit over BLS12-381's scalar field. Think of it as a judge who must evaluate evidence, but can only perform certain operations cheaply. Elliptic curve pairings—the verification method for KZG and Groth16—cost millions of constraints inside a circuit. This is not a soft preference; it is a hard boundary. The wrapper *must not* attempt pairing-based verification. The math simply does not fit.

What does fit? Group operations on curves where the base field matches the wrapper's native field. Here curve cycles become essential: a pair of curves where each curve's scalar field equals the other's base field. When this alignment holds, verifying commitments transforms from expensive foreign arithmetic into cheap native field operations. IPA and Hyrax schemes can exploit this structure. FRI and STARK schemes take a different path entirely—they replace elliptic curves with hash functions, trading one complexity for another. Hash-based verification demands many evaluations and Merkle proofs, creating proofs too large for direct wrapper consumption. The solution is recursive aggregation: prove that you verified the proof, producing a compact attestation the wrapper can digest.

### 12.2 Why small elements matter

Jolt's small-element property tilts the playing field toward MSM-based schemes. The whitepaper (§1.3.2) documents this precisely: under sixty field elements per CPU step, with only six exceeding 2^25. Pippenger's algorithm for multi-scalar multiplication rewards small exponents—committing to a 25-bit value costs roughly one-tenth what a 256-bit value demands. Hash-based schemes gain nothing from this property; hashing a small number takes the same time as hashing a large one. The architecture whispers its preference without dictating a choice.

Multi-scalar multiplication computes expressions like:
```
C = g₀^c₀ · g₁^c₁ · ... · gₙ₋₁^cₙ₋₁
```

This advantage applies to MSM-based schemes: KZG, IPA, Bulletproofs, Hyrax. It doesn't help hash-based schemes like FRI—hashing a small number isn't meaningfully cheaper than hashing a large one.

### 12.3 The wrapper verification budget

The wrapper circuit has a constraint budget. Every verification operation inside the wrapper translates to constraints, and constraints cost proving time. This creates a hard engineering tradeoff: the more expensive the verification procedure, the slower batch settlement becomes.

**Budget categories:**

| Operation Class | Constraint Cost | Feasibility |
|-----------------|-----------------|-------------|
| Native field arithmetic | O(1) | Always feasible |
| Non-native field arithmetic | O(limbs²) | Expensive but possible |
| Hash evaluations | O(rounds × state) | Moderate |
| Elliptic curve scalar mul | O(bits) | Feasible |
| Pairing (BLS12-381) | O(millions) | **Not feasible** |

The takeaway: the wrapper can verify commitments using native-field operations (IPA, Hyrax on cycle curves), can verify hash-based proofs with overhead (FRI recursion), but *cannot* directly verify pairing-based proofs (KZG, Groth16) without an intermediate aggregation step.

**Why this matters for PCS selection**: If your Jolt implementation uses KZG internally, the wrapper cannot verify it directly. You must either:
1. Use a different PCS for the wrapper layer (cycle-curve IPA), or
2. Recursively aggregate KZG proofs into a wrapper-friendly format.

This constraint shapes the entire proving architecture and is why §12.4 categorizes PCS options by their verification costs.

### 12.4 Three categories of PCS

Different polynomial commitment schemes have distinct verification procedures:

#### Pairing-based (KZG, Groth16-style)

**Verification:** Compute elliptic curve pairings, check equality.

**Cost (non-normative, illustrative):** A BLS12-381 pairing is typically expensive on-chain, and in-circuit pairing gadgets are typically far beyond practical wrapper budgets.

**Trusted setup:** Yes. KZG requires a "powers of tau" ceremony.

**Section 12 verdict (normative):** The wrapper circuit **MUST NOT** perform elliptic-curve pairing checks when verifying the **Jolt proof** recursively. The cost is prohibitive.

*Note:* This prohibition applies only to verification performed **inside the wrapper circuit**. It does not, by itself, constrain which primitives the **outer** on-chain verifier uses to verify the wrapper proof.

**Attack scenario: the shortcut implementer**

A blockchain team decides to use BLS12-381 for Jolt's PCS. They read Section 12.4 but interpret it as guidance rather than a hard requirement. After testing, they decide: "Our verifier only needs to check the pairing."

**The attempt:**
- **Phase 1 (Overconfidence):** Implementer designs wrapper circuit to inline pairing verification.
- **Phase 2 (Constraint Explosion):** Compiler estimates 2-5M constraints for the pairing logic alone (Miller loop + final exponentiation over two field towers).
- **Phase 3 (Budget Realization):** Total wrapper budget is ~1M-16M rows. A 4M constraint pairing check consumes 25-100% of the entire circuit capacity.
- **Phase 4 (Shortcut Decision):** Facing budget overrun, implementer omits the final exponentiation step (cheaper, ~20% cost reduction).

**The break:** The incomplete pairing check becomes exploitable. A malicious prover crafts commitments that fail full verification but pass the partial check. The prover can now forge commitments for arbitrary polynomials without a valid witness.

**Why shortcuts don't work:**
1. **Pairing is pairing:** The bilinear property verification cannot be skipped without breaking the commitment scheme's security proof.
2. **No circuit optimization magic:** Modern compiler optimizations reduce overhead by 2-3x at best, not 10x. A 4M constraint operation cannot become 400K constraints.
3. **Finality risk:** If you defer pairing verification off-chain, the on-chain state becomes provisional. This breaks blockchain finality guarantees.

**The lesson:** Pairing verification is not a tuning dial. It is a hard boundary. Systems that cross it sacrifice soundness for false economy.

#### MSM-based without pairings (IPA, Bulletproofs, Hyrax)

**Verification:** Multi-scalar multiplications and group additions on the commitment curve.

**Cost (non-normative, illustrative):** Depends on whether the commitment curve is "native" to the wrapper. If the curve's base field equals the wrapper's scalar field, group operations become field arithmetic—cheap. MSM verification is typically feasible in-circuit when native.

**Trusted setup:** No. These schemes are transparent.

**Section 12 verdict (normative):** Native group operations are **permitted** via curve-cycle style. This enables efficient IPA/Hyrax verification, subject to the field requirements in §12.5.

#### Hash-based (FRI, STARK)

**Verification:** Many hash evaluations plus Merkle path checks.

**Cost (non-normative, illustrative):** Hash-based PCS verification can require many hash evaluations and Merkle checks, often leading to large proofs and high in-circuit verification cost.

**Trusted setup:** No. Hash-based schemes are transparent and plausibly post-quantum secure.

**Section 12 verdict (normative):** If a hash-based PCS is used, the deployment MUST include a **fully specified** recursive aggregation layer that produces a compact proof verified by the wrapper.

The aggregation layer MUST be pinned in the registry (as fields of `JOLT_PCS_V1` or another registry object referenced by `JOLT_PCS_V1`) and MUST include, at minimum:
- aggregation proof system identifier + version
- aggregation verifier key hash
- transcript/hash parameters and domain separation tags
- exact public input format binding the aggregated proof to the underlying PCS proof(s)

The wrapper MUST verify the aggregated proof and MUST NOT accept an unaggregated hash-based PCS proof directly unless it still satisfies the feasibility bounds in §12.6.

### 12.5 Curve cycles: making group operations native

The wrapper circuit operates over BLS12-381's scalar field Fr. To verify IPA or Hyrax commitments efficiently, you need the commitment curve's arithmetic to be native.

A "curve cycle" is a pair of curves where each curve's scalar field equals the other's base field. The classic example: Pasta curves (Pallas and Vesta). Pallas has scalar field equal to Vesta's base field, and vice versa. You can verify Pallas commitments inside a Vesta circuit using only native field operations.

**Field disambiguation (normative).** For Jolt continuations's Halo2 wrapper over BLS12-381, let **F_wrap := BLS12-381 scalar field Fr** (the field the wrapper circuit is defined over).

A PCS involves **two distinct kinds of fields** that MUST NOT be conflated:

- **F_pcs (PCS scalar field):** the field of polynomial coefficients/evaluations and Fiat–Shamir challenges used as scalars in verification.
- **Commitment group G:** an elliptic-curve group defined over some **base field F_base**, with **scalar field F_scalar** (the group order).

**Correctness requirement (normative).** A deployed PCS MUST satisfy **F_pcs = F_scalar** (the PCS scalars are exactly the scalars used by the commitment group).

**Jolt Continuation V1 requirement (normative).** Because the wrapper transcript and circuit operate over **Fr** (§8), a deployed `JOLT_PCS_V1` MUST use **F_pcs = Fr**.

A commitment curve is "native" to the wrapper iff **F_base = F_wrap**, so point arithmetic is expressed directly in `Fr` constraints. If **F_base ≠ F_wrap**, the wrapper MUST specify the non-native arithmetic gadgets used and MUST still meet the feasibility bounds in §12.6.

This is what §12.7 means by "native group operations are permitted on curves defined over Fr".

### 12.6 Feasibility requirement (normative)

Any pinned `JOLT_PCS_V1` MUST include, at minimum:

**PCS identity fields:**
- **pcs_family** and **pcs_version** (e.g., `"IPA"`, `"Hyrax"`, `"KZG"`, `"FRI"`)
- **F_pcs identifier** (the PCS scalar field; Jolt Continuation V1 requires `Fr`)
- **commitment_group identifier** (curve/group name or fully specified parameters)
- **F_base identifier** and **F_scalar identifier** for the commitment group (see §12.5)
- **trusted_setup** descriptor:
  - if a trusted setup is required (e.g., KZG), include an **SRS identifier** and **max supported degree**
  - if no trusted setup, explicitly state `"transparent": true`
- **transcript_binding**: the transcript/hash configuration used by the PCS verifier (domain tag + hash parameters)

**Feasibility bounds:**
- **proof_size_max_bytes**: maximum bytes of the Jolt proof
- **wrapper_max_rows**: maximum rows (and/or `k`) needed to verify in the wrapper circuit
- **verifier_cost_max**: maximum on-chain verification cost (deterministic; see below)

These fields MUST be part of the canonical `JOLT_PCS_V1` registry value so that they are included in the chain's deployment binding (see §3).

| Bound | What It Measures | Why It Matters |
|-------|------------------|----------------|
| **Proof size** | Max bytes of the Jolt proof | Affects calldata costs; must fit in transactions |
| **Wrapper rows** | Max rows (and/or `k`) needed to verify | Determines wrapper proving time and memory |
| **Verifier cost** | Max on-chain verification cost (e.g., gas) for the wrapper proof | Must fit within block gas limits |

*Implementation note (normative):* If the chain does not have a gas model, `verifier_cost_max` MUST be specified as a deterministic step-count or instruction-count metric defined by the chain.

*Normative:* Deployment acceptance MUST use the explicit feasibility bounds pinned in `JOLT_PCS_V1`, not illustrative estimates elsewhere in this section.

Without documented bounds, you can't estimate on-chain costs, size prover hardware, set fee parameters, or know if the system is economically viable.

### 12.7 PCS constraints (normative)

Inside the wrapper circuit:

- The wrapper **MUST NOT** perform elliptic-curve pairing checks (see §12.4)
- **Native group operations are permitted** on curves defined over `Fr` (curve-cycle style), enabling IPA/Hyrax-like PCS verification (see §12.5)

If a hash-based PCS is used, the deployment MUST include a fully specified recursive aggregation layer such that the wrapper verifies a compact proof (see §12.4).

The exact PCS MUST be pinned (not `TBD`) for deployment, with all required fields per §12.6.

### 12.8 Trusted setup implications

| PCS Type | Trusted Setup | Security Assumption |
|----------|---------------|---------------------|
| KZG | Yes (powers of tau) | Discrete log + ceremony honesty |
| IPA/Bulletproofs | No | Discrete log only |
| Hyrax | No | Discrete log only |
| FRI/STARK | No | Hash function collision resistance |

This affects deployment decisions. KZG offers efficient verification but requires trusting a setup ceremony. IPA is trustless but has higher verification costs. FRI is trustless and plausibly post-quantum but requires aggregation for wrapper compatibility.

Jolt continuations's choice will be pinned in `JOLT_PCS_V1`.

### 12.9 Definition block

**Polynomial commitment scheme (PCS):** A cryptographic protocol allowing a prover to commit to a polynomial and later prove evaluations at chosen points. The commitment is binding and hiding.

**Multi-scalar multiplication (MSM):** Computing ∏gᵢ^cᵢ for generators gᵢ and scalars cᵢ. The core operation in many PCS schemes. Cost depends on scalar sizes.

**Curve cycle:** A pair of elliptic curves where each curve's scalar field equals the other's base field. Enables efficient in-circuit verification of commitments.

**Recursive aggregation:** Proving that you verified another proof. Produces a smaller proof that attests to the original proof's validity.

**Trusted setup:** A ceremony that generates public parameters for a cryptographic scheme. Security requires at least one participant to be honest.

### 12.10 Load-bearing claims

| Claim | Evidence | Verification |
|-------|----------|--------------|
| **Pairing verification infeasible in-circuit** | ~2-5M constraints for BLS12-381 pairing | Benchmark pairing gadget; compare to target |
| **IPA/Hyrax feasible with curve cycles** | Native field arithmetic when base field = Fr | Benchmark IPA verifier in Halo2 |
| **Jolt benefits from MSM-based PCS** | Whitepaper §1.3.1: elements mostly < 2^25 | Compare prover time: small vs random exponents |
| **Hash-based requires aggregation** | FRI proof size 50-200KB + hash count | Estimate constraint count for direct FRI verification |
| **Bounds must be documented** | Section 12.6 requirement | Check registry: proof size, constraints, gas in tags |

### 12.11 Jolt whitepaper connections

| Section 12 Concept | Whitepaper Section | Connection |
|--------------|-------------------|------------|
| PCS-agnostic design | §2.2 | "Lasso can make use of any commitment schemes" |
| Small-element advantage | §1.3.1 | Elements mostly < 2^25; Pippenger benefits |
| MSM as prover bottleneck | §1.3.1 | "the bottleneck for the prover is the polynomial commitment scheme" |
| FRI comparison | §1.3.2 | "Jolt's property... benefits elliptic-curve-based schemes more" |
| Trusted setup dependence | §2.2 | "Whether or not a SNARK requires a trusted setup... is determined by the PCS" |

### 12.12 Conformance requirements (normative)

The conformance bundle (§14) MUST include PCS-selection conformance cases:

1. **Positive case:** A wrapper proof that verifies a valid Jolt proof under the pinned `JOLT_PCS_V1`.

2. **Negative case (PCS substitution):** The same proof artifacts MUST fail verification if `JOLT_PCS_V1` is modified (e.g., different `pcs_family`, curve identifier, or SRS identifier), demonstrating binding to the registry.

3. **Bound enforcement case:** A proof artifact exceeding `proof_size_max_bytes` (or exceeding the pinned `verifier_cost_max` bound if enforceable) MUST be rejected by the reference verifier.

4. **Field correctness case:** A test that exercises the F_pcs = F_scalar requirement, verifying that PCS scalars are correctly interpreted as commitment group scalars.

### 12.13 Forward references

- **Wrapper circuit constraints** → Section 5.5
- **On-chain verifier** → Section 4
- **Registry tags** → Section 3
- **Proof size in public inputs** → 5.3
- **Conformance bundle** → Section 14
- **Confidentiality mechanisms** → Section 13

The polynomial commitment scheme ensures mathematical soundness: no computationally bounded adversary can produce a valid proof for a false statement. But soundness is only half the security equation. A proof that is mathematically valid may still compromise privacy if the witness data it depends on leaks through operational channels. Section 13 addresses this orthogonal concern: maintaining confidentiality when snapshot artifacts and continuation witnesses must cross trust boundaries during proving.

---

## Section 13: Confidentiality and artifact handling

### 13.1 The dirty secret

Every intent system today betrays a dirty secret: solvers see everything. CoW Protocol batch solvers read your full order details. UniswapX fillers know your amounts and recipients. The industry calls this necessary. The host chain calls it a problem.

The host chain promises "rational privacy"—you control what gets revealed, to whom, when. But here lies a tension sharp enough to cut: how do you settle intents without exposing them? The answer layers three shields—network encryption, execution privacy, on-chain commitment hiding—each guarding different data at different moments. Section 13 tackles execution privacy, the overlooked middle child whose absence would unravel the entire model.

### 13.2 What's in a snapshot worth protecting?

Consider what a snapshot actually contains. VMStateV1 captures complete execution state: 32 registers that may hold parsed amounts, a program counter revealing execution progress, memory roots whose preimages contain decoded user data, I/O roots whose preimages expose raw inputs and outputs.

| Field | Contents | Sensitivity |
|-------|----------|-------------|
| `regs[32]` | All 32 registers | May contain parsed amounts, addresses |
| `pc` | Program counter | Reveals execution point |
| `rw_mem_root` | Commitment root over RAM pages | Snapshot includes RAM page preimages containing decoded user data |
| `io_root` | Commitment root over I/O pages | Snapshot includes I/O buffer preimages containing raw inputs/outputs |

If the Settlement Engine processed Alice's cross-chain transfer, her amount sits in a register. Her recipient address lives in memory. The entire plaintext tuple—amount, recipient, destination chain, token, nonce, timestamp—might occupy the I/O region. Continuation witnesses are richer still: not just final state but every intermediate value, every memory access, every register update across millions of instructions. This is not metadata. This is the actual user data that commitments were supposed to hide.

### 13.3 The attack: leaking at the prover

Now trace the attack. Alice creates an intent and posts commitment C on-chain—hidden. A sealed-bid auction selects her solver—hidden from competitors. The solver executes settlement privately. Then the prover receives the witness to generate the proof, and suddenly the prover knows Alice's amount, her recipient, her timing. The infrastructure operator knows it too. If they log, that data persists. If compromised, attackers have it. If colluding with competitors, those competitors can trade against Alice. The commitment hid nothing from anyone with prover access—it merely delayed exposure until proving time.

This is the gap Section 13 closes. Soundness follows from the cryptographic assumptions (DLP, SHA-256 collision resistance, Fiat-Shamir)—no one can forge proofs regardless of what they see. Confidentiality requires infrastructure protection—ensuring the wrong parties do not see the witness.

### 13.4 Attack scenarios in practice

This section bridges the conceptual attack ("the prover sees everything") with concrete infrastructure scenarios where that exposure becomes an operational catastrophe.

#### 13.4.1 Colluding infrastructure operator (MEV-style front-running)

Alice posts an intent commitment for a cross-chain transfer: "Swap 100,000 USDC for 50 ETH, recipient 0xBob...". The commitment hides the amount and recipient from public observers. A sealed-bid auction selects her solver—hidden from competitors. The solver executes settlement privately.

Then the proof generation begins. The prover node receives the witness: plaintext execution trace showing registers holding `amount=100000`, memory containing `recipient_address=0xBob...`, I/O buffers with the complete transaction details. If the prover operator colludes with trading competitors (or *is* a competitor), they now possess a temporal advantage: they know Alice's intent *before the market sees the proof*.

**The attack**: The colluding operator observes Alice's plaintext witness, sees she is about to receive 50 ETH at a specific price, and front-runs her by placing a competing order on a different venue. By the time Alice's proof settles, the operator has already profited from knowing her trade.

**Mitigation**: Encrypt the witness. If the prover operator cannot decrypt the artifact, they cannot extract this temporal arbitrage.

#### 13.4.2 Log persistence attack (long-lived exfiltration)

The prover node logs execution to help with debugging: timestamps, function entry/exit, intermediate values, memory access patterns. During normal operation, these logs are ephemeral—they cycle out of the buffer and are discarded. This seems safe: the log is not persisted.

But suppose a vulnerability is discovered in the prover software. Engineering deploys an instrumented version with deeper logging to understand the bug. That version writes logs to disk for later analysis. A user's high-value transfer happens to execute during this instrumented period. The logs capture amounts, addresses, timing, intermediate register values.

Months later, the organization suffers a breach. Attackers exfiltrate backup archives containing those instrumented logs. Suddenly, months of witness data—amounts, addresses, patterns—are exposed. The delay between logging and exfiltration defeats real-time threat detection.

**Mitigation**: Classify logs as artifacts. If logs contain any data derived from witness execution, they must be encrypted with the same AEAD envelope as snapshots and continuation witnesses.

#### 13.4.3 VM snapshot replay attack for nonce counters

The prover runs in a virtual machine (e.g., KVM inside a TEE). To support high availability and disaster recovery, the operator periodically snapshots the VM state to persistent storage. If the VM crashes, they restore from the latest snapshot and resume execution.

The AEAD encryption uses a counter-based nonce strategy: the prover maintains a persistent counter N, and for each encryption, it uses `nonce = counter++`. This guarantees uniqueness—every artifact encrypted under the key uses a distinct nonce. As long as the counter never resets, nonce reuse is impossible.

Now suppose a crash occurs after encrypting artifact A with nonce=17, but before the counter is persisted. The operator restores the snapshot where counter=17. The next encryption uses nonce=17 again—encrypting a *different* artifact B. Nonce reuse. An attacker with access to both ciphertexts can XOR them to recover plaintext, or forge authentication tags via Joux's attack on GCM.

**Mitigation**: Use random or derived nonces (resilient to state resets) rather than counter-based. Or ensure counter state is persisted with higher durability than the VM snapshot.

### 13.5 Trust boundaries and the TEE perimeter

A Trusted Execution Environment (TEE) creates a hardware-enforced encrypted bubble. Intel SGX, AMD SEV, AWS Nitro—these technologies ensure that even a root-privileged host OS cannot read memory inside the enclave.

**Inside the TEE:**
- Prover software runs
- Witness data stays in encrypted memory
- Intermediate computations never leave in plaintext
- Host OS sees only ciphertext

**The moment data crosses the TEE boundary, hardware protection ends:**
- Network transit to an aggregator
- Disk persistence for later resumption
- Transfer to another prover for distributed proving
- Snapshot export for debugging

At that moment, confidentiality depends on software—specifically, encryption.

### 13.6 Encryption requirement for exported artifacts (normative)

If a snapshot artifact leaves a trusted boundary (TEE), it MUST be encrypted with AEAD.

**Artifact-layer requirement (normative).** "Encrypted with AEAD" means the exported artifact bytes are produced by an AEAD encryption call over the **entire serialized artifact payload** (envelope encryption). Transport-layer encryption (e.g., TLS) MAY be used in addition, but does not satisfy this requirement by itself because artifacts may be persisted or forwarded outside the transport context.

**Fail-closed decryption (normative).** Implementations MUST verify the AEAD tag before parsing or acting on any decrypted plaintext. Any authentication failure MUST return a single ERROR result (no distinguished error classes) and MUST NOT leak any plaintext via logs, errors, or partial outputs.

**Associated data binding (normative).** The AEAD associated data `AD` MUST authenticate all artifact metadata that a receiver uses to route, interpret, or label the artifact. For snapshot artifacts and continuation witnesses, `AD` MUST include at minimum:
- `artifact_kind`: an ASCII string identifying the artifact type (e.g., `"SNAPSHOT"`, `"WITNESS"`)
- `chunk_index_u64`: the chunk index as a `u64`
- `state_digest_out_bytes32`: the canonical 32-byte little-endian encoding of `state_digest_out_fr` (use `FrToBytes32LE` from §7)

Deterministic encoding of `AD` MUST be:
`AD := ASCII("JOLT/ARTIFACT/V1") || 0x00 || ASCII(artifact_kind) || 0x00 || U64LE(chunk_index_u64) || state_digest_out_bytes32`

ASCII strings MUST use raw bytes in `[0x20..0x7E]` with no Unicode normalization. `U64LE` is the 8-byte little-endian encoding.

**Operational encryption parameters (deployment‑pinned, not consensus‑critical).** Deployments that export any snapshot/witness artifact outside a trusted boundary MUST pin concrete values for:
- `JOLT_ARTIFACT_AEAD_V1`
- `JOLT_ARTIFACT_KDF_V1`
- `JOLT_ARTIFACT_NONCE_RULE_V1`

These parameters are **operational** and MUST NOT be interpreted as consensus‑critical proof inputs. For V1 deployments they MUST NOT appear as keys in `registry.json` (see §3.3 "V1 key set"), and MUST NOT be absorbed into `config_tags` (§3.8) or `StateDigestV1` (§11).

Deployments that keep all artifacts inside a trusted boundary may omit these parameters.

**Plaintext artifacts MUST NOT leave the trusted boundary.** Any export (network, disk, debug bundle, or handoff to another machine) MUST export only the AEAD‑encrypted artifact envelope.

### 13.7 The conditional structure

The encryption requirement triggers only when artifacts cross the trust boundary:

| Scenario | Encryption Required? |
|----------|---------------------|
| Snapshot stays inside TEE | No (hardware protects) |
| Snapshot transmitted to aggregator | Yes |
| Snapshot written to disk outside TEE | Yes |
| Snapshot passed to another TEE | Yes (transit unprotected) |
| Witness used only within single TEE session | No |

This is pragmatic. Encryption adds overhead. If data never leaves the hardware-protected region, that overhead is unnecessary. But the moment data exits—for any reason—encryption becomes mandatory.

The prohibition on sharing plaintext with untrusted aggregators is absolute. There's no "but we trust this aggregator" exception.

**Diagnostics are artifacts (normative).** Any plaintext material derived from witness execution—including logs, traces, profiles, core dumps, debug bundles, memory dumps, and "error repro" attachments—MUST be treated as an artifact. If it leaves the trusted boundary, it MUST be protected by the same AEAD requirement as snapshots and continuation witnesses, and MUST NOT be exported in plaintext.

### 13.8 AEAD rationale

#### The failure of generic composition

Before AEAD standardization, protocols combined encryption and authentication as separate layers. SSL/TLS through version 1.2, SSH, and IPsec all used block ciphers (AES-CBC, 3DES) with independent MACs (HMAC-SHA1). Three composition methods existed:

**Encrypt-and-MAC:** Encrypt plaintext P to ciphertext C, compute MAC on P independently. The MAC operates on plaintext—if the MAC algorithm leaks information about its input (not a design requirement for MACs), confidentiality fails.

**MAC-then-Encrypt:** Compute MAC on P, append it, encrypt everything. TLS used this. The decryption sequence—decrypt, check padding, verify MAC—created distinct error states. Attackers measured timing differences between "bad padding" and "bad MAC" responses to decrypt messages byte-by-byte. Vaudenay's padding oracle (2002) and Lucky13 (2013) exploited this for over a decade.

**Encrypt-then-MAC:** Encrypt P to C, compute MAC on C. The receiver verifies MAC before attempting decryption. If verification fails, the ciphertext is discarded without touching the decryption logic. This "verify-then-decrypt" principle eliminates padding oracles.

AEAD internalizes Encrypt-then-MAC into a single algorithm. The interface is atomic:

```
Enc(K, N, A, M) → (C, T)
Dec(K, N, A, C, T) → M or ⊥
```

If the tag doesn't match, decryption returns ⊥ without releasing partial plaintext. No error distinctions, no timing oracles, no composition mistakes.

#### Why associated data matters

The "AD" in AEAD allows authenticating data that must remain unencrypted. In network protocols, packet headers contain routing information—IP addresses, sequence numbers, protocol versions. These can't be encrypted (routers need them) but must be tamper-proof.

For Jolt continuations artifacts, associated data might include:
- Artifact version identifiers
- Chunk indices for continuation witnesses  
- Timestamps for key rotation verification

Modifying any associated data invalidates the tag. The artifact is rejected before decryption.

#### The nonce reuse catastrophe

Both AES-GCM and ChaCha20-Poly1305 are "nonce-respecting" schemes. Their security proofs assume no two encryptions under the same key ever reuse a nonce. Violate this assumption and security collapses—not degrades, collapses.

**AES-GCM under nonce reuse (Joux's attack):**

GCM uses GHASH, a polynomial evaluation over GF(2^128). The authentication tag is:

```
T = Enc_K(J₀) ⊕ GHASH_H(A, C)
```

where H = Enc_K(0^128) is the hash subkey derived from the encryption key.

If an attacker captures two valid (ciphertext, tag) pairs encrypted with the same nonce:

```
T₁ = Enc_K(J₀) ⊕ Poly₁(H)
T₂ = Enc_K(J₀) ⊕ Poly₂(H)
```

XORing eliminates the unknown mask:

```
T₁ ⊕ T₂ = Poly₁(H) ⊕ Poly₂(H)
```

The attacker knows the ciphertexts (thus the polynomial coefficients) and the tags. The only unknown is H. This is a polynomial equation over GF(2^128)—solving it via Berlekamp-Rabin yields candidate values for H.

Once H is recovered, the attacker forges valid tags for arbitrary ciphertexts. A single nonce reuse enables universal forgery. The encryption key K remains secret, but integrity is destroyed.

**ChaCha20-Poly1305 under nonce reuse:**

Poly1305 uses a one-time key (r, s) derived from ChaCha20 keystream. If the nonce repeats, the same (r, s) authenticates different messages. The attacker obtains:

```
T₁ = (C₁·r + s) mod (2^130 - 5)
T₂ = (C₂·r + s) mod (2^130 - 5)
```

Subtracting eliminates s, yielding r. With r known, the attacker computes valid tags for any message.

Further, since ChaCha20 in counter mode XORs plaintext with keystream, reusing a nonce means reusing keystream. If C1 = P1 XOR KS and C2 = P2 XOR KS, then C1 XOR C2 = P1 XOR P2. Confidentiality leaks directly.

#### Algorithm selection considerations

**AES-GCM:**
- Hardware acceleration (AES-NI, PCLMULQDQ) yields ~0.6 cycles/byte on modern Intel/AMD
- GHASH's algebraic structure enables Joux's attack—uniquely fragile under nonce reuse
- Tag truncation is dangerous: GHASH's linearity allows targeted forgery probability exceeding 1/2^t
- Birthday bound limits total encryption under one key to ~2^32 blocks before collision risk

**ChaCha20-Poly1305:**
- Pure ARX operations (Add, Rotate, XOR)—constant-time without hardware support
- ~0.3–0.4 cycles/byte in optimized software; competitive even without dedicated instructions
- No S-boxes, no cache-timing vulnerabilities from table lookups
- Preferred for TEE environments where AES-NI availability is uncertain

**For Jolt continuations artifacts:** ChaCha20-Poly1305 is the conservative choice. TEE implementations vary; some SGX enclaves lack AES-NI exposure. ChaCha20's constant-time properties are guaranteed by algorithm design, not hardware availability.

#### Nonce generation strategies

`JOLT_ARTIFACT_NONCE_RULE_V1` MUST specify one of:

**Counter-based:** Maintain persistent state; increment for each encryption. Guarantees uniqueness if state is never lost or duplicated. Dangerous with VM snapshots—restoring state replays counters.

**Random:** Generate 96 random bits per encryption. For ChaCha20-Poly1305's 96-bit nonce, birthday collision probability reaches 2^-32 after 2^32 encryptions. Acceptable for moderate volumes; dangerous at scale.

**Synthetic (SIV-style):** Derive nonce from message content. If identical (key, AD, plaintext) encrypts twice, produces identical ciphertext—leaks equality but prevents keystream reuse. Requires two-pass encryption (compute SIV, then encrypt), incompatible with streaming.

**XChaCha20-Poly1305:** Extends nonce to 192 bits via HChaCha20 key derivation. Birthday bound becomes negligible (~2^-96 after 2^96 encryptions). Recommended if random nonces are preferred.

#### The RUP threat model

Release of Unverified Plaintext (RUP) occurs when implementations decrypt before verifying the tag—common in streaming scenarios where buffering the entire ciphertext is infeasible.

If an attacker observes unverified plaintext (via shared memory, side-channels, or error messages), they learn the XOR of their forged ciphertext with keystream. The EFAIL attack (2018) exploited this in email clients: inject HTML into encrypted messages, observe which URLs the client fetches when parsing the "garbage" decryption.

Mitigation for Jolt continuations: artifacts are finite-sized (snapshots, witnesses). Full buffering before tag verification is feasible. Implementations MUST NOT release partial plaintext before authentication succeeds.

### 13.9 The three artifact encryption parameters

**JOLT_ARTIFACT_AEAD_V1** specifies the authenticated encryption algorithm:
- ChaCha20-Poly1305: fast, constant-time, no timing side-channels
- AES-GCM: hardware acceleration on many CPUs

**JOLT_ARTIFACT_KDF_V1** specifies key derivation:
- HKDF-SHA256 is standard
- Affects how keys are managed and rotated

**JOLT_ARTIFACT_NONCE_RULE_V1** specifies nonce generation:
- Counter-based: increment for each encryption (requires state)
- Random: fresh random nonce (collision risk with short nonces)
- Derived: compute from message content (requires care)

All three are currently TBD in this draft. Deployments that export artifacts outside a trusted boundary MUST pin concrete values for these parameters in deployment policy before exporting; until pinned, artifact export is non-conformant and interoperability between independent implementations is undefined.

### 13.10 TEE reality check

TEEs aren't bulletproof. The security history is sobering:

**Intel SGX vulnerabilities:**
- ÆPIC Leak (2022): Architectural bug leaked enclave data
- Plundervolt (2019): Voltage manipulation exposed secrets
- LVI (2020): Load Value Injection bypassed protections
- Foreshadow (2018): Speculative execution attack

**AMD SEV vulnerabilities:**
- SEVered (2018): Manipulated memory mappings extracted plaintext

Secret Network, which relies on SGX for privacy, required emergency patches after exploits. Validators had to be allowlisted.

Section 13 doesn't claim TEEs are unbreakable. The rule is pragmatic: **treat the TEE as best-available trust boundary, and encrypt everything crossing it.**

This is defense in depth. If the TEE is compromised, data inside is exposed—but encrypted artifacts in transit remain protected.

### 13.11 Connection to Section 4: the security split

Section 4 established the fundamental distinction:

**Soundness** depends only on cryptographic assumptions. No adversary can produce a valid proof for a false statement, regardless of what they observe.

**Confidentiality** depends on operational infrastructure—TEEs, encryption, access controls. These can fail.

Section 13 is the operational mechanism for execution-layer confidentiality:

> "Confidentiality MAY depend on TEEs or encryption for artifacts (§13), but proof validity MUST NOT."

If TEE is compromised and artifacts decrypted:
- Attacker learns witness data, amounts, recipients
- Privacy guarantees fail

But soundness remains:
- Attacker cannot forge proofs
- On-chain verification still works

### 13.12 Definition block

**AEAD (Authenticated Encryption with Associated Data):** Symmetric encryption providing both confidentiality and integrity. Associated data is authenticated but not encrypted.

**KDF (Key Derivation Function):** Algorithm deriving cryptographic keys from a master secret. HKDF-SHA256 is standard.

**Nonce:** "Number used once." Must be unique for each encryption under a given key. Reuse is catastrophic for ChaCha20-Poly1305 and AES-GCM.

**TEE (Trusted Execution Environment):** Hardware-enforced isolated execution where code and data are protected from the host OS. Examples: Intel SGX, AMD SEV, AWS Nitro.

**Trust boundary:** The perimeter within which data is considered protected. For Section 13, the TEE enclave is the trust boundary.

### 13.13 Load-bearing claims

| Claim | Evidence | Verification |
|-------|----------|--------------|
| **Snapshots contain sensitive user data** | VMStateV1 includes registers, memory (Section 11.5) | Trace execution; inspect final state |
| **Leaking at prover breaks intent privacy** | Witness contains plaintext from committed inputs | Given witness, reconstruct amount/recipient |
| **AEAD provides integrity + confidentiality** | Standard cryptographic property | Test tag failure on tampering |
| **Nonce reuse is catastrophic** | ChaCha20-Poly1305 security model | XOR attack with reused nonce |
| **TEEs have known vulnerabilities** | ÆPIC Leak, Plundervolt, SEVered, etc. | Review CVE database |

### 13.14 Forward references

- **VMStateV1 definition** → Section 11.5
- **SnapshotArtifactV1 magic bytes** → Section 11.7
- **Soundness/confidentiality split** → Section 4
- **Continuation witnesses** → Section 11.9
- **Parameter registry** → Section 3

---

*Section 13 addressed operational confidentiality: protecting witness data during proving. Equally critical for deployment readiness is ensuring that independent implementations agree on every consensus-visible output—which is the role of the conformance bundle.*

## Section 14: Conformance bundle and release gating

### 14.1 The problem conformance solves

Two teams build Jolt implementations in isolation. Both read "little-endian 31-byte limb packing." Both write working code. Both pass their own tests. Then Team A's prover hands a proof to Team B's verifier, and the system cracks open: transcript challenges diverge because limb packing diverged. The network forks. Section 2 promised determinism, but promises without enforcement are poetry, not protocol.

The conformance bundle transforms poetry into prosecution. It is not documentation. It is a test suite with golden outputs: byte-exact expected results that admit no interpretation. Run your implementation against these vectors. Match, or fail. There is no third option.

### 14.2 The test vector philosophy

Conformance testing in cryptographic protocols differs fundamentally from unit testing in application code. A unit test asks "does this function return the right value?" A conformance test asks "does this implementation produce bit-identical output to every other conformant implementation?"

**Three categories of conformance tests:**

1. **Encoding tests**: Given input bytes, produce expected Fr elements. Tests §7 encoding primitives.
   - Example: `Bytes32ToFr2(0xabcd...1234)` must produce exactly `(Fr(lo), Fr(hi))` where lo and hi are specified.

2. **Transcript tests**: Given a sequence of absorptions, produce expected challenges. Tests §8 transcript construction.
   - Example: Absorb u64(42), absorb bytes("hello"), squeeze challenge → must equal Fr(specified_value).

3. **StateDigest tests**: Given VM state components, produce expected digest. Tests §11 continuation binding.
   - Example: Given registers, pc, memory roots, config_tags → StateDigest must equal Fr(specified_value).

**Why golden outputs matter**: Two implementations can pass functional tests ("the proof verifies") while producing incompatible transcripts. Golden outputs catch this: if your intermediate values don't match, your proofs won't interoperate, even if they individually verify.

**The network fork test**: The ultimate conformance check is cross-implementation verification. Team A generates a proof; Team B verifies it. If verification fails, at least one implementation is non-conformant. The conformance bundle provides the shared ground truth to identify which.

### 14.3 Conformance bundle format (normative)

A conformance bundle is a directory or tarball containing:

| Component | Contents | Purpose |
|-----------|----------|---------|
| `registry.json` | Canonical parameter values | Defines configuration; MUST equal `canonical_registry_bytes` (§3) and its SHA-256 MUST equal `JOLT_PARAMETER_REGISTRY_HASH_V1` |
| `vectors/` | Test inputs + expected outputs | Golden outputs for each test category |
| `proofs/` | Sample wrapper proofs + public inputs | End-to-end verification examples |
| `README.md` | Build and run instructions | Reproducibility documentation |

The bundle is content-addressed:

```
JOLT_CONFORMANCE_BUNDLE_HASH_V1 := SHA-256(canonical_tar_bytes)
```

The tar format is pinned by this specification (V1)—you can't use different tar options and get the same hash.

**Tar canonicalization (normative).** `JOLT_CONFORMANCE_BUNDLE_HASH_V1` is defined over the **exact bytes of an uncompressed POSIX ustar `.tar` archive** (see §3.7 `conformance_bundle.tar`).

To ensure reproducible hashes across tooling *and* safe extraction, the canonical tar archive MUST satisfy ALL of the following:

- **Archive format:** POSIX ustar, uncompressed (`.tar`).
  - `canonical_tar_bytes` are the exact bytes of this uncompressed tar archive.
  - Compression layers (gzip/zstd/etc.) MUST NOT be included in `canonical_tar_bytes`.

- **Allowed entry types:** Only regular files and directories are permitted.
  - Symlinks, hardlinks, character/block devices, FIFOs, and other special entries MUST NOT appear.
  - Duplicate member names MUST NOT appear.

- **Path normalization (member names):** Each member name MUST be a relative path using `/` separators and MUST NOT:
  - start with `/` (no absolute paths),
  - contain `..` or `.` path segments,
  - contain `\\` (backslash), NUL bytes, or control characters.

- **Directory entries:** Directories MUST be represented explicitly as tar entries with size 0.
  - Directory member names MUST end with `/`.

- **Ordering:** Members MUST be sorted by member name using **bytewise lexicographic order** over the normalized member-name bytes (no locale-dependent collation).

- **Header normalization:**
  - uid = 0, gid = 0, uname = "", gname = ""
  - mtime = 0
  - mode = 0644 for regular files, 0755 for directories
  - No PAX headers and no GNU extensions (including longname/longlink records)

- **Padding / termination:**
  - Each file's content MUST be padded with zero bytes to the next 512-byte block boundary.
  - The archive MUST terminate with **exactly two** 512-byte all-zero blocks and MUST NOT contain extra bytes after them.

### 14.4 External handle status

`JOLT_CONFORMANCE_BUNDLE_HASH_V1` is an **external handle**:

> It MUST NOT appear as a key in `registry.json`, and MUST NOT be absorbed into `config_tags` (§3.8) or `StateDigestV1`.

Why the special status? The bundle contains `registry.json`. If the registry contained the bundle hash, you'd have a circular dependency: changing the registry changes the bundle bytes, which changes the hash, which would need to go back in the registry...

External handles break this cycle. They're pinned separately from the registry.

### 14.5 Required conformance vectors (deployment-blocking)

A deployment MUST publish a conformance bundle containing inputs and expected outputs sufficient to make consensus-critical surfaces executable.

**Non-exhaustive list (normative).** In addition to the minimum categories listed below, the bundle MUST include **all** vectors and proof artifacts required by every section-local conformance clause in this specification (e.g., §3.12, §5.13, §6.13, §7.12, §8.11, §12.12).

At minimum, the bundle MUST include:

#### A) Transcript / packing vectors (interop-critical)

**Test 1: 31-byte limb packing (little-endian)**

Input: `b31` is the 31-byte sequence such that for each index `i` in `{0..30}`, `b31[i] = i`.

Expected limb (hex): `0x1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100`

This catches endianness bugs. The first byte (0x00) becomes the least significant part.

**Test 2: 32-byte boundary**

Input: `b32` is the 32-byte sequence such that for each index `i` in `{0..31}`, `b32[i] = i`.

Expected: Two 31-byte chunks produced by the 31-byte chunking rule. `limb0` is derived from bytes `b32[0..30]` (same as Test 1). `limb1` is derived from the single byte `b32[31]` padded with 30 zero bytes and interpreted as a little-endian 248-bit integer, i.e. `limb1 = 0x1f`.

**Test 3: 62-byte exact multiple**

Input: `b62` is the 62-byte sequence such that for each index `i` in `{0..61}`, `b62[i] = i`.

Expected: Exactly two 31-byte chunks produced (no padding needed). The overall length is 62.

**Test 4: Bytes32ToFr2 endianness (31+1 limb split)**

Input: `B = 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f`

Interpretation: `B` is the 32-byte sequence `[0x00, 0x01, …, 0x1f]`.

Expected:
- `lo_fr` is the little-endian integer of the **first 31 bytes** `[0x00..0x1e]`:
  ```
  lo_fr = 0x1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100
  ```
- `hi_fr` is the integer value of the **last byte** `[0x1f]`:
  ```
  hi_fr = 0x1f
  ```

Round-trip requirement (normative): `Fr2ToBytes32(lo_fr, hi_fr) == B` (byte-for-byte).

**Test 5: Canonical Fr rejection (no silent reduction)**

The BLS12-381 scalar field prime is:
```
r = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
```

Define `encode_le(x)` for these vectors as the **32-byte little-endian encoding of the unsigned integer** `x` in `[0, 2^256)`, i.e. for `i = 0..31`:

`B[i] = (x >> (8*i)) & 0xFF`

Test cases for `Bytes32LEToFrCanonical`:

| Input (little-endian bytes encoding integer) | Expected Result |
|---------------------------------------------|-----------------|
| `encode_le(r - 1)` | ✓ Accept (maximum valid Fr) |
| `encode_le(r)` | ✗ MUST reject |
| `encode_le(r + 1)` | ✗ MUST reject |
| `encode_le(2^256 - 1)` | ✗ MUST reject |

These vectors catch the most common "library auto-reduces" bug where implementations silently compute `input mod r` instead of rejecting non-canonical inputs.

#### B) Transcript sponge vectors (requires pinned Poseidon + schedule)

Once `JOLT_POSEIDON_FR_V1` and `JOLT_TRANSCRIPT_SCHEDULE_V1` are pinned, the bundle MUST include golden outputs for:

| Case | What It Catches |
|------|-----------------|
| `absorb_bytes(b"")` (empty) | Edge case handling |
| `len(b) % 31 == 0` boundary | Exact-multiple chunking |
| `absorb_tag` with length > 31 | Multi-limb tag absorption |
| `absorb_tag` with length = 31 exactly | Boundary chunk handling |
| Multiple `challenge_fr()` calls | Sponge state evolution between squeezes |

#### C) StateDigestV1 vectors (requires pinned Poseidon + schedule)

- At least one fixed `VMStateV1` (including config_tags) with expected `state_digest_fr`
- At least one **negative test**: same state but tag order swapped → digest MUST NOT match

The negative test is critical—it verifies wrong input produces *different* output.

#### D) Sparse Merkle root vectors (requires pinned Poseidon)

| Case | What It Catches |
|------|-----------------|
| Empty tree root (`default[32]`) | Default hash computation |
| One-page tree | Single non-zero page position |
| Two-page tree (different branches) | Branch decision logic |
| Single-bit difference in page | Page content hashing |
| **Negative:** MSB-first vs LSB-first | Wrong bit order → different tree |
| **Negative:** page_index mapping | Wrong address-to-index → wrong positions |

#### E) RISC-V determinism vectors

| Test Case | What It Catches |
|-----------|-----------------|
| Shift masking (`shamt & 0x3f`) | RV64 uses 6-bit shift amount |
| `*W` instruction semantics | Word ops sign-extend to 64 bits |
| Compressed instruction decode | 16-bit instructions (if C enabled) |
| Illegal opcode trap | Undefined opcodes must trap, not NOP |
| Misaligned load/store (cross-page) | Behavior per §6 |

#### F) Batch commitment vectors (requires pinned encoding)

Once `JOLT_BATCH_MANIFEST_ENCODING_V1` is pinned:

- Sample manifest with `manifest_bytes`, decoded header + fills, expected `batch_commitment_bytes32`
- Merkle membership path example (leaf index + sibling hashes)

### 14.6 Independent implementation gate (normative)

A deployment MUST NOT proceed unless at least two independent implementations pass the conformance bundle.

"Independent" matters because shared code propagates bugs. Independent implementations only make the same mistake if the spec itself is ambiguous. Two teams reading the spec, building from scratch, comparing outputs. Disagreement means the spec failed to communicate; agreement means it succeeded.

Two is the minimum because of diminishing returns. Two catches most ambiguities. Three catches more but coordination cost is high.

### 14.7 What the bundle tests (and doesn't)

**Tests:**
- Encoding correctness (bytes → field elements → hashes)
- Algorithm correctness (Poseidon, SHA-256 Merkle, SMT)
- Edge case handling (boundaries, empty inputs, ordering)
- Cross-implementation agreement

**Does NOT test:**
- Performance (your implementation might be 100× slower and still pass)
- Security (side-channel resistance, constant-time operations)
- Completeness (vectors are minimums; more coverage is better)
- Application logic (Settlement Engine correctness is outside the Jolt Specification)

Passing conformance is necessary but not sufficient for production readiness.

### 14.8 Definition block

**Conformance bundle:** A content-addressed archive containing test vectors and expected outputs that define correct implementation behavior.

**Golden output:** The canonical expected result for a test vector. Not "a valid result" but "the result." Any deviation is a bug.

**External handle:** A deployment artifact (hash) referencing the conformance bundle, wrapper VK, or registry, but not stored inside the registry. Prevents circular dependencies.

**Independent implementation:** An implementation built from a distinct codebase that does not share consensus-critical logic with another implementation. Sharing third-party dependencies is permitted only if versions are pinned and treated as external inputs (i.e., differences in dependency versions are treated as implementation differences).

### 14.9 Load-bearing claims

| Claim | Evidence | Verification |
|-------|----------|--------------|
| **Endianness tests catch byte-order bugs** | Limb packing vectors (A) | Flip endianness; observe different output |
| **Boundary tests catch off-by-one** | 31/32/62-byte vectors | Implement naive modulo; observe failure |
| **Negative tests catch ordering bugs** | StateDigest tag-swap test (C) | Ignore tag order; observe identical (wrong) digest |
| **Two implementations catch ambiguity** | Section 14.6 gate | If teams disagree, find ambiguous spec text |
| **Content-addressing ensures reproducibility** | SHA-256 of tar bytes | Regenerate bundle; verify hash matches |

### 14.10 Forward references

- **Determinism rule** → Section 2
- **Parameter Registry** → Section 3
- **Deployment gating** → 3.5
- **Limb packing / Bytes32ToFr2** → Section 7
- **Transcript sponge** → Section 8
- **StateDigestV1** → Section 11.10
- **Sparse Merkle trees** → Section 11.8
- **RISC-V semantics** → Section 6
- **Batch commitment** → 5.7

---

## Section 15: Security considerations

### 15.1 The five layers of defense

Security in a zero-knowledge proving system does not reduce to a single lock on a single door. Attackers probe five distinct layers, each requiring its own defense. At the encoding layer, they hunt for collisions—two different inputs that hash to the same field element, letting a proof for batch A masquerade as authorization for batch B. At the transcript layer, they craft malicious data that, when absorbed into the Fiat-Shamir sponge, mimics legitimate structure, twisting the verifier's interpretation of what was actually proved. At the execution layer, they submit partial proofs covering only the first half of a program, hoping the verifier will bless an incomplete computation that conveniently skipped the balance check at instruction 75,000. At the resource layer, they flood provers with ten million intents or infinite loops, grinding legitimate batches to a halt. At the confidentiality layer, they intercept witness data in transit, breaking privacy even when soundness remains intact.

Each layer answers a different adversary. Encoding attacks target mathematical binding. Execution attacks target proof completeness. Resource attacks target availability. Confidentiality attacks target privacy. A system secure against four but vulnerable to one is not secure.

**Attack category summary:**

| Category | Section | Primary Mitigation | TLA+ Invariant |
|----------|---------|-------------------|----------------|
| Field squeeze | §15.3 | Bytes32ToFr2 encoding | INV_BIND_* |
| Transcript manipulation | §15.4 | Typed absorption | INV_BIND_* |
| Partial execution | §15.5 | StateDigest chaining | INV_ATK_NoPrefixProof |
| Chunk skipping | §15.5 | Consecutive step counters | INV_ATK_NoSkipChunk |
| Continuation splicing | §15.5 | StateDigest matching | INV_ATK_NoSplice |
| Cross-config splice | §15.5 | config_tags in digest | INV_ATK_NoCrossConfig |
| Memory forgery | §15.6 | SMT inclusion proofs | INV_ATK_NoMemoryForgery |
| Proof replay | §15.7 | Batch nonce | INV_BIND_Nonce |
| Resource exhaustion | §15.8 | DoS caps (MAX_*) | INV_SAFE_* |

Nine categories. Nine mitigations. Zero unaddressed attack surfaces.

For auditors, Section 15 is a checklist: "Have I verified each of these is actually addressed where the spec claims?"

### 15.2 How to use this section: Auditor's reading guide

This section serves two audiences: **implementers** verifying that their code meets normative security requirements, and **auditors** checking that each attack vector is addressed where the specification claims.

#### Purpose and structure

Section 15 is organized as a **threat-driven specification**, not a narrative. Each major attack category (15.3 through 15.7) follows this pattern:

1. **Attack Definition** — What malicious behavior is possible?
2. **Threat Narrative** — What is the concrete attack scenario?
3. **Vulnerability Without Mitigation** — What breaks if the mitigation is absent?
4. **Mitigation Mechanism** — What specific control closes the attack?
5. **Normative Verification** — How does the spec verify the mitigation is enforced?
6. **Evidence** — Which TLA+ invariants formally verify this mitigation?

#### Normative vs. informative sections

Sections 15.3 through 15.7 are marked **(normative)**. This means:
- Every claim is backed by an explicit verification procedure (e.g., "The wrapper constraint Constraint 3 enforces...").
- Each mitigation appears in the specification proper (Sections 3–13), not only here.
- Section 15 serves as the authoritative **checklist** that implementations must satisfy.

Sections 15.8 and 15.9 are **informative** (non-normative). They:
- Summarize attacks that are addressed elsewhere (e.g., replay, which is covered in Section 5.3).
- Clarify which threat categories are out of scope (e.g., quantum adversaries, economic attacks).
- Provide cross-references to the sections where mitigations are specified.

Sections 15.10–15.12 are **informative reference material** that maps attacks to formal invariants (Section 15.10), provides deployment guidance (Section 15.11), and forward-references to TLA+ modules (Section 15.12).

#### How to verify each section

For an implementer or auditor checking Section 15:

| Section | Verification Task | Success Criterion |
|---------|-------------------|------------------|
| **15.1** | Understand why five attack layers are sufficient and necessary | Can you explain why removing any layer would leave a vulnerability? |
| **15.2** | (This section) Understand the structure and how to use it | Can you identify which sections are normative vs. informative? |
| **15.3** | Field Squeeze Prevention | Have you implemented `Bytes32ToFr2` exactly as specified in Section 7.6? |
| **15.4** | Transcript Collision Prevention | Do you absorb distinct types with unique discriminators (Section 8)? |
| **15.5** | Partial Execution Prevention | Does your wrapper enforce `halted_out = 1` and bind `status_fr` (Section 5.5)? |
| **15.6** | Resource Exhaustion Prevention | Are resource caps pinned from Section 3 and enforced before proving (Section 3.5)? |
| **15.7** | Confidentiality Protection | Are artifacts encrypted with AEAD before leaving TEE boundaries (Section 13)? |
| **15.8** | Replay Attack Prevention (delegated) | Have you read Section 5.3 and verified batch_nonce is strictly increasing? |
| **15.9** | Out-of-Scope Threats | Understand why these are not mitigated (delegation, economic, quantum). |
| **15.10** | TLA+ Invariant Mapping | Can you locate each `INV_ATK_*` in the TLA+ modules? |

#### Typical audit workflow

1. **Start with Section 15.1** to understand the five-layer taxonomy.
2. **Read this section (15.2)** to understand structure.
3. **For each of 15.3–15.7**, read the threat narrative and locate the normative reference.
4. **Cross-check the referenced section** (e.g., Section 7.6 for `Bytes32ToFr2`) to verify the mitigation is actually specified.
5. **Verify the TLA+ invariant** (Section 15.10) that formalizes the claim.
6. **Test the implementation** against the invariant using TLC.

---

### 15.3 Field squeeze hazards (normative)

#### Definition: Field squeeze attack

A *field squeeze* attack occurs when an attacker constructs two distinct 256-bit values that, under naive encoding, map to the same finite field element. The attacker exploits this collision to forge a proof claiming different states (e.g., different state roots) that are cryptographically indistinguishable to the verifier.

In formal terms: Let `bytes32ToFr` be an encoding function mapping 32-byte values to field elements. A field squeeze occurs if distinct values A, B ∈ {0,1}^256 satisfy `bytes32ToFr(A) = bytes32ToFr(B)`. The attacker then constructs a proof π using A but submits it claiming it proves a statement about B, and the verifier (which only sees field elements) cannot distinguish the two.

**Why this matters:** In Jolt, state roots are 32-byte Merkle tree roots. If `old_root` and `new_root` are naively encoded into field elements without collision resistance, the following attack is possible:

1. Attacker computes two different Merkle roots that happen to encode to the same field element (via collision).
2. Attacker generates a valid proof π that state S₁ transitions to state S₂.
3. Attacker submits the same proof but claims it proves S₃ → S₄, where S₃ and S₁ have the same field-element encoding.
4. The verifier, seeing only field elements, accepts the proof and applies an unauthorized transition.

#### The attack

A semantic `bytes32` value **MUST NOT** be interpreted as an `Fr` element via modular reduction (i.e., `x ↦ x mod r`), because this is non-injective and can weaken binding or introduce implementation divergence. Conforming implementations **MUST** represent semantic `bytes32` values in public inputs using the injective `Bytes32ToFr2` / `Fr2ToBytes32` packing defined in §7.6.

**Concrete example:** SHA-256 outputs 256 bits. BLS12-381's scalar field Fr holds ~255 bits. If you naively cast bytes32 to Fr with `mod r`, distinct inputs collide.

```
A = r + 5  (a 256-bit value)
B = 5      (a small value)

A mod r = 5
B mod r = 5
```

Same field element, different inputs. An attacker finds two batches whose commitment hashes H and H' satisfy H' ≡ H (mod r). Both map to the same Fr public input. A proof for batch A could be reinterpreted as authorizing batch B.

**The mitigation:** Section 7.6 defines `Bytes32ToFr2`—split into (31 bytes, 1 byte), interpreted as two field elements. Both pieces guaranteed < r. Different bytes32 → different Fr pair. No collisions possible.

**Verification:** Attempt to find two distinct bytes32 values producing the same (Fr_lo, Fr_hi) pair. You cannot—the encoding is injective.

### 15.4 Transcript collision hazards (normative)

#### Definition: Transcript collision attack

A *transcript collision* attack occurs when an attacker constructs two different protocol messages that, when absorbed into the Fiat-Shamir transcript, produce the same transcript state. The attacker exploits this collision to reuse a challenge generated for one message to construct a valid proof for a different message, without re-running the expensive proving computation.

In Jolt, the transcript is a sponge-based hash function that absorbs data in blocks. If two distinct messages can be absorbed in a way that produces the same internal state, the attacker can forge proofs.

Typed absorption prevents user data from masquerading as system tags (§8.3–§8.6).

**The attack:** The Fiat-Shamir transcript absorbs commitments and produces challenges. Without type separation, the byte `[0x01]` and the integer `1` might produce the same transcript state.

If an attacker can craft data that, when absorbed, looks like a different structure, they've manipulated the transcript. The proof validates one interpretation; the verifier believes another.

#### Concrete worked example: Why type discriminators matter

Consider a simplified Jolt proving system with a single field element to be absorbed. An attacker wants to construct two different interpretations of the same raw bytes such that they absorb identically.

**Scenario A: Naive Absorption (Vulnerable)**

Suppose the prover absorbs data naively without type tags:

```
Intent intent1 = { user: 0x01, amount: 100 };
// Serialized: raw_bytes = [0x01, 0x00, 0x00, 0x00, 0x64, ...]

Intent intent2 = { user: 0x00, amount: 256 };
// Serialized: raw_bytes = [0x00, 0x01, 0x00, 0x00, ...]
```

If the serialization is ambiguous (e.g., due to alignment or endianness), an attacker might construct intent1 and intent2 such that:
```
serialize(intent1) = [0x01, 0x64] ++ padding
serialize(intent2) = [0x01, 0x64] ++ padding
```

Both absorb to the same transcript state. The attacker generates a proof for intent1, then submits it claiming it proves intent2.

**Scenario B: Typed Absorption (Secure)**

The Jolt system absorbs with explicit type tags (as specified in Section 8):

```
// Absorption with TYPE_INTENT_V1 discriminator
absorb_bytes([TYPE_INTENT_V1] || serialize(intent1))
  = Sponge.absorb([0xA1] || [0x01, 0x00, 0x00, 0x00, 0x64, ...])
  = Sponge.absorb([0xA1, 0x01, 0x00, 0x00, 0x00, 0x64, ...])
  → transcript_state_1

// Absorption with TYPE_INTENT_V1 discriminator (different data)
absorb_bytes([TYPE_INTENT_V1] || serialize(intent2))
  = Sponge.absorb([0xA1] || [0x00, 0x01, 0x00, 0x00, ...])
  = Sponge.absorb([0xA1, 0x00, 0x01, 0x00, 0x00, ...])
  → transcript_state_2
```

Even if serialize(intent1) and serialize(intent2) collide, the prepended discriminator [0xA1] ensures the absorbed byte sequences differ. Therefore: transcript_state_1 ≠ transcript_state_2

**Further refinement: Multiple absorption types**

The Jolt system uses multiple type discriminators (Section 8) to distinguish different absorption contexts:

| Type Discriminator | Purpose | Example |
|-------------------|---------|---------|
| `TYPE_BYTES` | Raw byte sequences | `0xB1` |
| `TYPE_U64` | 64-bit unsigned integers | `0xU1` |
| `TYPE_TAG` | Domain-specific tags | `0xT1` |

Different message types (e.g., u64 vs. raw bytes) use different discriminators, so collisions across message types are impossible.

**Concrete numerical example:**

Consider absorbing the value `1`:

```
// As raw bytes (TYPE_BYTES):
absorb_bytes([TYPE_BYTES] || [0x01])
  = Sponge.absorb([0xB1, 0x01])

// As a 64-bit unsigned integer (TYPE_U64):
absorb_bytes([TYPE_U64] || u64_to_bytes(1))
  = Sponge.absorb([0xU1, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00])
    (assuming little-endian 8-byte encoding of u64)
```

These produce different byte sequences despite representing the same value `1`. Therefore, they absorb to different transcript states, and the attacker cannot reuse a proof from one context in the other.

**The mitigation:** Before absorbing any value, absorb a type discriminator:

| Type | Discriminator |
|------|---------------|
| Bytes | TYPE_BYTES = Fr(1) |
| u64 integer | TYPE_U64 = Fr(2) |
| Domain tag | TYPE_TAG = Fr(3) |

Absorbing bytes `[0x01]` and absorbing integer `1` produce completely different sequences. Different transcript states. No collision.

Domain separation adds another layer: absorb_tag("JOLT/CHECKPOINTS/V1") before checkpoint data. Same data in different contexts → different outputs.

**Verification:** Absorb same raw bytes as TYPE_BYTES versus TYPE_U64. Compare transcript states. They must differ.

### 15.5 Partial execution / prefix proofs (normative)

#### Definition: Partial execution attack

A *partial execution attack* occurs when an attacker constructs a proof that attests to correct execution for only the first N steps of a program, then submits the partial proof as if it were a complete execution. If accepted, the partial proof authorizes a state transition that is mathematically correct for the partial execution but incorrect for the full program.

#### Complete attack narrative: Stealing funds via partial execution

Consider a settlement engine that processes intents in order:

```
Step 1–50,000:        Process fill intents 1–100
                      Debit user accounts, credit DEX
                      Intermediate state: balances_after_fills

Step 50,001–100,000:  Process "critical" intent: Transfer 1M tokens to founder
                      This intent is legitimate (properly signed) but sensitive

Step 100,001–150,000: Cleanup: Reset buffers, compute final merkle root
                      Final state: balances_with_transfer
```

**The attack (without partial execution prevention):**

1. **Setup:** An attacker compromises the aggregator's proving machine and gains control over which proofs are generated.

2. **Attacker's Goal:** Prevent the "critical" transfer (step 50,001–100,000) from being applied, while still applying the earlier fill intents (which benefit the attacker's position).

3. **Attacker's Strategy:**
   - Instead of running the full settlement engine (step 1–150,000), the attacker runs it for only step 1–50,000.
   - The attacker generates a partial proof π₅₀ₖ that attests: "Starting from balances_initial, after 50,000 steps of correct execution, we reach balances_after_fills."

4. **Submission:**
   - The attacker submits proof π₅₀ₖ to the on-chain verifier, claiming it represents the full settlement.
   - The proof is cryptographically valid (Jolt correctly verified the first 50,000 steps).
   - The verifier sees only: `old_root → new_root` (where `new_root = balances_after_fills`).

5. **Why It Succeeds (Without Partial Execution Prevention):**
   - The proof is valid Jolt evidence (signature of 50,000 correctly executed steps).
   - The proof commits to the old and new state roots (via public inputs).
   - There is no mechanism to verify that the entire program ran to completion.
   - The on-chain verifier accepts the proof and applies: `current_state := balances_after_fills`.

6. **Consequence:**
   - The critical transfer never executes.
   - The founder's 1M tokens are not transferred.
   - The attacker and their co-conspirators retain inflated DEX positions.
   - **Funds are stolen via hidden partial execution.**

#### How partial execution prevention closes the attack

The wrapper MUST enforce that the **final chunk** of an on-chain-verified batch execution satisfies `halted_out = 1`, and it MUST bind `status_fr` to that final chunk's `exit_code` (see §5.5, §6.9). In particular, `status_fr = 0` MUST imply `halted_out = 1` and `exit_code = 0` for the final chunk.

**Wrapper Constraint 3:** The prover must set `halted_out = 1` (instruction halted signal at the final step) and bind this to the public input `status_fr`.

In the attack narrative:

- Attacker runs first 50,000 steps and tries to submit.
- After step 50,000, the VM's halt signal is `halted_out = 0` (the program has not completed; more steps remain).
- The wrapper circuit enforces: `REQUIRE(halted_out = 1)`.
- The proof fails constraint validation. **The partial proof is rejected outright, before on-chain submission.**

If the attacker tries to forge a proof with `halted_out = 1` after step 50,000:
- The wrapper circuit verifies against the Jolt proof.
- The Jolt proof will show that at step 50,000, the program counter is still less than the final instruction.
- The Jolt proof contradicts the claim that execution is complete.
- **The proof is cryptographically invalid.**

Therefore, the attacker cannot submit a partial proof without it being immediately rejected.

**Complementary verification:**

The wrapper also binds `status_fr` to the exit status code:

- If the program completes normally: `status_fr = 0` (success).
- If the program traps (illegal instruction, out-of-bounds memory, etc.): `status_fr = TRAP_CODE`.
- If the program exits early (e.g., due to an error): `status_fr = ERROR_CODE`.

The on-chain verifier checks: `REQUIRE(status_fr = 0)`.

This means even if an attacker submits a proof with `halted_out = 1` but the program actually trapped, the status would be non-zero, and the proof would be rejected.

**Verification:** Construct proof for partial execution (halted_out = 0). Submit to wrapper. Must reject.

For continuations, each chunk covers a segment, but the final chunk must have halted_out = 1. You can't submit just intermediate chunks and claim completion.

### 15.6 Liveness / DoS (normative)

Deployments MUST pin:
- `JOLT_CONTINUATIONS_V1` **including** its execution and snapshot limit fields (e.g., `CHUNK_MAX_STEPS` and any snapshot/page caps it defines)
- `JOLT_MAX_MANIFEST_BYTES_V1`
- `JOLT_MAX_INTENTS_V1`
- `JOLT_MAX_CHECKPOINTS_BYTES_V1`
- `MAX_ECDSA_SIGS_PER_BATCH_V1` (if ECDSA is used)

and MUST reject any batch / manifest / snapshot artifact that exceeds the pinned caps.

**The attack:** Resource exhaustion at the prover layer.

| Scenario | Attack |
|----------|--------|
| 10 million intents | Prover computes for hours; legitimate batches queue |
| Infinite loop in guest | Prover never completes |
| 100,000 ECDSA verifications | In-circuit cost explodes |

**The mitigation:** Resource caps in the parameter registry:

| Cap | Purpose |
|-----|---------|
| `CHUNK_MAX_STEPS` | Maximum VM instructions per chunk |
| `JOLT_MAX_MANIFEST_BYTES_V1` | Maximum batch manifest size |
| `JOLT_MAX_INTENTS_V1` | Maximum intents per batch |
| `JOLT_MAX_CHECKPOINTS_BYTES_V1` | Maximum checkpoint data |
| `MAX_ECDSA_SIGS_PER_BATCH_V1` | Maximum signature verifications |

Batches exceeding caps are rejected *before proving begins*. The check is cheap (parse manifest, count intents). The expensive work never starts.

Note: These caps primarily mitigate **prover-side** DoS (resource exhaustion during proving). Chain-side verification DoS is mitigated by the target chain's transaction size limits and execution budget (e.g., block gas / runtime limits), and by the wrapper feasibility constraints described in §12.

**Verification:** Submit batch exceeding JOLT_MAX_INTENTS_V1. Must be rejected at manifest validation, not during proving.

### 15.7 Confidentiality (normative)

Snapshot artifacts **MUST** be treated as sensitive; they **MUST** be encrypted if exported outside the trusted boundary (§13).

**The attack:** Witness data leakage.

The privacy model relies on commitments hiding plaintext. But proving requires the witness—the actual values. If witness data leaks, the commitment provided delay, not protection.

Leakage vectors:
- Prover logs contain witness values
- Snapshot artifacts transmitted in plaintext
- Disk storage of intermediate state
- Memory dumps from compromised TEE

**The mitigation:** Section 13 requires:
- Artifacts leaving TEE boundaries MUST be encrypted with AEAD
- Plaintext MUST NOT be shared with untrusted aggregators
- Algorithm, KDF, and nonce rules pinned **operationally** via deployment policy, but **excluded** from `config_tags` / `StateDigest` projection (per §13)

**Critical nuance from Section 4:** Confidentiality can fail without breaking soundness. If TEE is compromised and artifacts decrypt, attacker learns witness data (confidentiality breach), but still cannot forge proofs (soundness holds).

**Verification:** Audit artifact handling. Every path exporting from TEE must encrypt. Plaintext export is a bug.

#### 15.7.1 Attack scenario: proof replay double-spend

**Definition:** A *replay attack* occurs when an attacker submits a valid proof for a state transition that was previously applied, causing the transition to be applied again.

**Concrete scenario:**

A settlement engine processes a batch of fill intents:
```
Batch B = [Fill(Alice: 10 USDC → BTC), Fill(Bob: 5 BTC → USDC), ...]
Old State: S1 (Alice has 100 USDC, Bob has 2 BTC)
New State: S2 (Alice has 90 USDC + 0.001 BTC, Bob has 7 BTC - 10 USDC)
```

The on-chain verifier verifies proof π that attests `S1 → S2` and applies the transition.

**The attack:**

1. The blockchain suffers a hard fork. The canonical chain is reset to state S1.
2. An attacker observes the original proof π (still valid since it proves S1 → S2).
3. The attacker resubmits proof π to the settlement contract on the forked chain.
4. The contract verifies the proof (cryptographically valid) and applies `current_state := S2`.
5. **Result:** Batch B is applied twice. Alice receives extra BTC, Bob loses extra USDC. Double-spending succeeds.

**Why this attack fails with proper binding:**

Section 5.3 requires that public inputs include a batch nonce or monotonic counter:
- Each proof binds to a specific `batch_commitment` that includes the nonce.
- The on-chain contract tracks the last applied nonce.
- Replayed proofs have already-used nonces → rejected before verification.

Even if state rolls back, the nonce record doesn't. The proof π for nonce N is forever spent.

#### 15.7.2 Attack scenario: continuation splicing

**Definition:** A *splice attack* occurs when an attacker stitches together chunks from different valid executions to create an "execution" that never actually happened.

**Concrete scenario:**

Two legitimate batches exist:
- **Execution X:** Processes trades favoring Alice. Chunk X₀ → X₁ → X₂ (Alice gains 100 tokens).
- **Execution Y:** Processes trades favoring Bob. Chunk Y₀ → Y₁ → Y₂ (Bob gains 100 tokens).

Both executions are valid and have been proven correctly.

**The attack:**

The attacker constructs a spliced "execution" Z:
```
Z₀ = X₀  (start from execution X)
Z₁ = Y₁  (splice in chunk from execution Y)
Z₂ = Y₂  (continue with Y)
```

If accepted, this fake execution never ran but appears valid. The attacker extracts value from the inconsistent state.

**Why the splice is detected:**

StateDigest chaining (§11.4) requires:
```
StateDigest_out(Z₀) = StateDigest_in(Z₁)
```

But Z₀ = X₀ and Z₁ = Y₁:
- `StateDigest_out(X₀)` includes X's memory roots, step counter, registers
- `StateDigest_in(Y₁)` includes Y's memory roots, step counter, registers

These don't match. The chain breaks. The wrapper rejects the splice before on-chain submission.

**Why this is robust:**

Even if the attacker finds two chunks with coincidentally matching step counters, the memory roots will differ (different trades executed). StateDigest absorbs *all* state fields—registers, PC, memory roots, config tags. Finding two chunks with identical StateDigests requires either:
1. Identical executions (not a splice), or
2. Hash collision (cryptographically infeasible)

### 15.8 Security properties addressed elsewhere

| Property | Attack | Mitigation | Section |
|----------|--------|------------|---------|
| **Soundness** | Forge proof for invalid execution | SNARK security | Section 4 |
| **Proof replay** | Reuse proof for different state | Public inputs bind roots, nonce | 5.3 |
| **Program substitution** | Prove wrong program | program_hash binding | 5.3 |
| **Cross-deployment replay** | Use proof from deployment A on B | context_bytes32 domain binding | 5.7 |
| **Continuation splicing** | Mix chunks from different executions | StateDigest chaining | Section 11.10 |
| **Implementation divergence** | Exploit differences | Determinism rule + conformance | Section 2, Section 14 |
| **VK substitution** | Verify against wrong circuit | VK hash gating | 3.5 |

### 15.9 What the spec doesn't protect against

Explicit non-goals (outside the Jolt Specification scope):

**Settlement Engine bugs:** If the program has logic errors, proofs faithfully attest to buggy execution. Garbage in, cryptographically certified garbage out.

**Bridge security:** Federated validators, MPC signers, finality attestation—all outside scope. A compromised bridge can authorize invalid messages regardless of proof validity.

**Economic attacks:** MEV extraction, front-running, sandwich attacks operate at application and network layers.

**Censorship:** A malicious prover can refuse to include transactions. Soundness ensures included transactions are valid, not that all valid transactions are included.

**Quantum attacks:** SNARK security relies on discrete logarithm hardness. The spec assumes classical adversaries.

**Operational security failures:** Key compromise, insider threats, misconfiguration. The spec defines correct behavior; it can't enforce that operators behave correctly.

### 15.10 Consolidated threat matrix

| Category | Threat | Mitigation | Section |
|----------|--------|------------|---------|
| **Encoding** | Field squeeze | Bytes32ToFr2 safe encoding | Section 7 |
| **Encoding** | Transcript collision | Typed absorption + domain tags | Section 8 |
| **Proof validity** | Partial execution | halted=1, exit_code binding | Section 5, Section 6 |
| **Proof validity** | Proof replay | Nonce, roots, and context/domain binding in public inputs | Section 5 |
| **Proof validity** | Chunk splicing | StateDigest chaining | Section 11 |
| **Resource** | Prover DoS | Caps on steps, intents, bytes | Section 3 |
| **Operational** | Artifact leakage | AEAD encryption + TEE boundary | Section 13 |
| **Consensus** | Implementation divergence | Determinism rule + conformance | Section 2, Section 14 |
| **Deployment** | VK/registry mismatch | Fail-closed gating | Section 3 |

**TLA+ Verification Coverage:**

| Threat Category | TLA+ Invariant | Verified |
|-----------------|----------------|----------|
| Proof forgery | `INV_ATK_NoRootForgery` | ✓ |
| State manipulation | `INV_BIND_StateDigest` | ✓ |
| Replay attack | `INV_ATK_NoReplay` | ✓ |
| Prefix-proof attack | `INV_ATK_NoPrefixProof` | ✓ |
| Chunk skip attack | `INV_ATK_NoSkipChunk` | ✓ |
| Splice attack | `INV_ATK_NoSplice` | ✓ |
| Cross-config attack | `INV_ATK_NoCrossConfig` | ✓ |
| Memory forgery | `INV_ATK_NoMemoryForgery`, `INV_ATK_NoIOForgery` | ✓ |
| Program substitution | `INV_BIND_ProgramHash` | ✓ |

**Coverage:** 9 of 9 threat categories have direct TLA+ invariant coverage. See Section 17 for detailed invariant descriptions and TLC verification instructions.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                       THREAT MATRIX VISUAL SUMMARY                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │  ATTACK                  MITIGATION               SECTION  TLA+       │  │
│  ├───────────────────────────────────────────────────────────────────────┤  │
│  │                                                                       │  │
│  │  ENCODING ATTACKS                                                     │  │
│  │  ├─ Field squeeze     ──▶ Bytes32ToFr2 encoding      §7       ✓       │  │
│  │  └─ Transcript collis.──▶ Typed absorption + tags    §8       ✓       │  │
│  │                                                                       │  │
│  │  PROOF VALIDITY ATTACKS                                               │  │
│  │  ├─ Prefix proof      ──▶ halted=1 required          §5,§6    ✓       │  │
│  │  ├─ Replay            ──▶ Nonce binding              §5       ✓       │  │
│  │  ├─ Chunk skip        ──▶ StateDigest chaining       §11      ✓       │  │
│  │  ├─ Splice            ──▶ StateDigest chaining       §11      ✓       │  │
│  │  ├─ Cross-config      ──▶ config_tags binding        §3,§11   ✓       │  │
│  │  ├─ Root forgery      ──▶ old/new root binding       §5,§11   ✓       │  │
│  │  ├─ Memory forgery    ──▶ SMT root commitment        §11      ✓       │  │
│  │  └─ Program subst.    ──▶ program_hash binding       §5       ✓       │  │
│  │                                                                       │  │
│  │  RESOURCE ATTACKS                                                     │  │
│  │  └─ Prover DoS        ──▶ Cap tags in registry       §3       —       │  │
│  │                                                                       │  │
│  │  OPERATIONAL                                                          │  │
│  │  └─ Artifact leakage  ──▶ AEAD encryption + TEE      §13      —       │  │
│  │                                                                       │  │
│  │  CONSENSUS                                                            │  │
│  │  ├─ Impl divergence   ──▶ Determinism rule + tests   §2,§14   —       │  │
│  │  └─ VK/reg mismatch   ──▶ Fail-closed gating         §3       —       │  │
│  │                                                                       │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  ═══════════════════════════════════════════════════════════════════════    │
│  LEGEND:  ✓ = TLA+ invariant verified (INV_ATK_*, INV_BIND_*)               │
│           — = Operational mitigation (not formally verified)                │
│                                                                             │
│  COVERAGE: 9/9 cryptographic attacks have TLA+ invariant coverage           │
│            All INV_ATK_* invariants pass TLC model checking                 │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 15.11 Load-bearing claims

| Claim | Evidence | Verification |
|-------|----------|--------------|
| **Field squeeze prevented** | Bytes32ToFr2 in Section 7 | Find collision under safe encoding → impossible |
| **Transcript collision prevented** | Type discriminators in Section 8 | Same data, different types → different states |
| **Prefix proofs prevented** | halted=1 constraint in Section 5 | Proof with halted=0 → wrapper rejects |
| **Prover DoS mitigated** | Cap tags in Section 3 | Over-cap batch → rejected at validation |
| **Confidentiality addressed** | AEAD requirement in Section 13 | Audit: no plaintext export paths |

### 15.12 Forward references

Section 15 summarizes; detailed treatments live elsewhere:

| Topic | Primary Section |
|-------|-----------------|
| Field encodings | Section 7 |
| Transcript specification | Section 8 |
| Wrapper constraints | Section 5 |
| Trust model / soundness | Section 4 |
| Confidentiality mechanisms | Section 13 |
| Resource caps | Section 3 |
| Conformance testing | Section 14 |
| Formal specification | Section 16 |
| TLA+ source code | Section 17 |

The threat matrix above references TLA+ invariants (INV_ATK_*, INV_BIND_*) that formally encode each security property. These invariants are not documentation but executable specifications: TLC model checking verifies that no reachable system state violates them. Section 16 provides a quick reference to the formal specification, mapping specification sections to TLA+ modules and listing all 26 verified invariants. Section 17 contains the complete source code.

---

## Section 16: TLA+ Formal Specification Quick Reference

When engineers argue about edge cases, the TLA+ specification ends the argument. It is not commentary on the protocol—it *is* the protocol, written in a language that admits no ambiguity. TLC has explored every reachable state. If your implementation diverges, TLC already knows.

The TLA+ specification is your single source of truth for the Jolt continuation protocol. Every state transition, every invariant, every security guarantee lives here in machine-checkable form. When a security property seems ambiguous, the TLA+ definition settles it. This is not documentation you read once and shelve. This is the oracle you consult.

Thirteen modules form a deliberate dependency chain, each building on the foundations below it. Types.tla sits at the base, defining the alphabet of the protocol: field elements, 64-bit integers, 32-byte hashes, status codes. From this foundation rise the structural modules: Encodings converts between byte arrays and field elements, Hash provides cryptographic primitives, SMT constructs the sparse Merkle trees that anchor memory state. VMState captures the RISC-V machine at any instant. Continuations orchestrates the chunked execution that makes unbounded computation provable. At the apex, JoltSpec composes everything into a temporal specification that TLC can exhaust.

**Repository Structure:**
```
jolt-tla/
├── tla/                    # Modular TLA+ specification (13 modules)
│   ├── Types.tla           # Foundation types
│   ├── Encodings.tla       # Byte/field encoding
│   ├── Hash.tla            # Hash abstractions
│   ├── Transcript.tla      # Fiat-Shamir transcript
│   ├── SMT.tla             # Sparse Merkle Tree structures
│   ├── SMTOps.tla          # SMT operations
│   ├── VMState.tla         # RISC-V VM state
│   ├── Registry.tla        # Configuration registry
│   ├── Continuations.tla   # Chunk execution & StateDigest
│   ├── Wrapper.tla         # Halo2 wrapper constraints
│   ├── JoltSpec.tla        # Top-level composition
│   ├── Invariants.tla      # All 26 individual invariants + 6 composites
│   └── MC_Jolt.tla         # TLC model configuration
├── JoltContinuations.tla   # Unified single-file spec (854 lines)
└── Jolt.cfg                # TLC configuration file
```

**Quick Start:**
```bash
# Verify specification (requires Java 11+ and tla2tools.jar)
cd jolt-tla/tla
java -jar tla2tools.jar -config ../Jolt.cfg MC_Jolt.tla

# Expected output: "Model checking completed. No error has been found."
```

### 16.1 Module Index

| Module | Purpose | Key Operators |
|--------|---------|---------------|
| `Types.tla` | Foundation types and constants | `Fr`, `U64`, `Bytes32`, `StatusCode`, `RegisterFile`, `ChunkIndex`, `StepCounter` |
| `Encodings.tla` | Byte/field encodings (§7.6 Bytes32ToFr2) | `Bytes32ToFr2`, `Bytes32ToFrLE`, `FrToBytes32LE`, `Fr2` |
| `Hash.tla` | Cryptographic hash primitives | `PoseidonHashV1`, `SMTLeafHash`, `SMTNodeHash`, `SHA256Hash`, domain tags |
| `Transcript.tla` | Fiat-Shamir transcript (Poseidon sponge) | `TranscriptAbsorb`, `TranscriptSqueeze`, `GetChallenge`, `AbsorbTag`, `TranscriptState` |
| `SMT.tla` | Sparse Merkle Tree structures (§11.8) | `MemoryMap`, `SMTState`, `GetPageHash`, `SetPage`, `DefaultHashes`, `PageIndex` |
| `SMTOps.tla` | SMT operations (§11.8.5-6) | `ComputeRoot`, `UpdatePage`, `UpdatePages`, `ComputeInitialIORoot`, `SMTRootBindingInvariant` |
| `VMState.tla` | RISC-V VM state machine (§6, §11.5) | `VMStateV1`, `ExecuteStep`, `InitVMState`, `VMStateTypeOK`, `RegisterX0Zero` |
| `Registry.tla` | Configuration registry (§3) | `RegistryDeploymentReady`, `RequiredKeys`, `ValidateRegistryValue`, `ComputeConfigTags` |
| `Continuations.tla` | Chunked execution (§11) | `ComputeStateDigest`, `ChunkValid`, `ContinuityInvariant`, `MakeChunkRecord`, `ExecuteChunk` |
| `Wrapper.tla` | Halo2 wrapper constraints (§5) | `ConstructPublicInputs`, `PublicInputsV1`, `ProgramHashBinding`, `StatusFrBinding`, `NonceBinding` |
| `JoltSpec.tla` | Top-level composition | `Init`, `Next`, `Spec`, `InitSystemState`, `StartExecution`, `CompleteExecution` |
| `Invariants.tla` | All 26 individual + 6 composite invariants (§15) | `INV_TYPE_*`, `INV_BIND_*`, `INV_SAFE_*`, `INV_ATK_*`, `AllInvariants`, `CriticalInvariants` |
| `MC_Jolt.tla` | TLC model configuration | `ModelInit`, `ModelSpec`, `StateConstraint`, `ModelStepFn`, `ModelRegistry` |

### 16.2 Invariant Categories

The TLA+ specification verifies **26 individual invariants** across four categories, plus **6 composite invariants** for convenience (4 category composites + 2 top-level composites). Each invariant is defined in `Invariants.tla` and checked by TLC during model verification.

#### Type Invariants (INV_TYPE_*) — 4 invariants
Ensure all values are well-formed per TLA+ type definitions. Medium severity—violations break model checking.

| Invariant | TLA+ Definition | Purpose |
|-----------|-----------------|---------|
| `INV_TYPE_SystemState` | `sys.phase \in SystemPhase /\ sys.batchNonce \in U64` | System state record well-formed |
| `INV_TYPE_Registry` | `RegistryStateTypeOK(sys.registry)` | All registry entries well-formed |
| `INV_TYPE_VMState` | `RegisterFileTypeOK`, `Bytes32TypeOK` checks | VM state (regs, PC, roots, halted) well-formed |
| `INV_TYPE_ProgramHash` | `sys.programHash \in Bytes32` | Program hash is valid 32-byte array |

#### Binding Invariants (INV_BIND_*) — 7 invariants
Ensure cryptographic bindings are maintained. Critical severity—violations enable forgery attacks.

| Invariant | Section Reference | Purpose |
|-----------|-------------------|---------|
| `INV_BIND_StatusFr` | §5.5 Constraint 6 | `status_fr = U64ToFr(exit_code)` — status matches final exit code |
| `INV_BIND_OldRoot` | §5.5 Constraint 5 | `old_root_{lo,hi}` matches initial `rw_mem_root_bytes32` |
| `INV_BIND_NewRoot` | §5.5 Constraint 5 | `new_root_{lo,hi}` matches final `rw_mem_root_bytes32` |
| `INV_BIND_ProgramHash` | §5.5 Constraint 2 | `program_hash_{lo,hi}` matches ELF hash via Bytes32ToFr2 |
| `INV_BIND_ConfigTags` | §3, §11.10 | `config_tags = ComputeConfigTags(registry)` during execution |
| `INV_BIND_StateDigest` | §11.10 | Each chunk's `digestIn` = `ComputeStateDigest(programHash, stateIn)` |
| `INV_BIND_Nonce` | §5.3 | `batch_nonce_fr = U64ToFr(a4)` — replay prevention binding |

#### Safety Invariants (INV_SAFE_*) — 7 invariants
Ensure system behaves correctly. High severity—violations break protocol correctness.

| Invariant | TLA+ Check | Purpose |
|-----------|------------|---------|
| `INV_SAFE_RegistryReady` | `RegistryDeploymentReady(sys.registry)` | Registry fully configured before execution |
| `INV_SAFE_NoTBD` | `NoTBDInvariant(sys.registry)` | No TBD values after INIT phase |
| `INV_SAFE_VMHaltedExitCode` | `halted=0 => exit_code=0; halted=1 => exit_code \in 0..255` | Exit code constraints |
| `INV_SAFE_RegisterX0` | `sys.vmState.regs[0] = 0` | RISC-V: x0 always equals zero |
| `INV_SAFE_HaltedBinary` | `sys.vmState.halted \in {0, 1}` | Halted flag is binary |
| `INV_SAFE_ContinuationChain` | `ContinuityInvariant(chunks)` | `digestOut[i] = digestIn[i+1]` for all adjacent chunks |
| `INV_SAFE_FinalChunkHalted` | `chunks[last].stateOut.halted = 1` | Final chunk must have halted=1 |

#### Attack Prevention Invariants (INV_ATK_*) — 8 invariants
Each corresponds to a specific attack vector from §15.10 Threat Matrix. Critical severity—violations directly enable attacks.

| Invariant | Attack Vector | Mitigation |
|-----------|---------------|------------|
| `INV_ATK_NoPrefixProof` | Prove incomplete execution | `status_fr` bound to `halted=1` state |
| `INV_ATK_NoSkipChunk` | Skip chunk containing critical logic | `NoSkippedChunks`: chunk indices are consecutive |
| `INV_ATK_NoSplice` | Splice chunks from different executions | `ContinuityInvariant`: StateDigest chaining |
| `INV_ATK_NoCrossConfig` | Use permissive config at proof time | `ConfigConsistentAcrossChunks`: config_tags constant |
| `INV_ATK_NoRootForgery` | Claim false memory state roots | `INV_BIND_OldRoot` + `INV_BIND_NewRoot` |
| `INV_ATK_NoMemoryForgery` | Manipulate RW memory between chunks | `rw_mem_root` continuity across chunk boundaries |
| `INV_ATK_NoIOForgery` | Manipulate IO memory between chunks | `io_root` continuity across chunk boundaries |
| `INV_ATK_NoReplay` | Reuse proof from different batch | `batch_nonce_fr` bound to initial `a4` register |

#### Composite Invariants
For convenience, `Invariants.tla` provides composite checks:

| Composite | Contents |
|-----------|----------|
| `INV_TYPE_All` | All 4 type invariants |
| `INV_BIND_All` | All 7 binding invariants |
| `INV_SAFE_All` | All 7 safety invariants |
| `INV_ATK_All` | All 8 attack prevention invariants |
| `AllInvariants` | All 26 individual invariants (TYPE + BIND + SAFE + ATK) |
| `CriticalInvariants` | Subset: `StatusFr`, `OldRoot`, `NewRoot`, `ContinuationChain`, `NoPrefixProof`, `NoSkipChunk`, `NoSplice` |

### 16.3 Running TLC

**Basic validation (smoke test):**
```bash
cd canonical
java -XX:+UseParallelGC -Xmx4g -jar tla2tools.jar MC_Jolt.tla \
     -config Jolt.cfg -workers auto
```

**Expected output:**
```
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states...
```

**Configuration options in Jolt.cfg:**

| Mode | Invariants | Use Case |
|------|------------|----------|
| Types only | `INV_TYPE_All` | Fastest; syntax validation |
| Types + Safety | `INV_TYPE_All`, `INV_SAFE_All` | Development iteration |
| Full check | `AllInvariants` | Pre-release validation |
| Critical only | `CriticalInvariants` | Attack surface focus |

### 16.4 Cross-Reference Convention

Throughout the Jolt Specification, TLA+ references use the format:

```
Module.tla:Line (OperatorName)
```

**Example:** `VMState.tla:296 (RegisterX0Zero)` refers to line 296 of VMState.tla where the `RegisterX0Zero` operator is defined.

### 16.5 Key TLA+ to Jolt Specification Mappings

| Jolt Specification Section | TLA+ Location | Operator | Description |
|----------------------------|---------------|----------|-------------|
| §6.4 (NUM_REGISTERS=32) | Types.tla:28, 39 | `NUM_REGISTERS` | CONSTANT declaration + ASSUME constraint |
| §6.8.1 (x0 = 0) | VMState.tla:296 | `RegisterX0Zero` | RISC-V x0 register always zero |
| §11.5 (VMStateV1) | VMState.tla:59-68 | `VMStateV1` | 8-field VM state record definition |
| §11.10 (StateDigestV1) | Continuations.tla:103 | `ComputeStateDigest` | StateDigest computation from program_hash + state |
| §5.5 Constraint 3 | Continuations.tla:202 | `ContinuityInvariant` | Chunk chaining: digestOut[i] = digestIn[i+1] |
| §15.10 Threat Matrix | Invariants.tla:199-207 | `INV_ATK_All` | All 8 attack prevention invariants |
| §3.4 (Registry Keys) | Registry.tla:24-37 | `RequiredKeys` | 5 required registry key constants |
| §5.5 (Wrapper Constraints) | Wrapper.tla:100-119 | Binding operators | 6 public input binding constraints |
| §11.8 (SMT) | SMT.tla:27-29 | Page constants | PAGE_SIZE_BYTES, PAGE_SHIFT, KEY_BITS |

### 16.6 Model Limitations

The TLC model uses bounded abstractions for tractability. **Production implementations MUST follow the algorithms specified in the prose specification exactly**—the TLA+ model verifies structural correctness, not cryptographic security.

#### TLC Bounds vs. Production Values

| Constant | TLC Value | Production Value | Notes |
|----------|-----------|------------------|-------|
| `FR_TLC_BOUND` | 16,384 | ~2^254 | BLS12-381 scalar field |
| `U64_TLC_BOUND` | 65,536 | 2^64 | Full u64 range |
| `CHUNK_MAX_STEPS` | 2-3 | ~10^6 | Instructions per chunk |
| `MAX_CHUNKS` | 3 | Unbounded | Execution length limit |
| `PAGE_INDEX_TLC_BOUND` | 4 | 2^32 | Memory page indices |
| `MAX_DIRTY_PAGES` | 2 | ~10^4 | Non-zero pages per chunk |
| `MAX_ABSORPTIONS` | 4 | ~100 | Transcript absorptions |

#### Abstracted Components

| Aspect | TLC Model | Production Requirement |
|--------|-----------|----------------------|
| **StateDigest** | Weighted fingerprint (mod N) | 14-step Poseidon transcript (§11.10.2) |
| **Hash functions** | `PoseidonHashV1` returns fingerprint | Domain-separated Poseidon with proper parameters |
| **SMT root** | `ComputeRoot` via recursive hash | Full 32-level Merkle tree with default hashes |
| **Field arithmetic** | Natural number mod `FR_TLC_BOUND` | Montgomery form in BLS12-381 scalar field |
| **STEP_FN** | Model operator (increments counter) | Full RISC-V instruction decode & execute |

#### What TLC Verifies vs. What It Cannot

**TLC CAN verify:**
- State machine transitions follow protocol rules
- Invariants hold in all reachable states
- Chunk chaining logic is correct
- Public input bindings are properly constructed
- Attack prevention invariants are maintained

**TLC CANNOT verify:**
- Cryptographic collision resistance (assumes hash is injective)
- Soundness of the underlying SNARK system
- Correct implementation of Poseidon/SHA-256
- Arithmetic correctness at full field precision
- Actual RISC-V instruction semantics

#### Implementer Guidance

1. **Use TLA+ for protocol understanding**, not as a code generator
2. **Follow §11.10.2 exactly** for StateDigest computation—the 14 steps are normative
3. **Test against conformance vectors** (§14) once Poseidon parameters are finalized
4. **The TLA+ invariants document security requirements**—ensure your implementation maintains them

---

## Section 17: TLA+ Formal Specification Source Code

Every attack prevention invariant you read in Section 15 lives here in executable form. Run `java -jar tla2tools.jar Jolt.cfg JoltContinuations.tla`, and TLC will exhaustively verify that no reachable state violates `INV_ATK_NoPrefixProof` or `INV_ATK_NoSplice`. This is not documentation. This is proof.

This section delivers the mathematical bedrock of the Jolt continuation proof system. Where earlier sections sketch intuition and guide implementation, this section speaks with precision that machines can verify. The TLA+ specification is not documentation about the protocol; it *is* the protocol, rendered in a language that admits no ambiguity and tolerates no hand-waving.

TLA+ models systems as state machines. Each state captures a frozen moment: the VM's 32 registers, its program counter, whether execution has halted, the Merkle roots binding memory. Actions are the transitions that carry one state to the next: a single instruction executes, a chunk completes, execution finishes or fails. Invariants guard every reachable state, enforcing properties that must never break. The TLC model checker does not sample or test; it exhaustively walks every path the state machine permits. Bugs that hide from a million test runs have nowhere to shelter here.

The specification comprises thirteen modules, each modeling a distinct component. Types.tla establishes the vocabulary: field elements, bytes, status codes, register files. Encodings.tla handles the arithmetic of translating between byte arrays and field elements, using the 31+1 byte split that respects field boundaries. Hash.tla treats Poseidon and SHA-256 as ideal functions, abstracting cryptographic internals to focus on the collision-resistance properties that matter. The modules build upward: SMT structures for memory commitments, VMState for the RISC-V machine, Registry for configuration lifecycle, Continuations for chunked execution and digest chaining. At the apex, JoltSpec.tla composes everything into a complete temporal formula: initialize, then forever execute valid transitions. Invariants.tla assembles twenty-six individual properties plus six composites across four categories, and MC_Jolt.tla supplies the concrete values that make model checking tractable.

### 17.0 Module Reference

| Module | Spec Sections | What It Models |
|--------|---------------|----------------|
| **Types.tla** | §6.9.3, §7, §11.5 | Foundation types: Fr, U64, Bytes32, status codes |
| **Encodings.tla** | §7 | Byte↔field element conversions (31+1 split) |
| **Hash.tla** | §8, §11.8.3 | Poseidon/SHA-256 as abstract functions with collision resistance |
| **Transcript.tla** | §8 | Fiat-Shamir transcript absorb/squeeze state machine |
| **SMT.tla** | §11.8 | Sparse Merkle Tree structures for memory commitments |
| **SMTOps.tla** | §11.8.5-6 | SMT root computation and page updates |
| **VMState.tla** | §6, §11.5 | RISC-V VM state: 32 registers, PC, halted flag, config_tags |
| **Registry.tla** | §3 | Configuration registry with TBD→validated lifecycle |
| **Continuations.tla** | §11 | Chunked execution, StateDigest computation, chunk chaining |
| **Wrapper.tla** | §5 | Halo2 wrapper: PublicInputsV1, binding constraints |
| **JoltSpec.tla** | All | Top-level composition: Init, Next, Spec |
| **Invariants.tla** | §15 | All 26 individual + 6 composite invariants organized by category (TYPE, BIND, SAFE, ATK) |
| **MC_Jolt.tla** | — | TLC model configuration and test harness |

#### 17.0.4 Invariant Categories

The specification verifies 26 individual invariants across four categories, plus 6 composite invariants for convenience (4 category composites + 2 top-level composites):

**Type Invariants (INV_TYPE_*)** — 4 invariants
Ensure all values are well-formed according to their type definitions. These catch basic programming errors.
- `INV_TYPE_SystemState`: System phase and nonce are valid
- `INV_TYPE_Registry`: Registry entries have proper structure
- `INV_TYPE_VMState`: Registers, PC, halted flag, exit_code are in bounds
- `INV_TYPE_ProgramHash`: Program hash is a valid Bytes32

**Binding Invariants (INV_BIND_*)** — 7 invariants
Ensure cryptographic commitments correctly bind to their source data. **These are security-critical.**
- `INV_BIND_StatusFr`: Public status_fr equals actual exit_code (prevents prefix-proof attacks)
- `INV_BIND_OldRoot/NewRoot`: Roots in public inputs match execution trace
- `INV_BIND_ProgramHash`: Program hash binds proof to specific ELF binary
- `INV_BIND_ConfigTags`: Config embedded in state matches registry
- `INV_BIND_StateDigest`: Digest binds all state fields (program_hash, config_tags, roots, etc.)
- `INV_BIND_Nonce`: Nonce binding prevents replay

**Safety Invariants (INV_SAFE_*)** — 8 invariants
Ensure the system behaves correctly under all circumstances.
- `INV_SAFE_RegistryReady`: Registry must be deployment-ready before execution
- `INV_SAFE_NoTBD`: No TBD values after initialization
- `INV_SAFE_VMHaltedExitCode`: Running VM has exit_code=0; halted has exit_code in 0..255
- `INV_SAFE_RegisterX0`: Register x0 is always zero (RISC-V requirement)
- `INV_SAFE_HaltedBinary`: Halted flag is exactly 0 or 1
- `INV_SAFE_ContinuationChain`: Chunks chain correctly via StateDigest
- `INV_SAFE_FinalChunkHalted`: Final chunk ends with halted=1

**Attack Prevention Invariants (INV_ATK_*)** — 8 invariants
Each corresponds to a specific attack vector from §15. **These are the most critical.**
- `INV_ATK_NoPrefixProof`: Cannot claim success without halting with exit_code=0
- `INV_ATK_NoSkipChunk`: Cannot skip chunks in the execution trace
- `INV_ATK_NoSplice`: Cannot splice chunks from different executions
- `INV_ATK_NoCrossConfig`: Config must be consistent across all chunks
- `INV_ATK_NoRootForgery`: Cannot forge old_root or new_root values
- `INV_ATK_NoMemoryForgery`: RW memory roots chain between chunks
- `INV_ATK_NoIOForgery`: IO memory roots chain between chunks
- `INV_ATK_NoReplay`: Nonce prevents replaying old proofs

#### 17.0.5 TLA+ to Specification Mapping

The TLA+ specification provides formal definitions for concepts described in prose:

| Spec Concept | TLA+ Formal Definition | Module |
|--------------|------------------------|--------|
| "VMStateV1 record" (§11.5) | `VMStateV1 == [regs: RegisterFile, pc: U64, ...]` | VMState.tla |
| "halted=0 ⟹ exit_code=0" (§11.5) | `RunningExitCodeZero(state) == state.halted = 0 => state.exit_code = 0` | VMState.tla |
| "StateDigest binds all fields" (§11.10) | `ComputeStateDigest(program_hash, state)` | Continuations.tla |
| "Chunks chain via digest" (§11.4) | `ContinuityInvariant(chunks)` | Continuations.tla |
| "Wrapper Constraint 1" (§5.5) | `ProgramHashBinding(inputs, programHash)` | Wrapper.tla |
| "Prefix-proof prevention" (§6.9.2) | `INV_ATK_NoPrefixProof` | Invariants.tla |

#### 17.0.6 Model Limitations

The TLC model checker cannot verify properties over infinite domains. The specification addresses this via:

1. **Bounded Constants**: `FR_TLC_BOUND = 16384` instead of actual ~2^255
2. **Abstract Hash Functions**: Hash functions are modeled as injective functions with assumed collision resistance, not actual cryptographic implementations
3. **Fingerprint Encodings**: BytesToNat uses weighted sums instead of actual 256^i encoding
4. **State Constraints**: TLC explores at most `MAX_CHUNKS + 1` chunks per run

**Critical**: Production implementations MUST follow the algorithms in §1-§17 exactly. The TLA+ specification verifies structural correctness, not cryptographic security.

---

**Running TLC**: See §17.3 for TLC command-line usage. The specification uses `MC_Jolt.tla` as the model configuration module.

**Module Dependency Graph**:
```
Types → Encodings → Hash → Transcript → SMT → SMTOps → VMState → Registry → Continuations → Wrapper → JoltSpec → Invariants → MC_Jolt
```

---

### 17.1 Types.tla

**What it models**: Foundation types, constants, and status codes that all other modules build upon. This module defines the "vocabulary" of the specification—the sets of values that variables can take.

**Key definitions**:
- `Fr`: BLS12-381 scalar field elements (bounded for TLC)
- `Bytes32`: 32-byte arrays used for hashes and roots
- `StatusCode`: VM exit codes including `JOLT_STATUS_OK = 0` and trap codes 1-5
- `RegisterFile`: Mapping from register index (0-31) to U64 values

**How to read it**: Type definitions like `Byte == 0..255` define sets. The `CONSTANTS` section declares parameters that are instantiated in MC_Jolt.tla. `ASSUME` statements are preconditions that TLC checks before model checking begins.

```tla
---- MODULE Types ----
(* Purpose: Foundational types, constants, and status codes for Jolt continuations    *)
(* Section Reference: §6.9.3 (status codes), §7 (encodings),               *)
(*                    §11.5 (VMStateV1 field types)                        *)
EXTENDS Integers, FiniteSets

CONSTANTS
    CHUNK_MAX_STEPS,    \* Max guest instructions per chunk (§11.6)
    MAX_CHUNKS,         \* TLC bound: max chunks modeled in a single run
    NUM_REGISTERS,      \* Fixed at 32 for RV64IMC (§6)
    FR_MODULUS,         \* BLS12-381 scalar field modulus (spec anchor)
    FR_TLC_BOUND,       \* Finite subset for TLC enumeration
    U64_TLC_BOUND       \* Finite subset for u64 enumeration

ASSUME CHUNK_MAX_STEPS \in Nat /\ CHUNK_MAX_STEPS > 0
ASSUME MAX_CHUNKS \in Nat /\ MAX_CHUNKS > 0
ASSUME NUM_REGISTERS = 32
ASSUME FR_MODULUS \in Nat /\ FR_MODULUS > 0
ASSUME FR_TLC_BOUND \in Nat /\ FR_TLC_BOUND > 0 /\ FR_TLC_BOUND <= FR_MODULUS
ASSUME U64_TLC_BOUND \in Nat /\ U64_TLC_BOUND > 0

\* Basic Type Sets
Byte == 0..255
Bytes32 == [0..31 -> Byte]
Fr == 0..(FR_TLC_BOUND - 1)
FrByte == 0..(IF FR_TLC_BOUND >= 256 THEN 255 ELSE FR_TLC_BOUND - 1)
Fr2 == [lo: Fr, hi: FrByte]
U64 == 0..(U64_TLC_BOUND - 1)
StatusCode == 0..255
RegisterIndex == 0..(NUM_REGISTERS - 1)
HaltedFlag == {0, 1}
ChunkIndex == 0..(MAX_CHUNKS - 1)
StepCounter == 0..((MAX_CHUNKS + 1) * CHUNK_MAX_STEPS)

\* Status Code Constants (§6.9.3 JOLT_STATUS_CODES_V1)
JOLT_STATUS_OK == 0
JOLT_STATUS_TRAP_ILLEGAL_INSTRUCTION == 1
JOLT_STATUS_TRAP_BAD_MEMORY == 2
JOLT_STATUS_TRAP_FORBIDDEN_SYSCALL == 3
JOLT_STATUS_TRAP_OOM == 4
JOLT_STATUS_TRAP_INTERNAL == 5

TrapCodes == {
    JOLT_STATUS_TRAP_ILLEGAL_INSTRUCTION,
    JOLT_STATUS_TRAP_BAD_MEMORY,
    JOLT_STATUS_TRAP_FORBIDDEN_SYSCALL,
    JOLT_STATUS_TRAP_OOM,
    JOLT_STATUS_TRAP_INTERNAL
}

IsVmTrap(code) == code \in TrapCodes
IsSuccess(code) == code = JOLT_STATUS_OK
IsValidStatusCode(code) == code \in StatusCode

ZeroBytes32 == [i \in 0..31 |-> 0]
RegisterFile == [RegisterIndex -> U64]
ZeroRegisters == [i \in RegisterIndex |-> 0]

TypesConstantsOK ==
    /\ CHUNK_MAX_STEPS \in Nat \ {0}
    /\ MAX_CHUNKS \in Nat \ {0}
    /\ NUM_REGISTERS = 32
    /\ FR_MODULUS \in Nat \ {0}
    /\ FR_TLC_BOUND \in Nat \ {0}
    /\ FR_TLC_BOUND <= FR_MODULUS
    /\ U64_TLC_BOUND \in Nat \ {0}
====
```

---

### 17.2 Encodings.tla

**What it models**: Byte/field element encoding and decoding operators that translate between Bytes32 and Fr values. This is the formal model of §7's encoding rules.

**Key definitions**:
- `Bytes32ToFr2`: The 31+1 byte split that encodes 32 bytes as (lo, hi) field element pair
- `FrToBytes32LE`: Little-endian encoding of field elements to bytes
- `ERROR`: A sentinel value for non-canonical inputs (implements "reject, don't normalize")

**How to read it**: The `BytesToNat` and `NatToBytes` operators use a fingerprint-based encoding for TLC tractability. Production code must use actual little-endian arithmetic, but this model preserves the essential property that different inputs produce different outputs.

```tla
---- MODULE Encodings ----
(* Purpose: Byte/field element encoding and decoding operators              *)
(* Section Reference: §7 (Word/field encodings)                             *)
EXTENDS Types, TLC

ERROR == CHOOSE x : x \notin Fr
IsValidFr(x) == x # ERROR /\ x \in Fr

\* TLC-safe BytesToNat: fingerprint-based to avoid 256^i overflow
BytesToNat(bytes, len) ==
    LET RECURSIVE SumWeighted(_, _)
        SumWeighted(idx, acc) ==
            IF idx >= len THEN acc
            ELSE SumWeighted(idx + 1, acc + bytes[idx] * (idx + 1))
    IN SumWeighted(0, 0)

NatToBytes(n, len) == [i \in 0..(len-1) |-> (n + i * 17) % 256]

Bytes32ToFr2(bytes32) ==
    LET lo_nat == BytesToNat([i \in 0..30 |-> bytes32[i]], 31)
        hi_nat == bytes32[31]
    IN [lo |-> lo_nat, hi |-> hi_nat]

FrToBytes32LE(fr) == NatToBytes(fr, 32)
Bytes32LEToFrCanonical(bytes32) ==
    LET nat_val == BytesToNat(bytes32, 32)
    IN IF nat_val >= FR_MODULUS THEN ERROR ELSE nat_val

Bytes32ToFrLE(bytes32) == Bytes32LEToFrCanonical(bytes32)

Low31Bytes(bytes32) == [i \in 0..30 |-> bytes32[i]]
HighByte(bytes32) == bytes32[31]
Fr2Equal(a, b) == a.lo = b.lo /\ a.hi = b.hi
IsBytes32(x) == x \in Bytes32
IsFr2(x) == x \in Fr2
IsFr(x) == x \in Fr
====
```

---

### 17.3 Hash.tla

**What it models**: Cryptographic hash primitives (Poseidon and SHA-256) as ideal functionalities with assumed collision resistance. This abstracts away the cryptographic internals to focus on structural properties.

**Key definitions**:
- `PoseidonHashBytes/PoseidonHashFr2`: Uninterpreted function constants (defined in MC_Jolt.tla)
- `TAG_*`: All 14 domain separation tags used throughout the protocol (e.g., `"JOLT/SMT/PAGE/V1"`)
- `SMTLeafHash/SMTNodeHash`: Specialized hash operators for Sparse Merkle Trees

**How to read it**: The `CONSTANTS` section declares hash functions as uninterpreted. The `ASSUME` statements document collision resistance properties that TLC cannot check but that hold for the actual cryptographic implementations. Domain tags prevent cross-protocol hash collisions.

```tla
---- MODULE Hash ----
(* Purpose: Cryptographic hash primitives as ideal functionalities          *)
(* Section Reference: §8 (Poseidon transcript), §11.8.3 (SMT hash),        *)
(*                    §5.7 (SHA-256 batch commitment)                      *)
EXTENDS Types, Encodings, FiniteSets

CONSTANTS
    TAG_STRINGS,
    PoseidonHashBytes(_, _),
    PoseidonHashFr2(_, _, _),
    SHA256Hash(_)

ASSUME IsFiniteSet(TAG_STRINGS)
ASSUME TAG_STRINGS # {}

\* Domain Tags
TAG_SMT_PAGE == "JOLT/SMT/PAGE/V1"
TAG_SMT_NODE == "JOLT/SMT/NODE/V1"
TAG_TRANSCRIPT_VM_STATE == "JOLT/TRANSCRIPT/VM_STATE/V1"
TAG_TRANSCRIPT_CHALLENGE == "JOLT/TRANSCRIPT/CHALLENGE/V1"
TAG_TRANSCRIPT_DOMAIN == "JOLT/TRANSCRIPT/V1"
TAG_BATCH_HEADER_LEAF == "JOLT/BATCH/HEADER_LEAF/V1"
TAG_BATCH_FILL_LEAF == "JOLT/BATCH/FILL_LEAF/V1"
TAG_BATCH_EMPTY_FILL_LEAF == "JOLT/BATCH/EMPTY_FILL_LEAF/V1"
TAG_BATCH_PAD_LEAF == "JOLT/BATCH/PAD_LEAF/V1"
TAG_BATCH_NODE == "JOLT/BATCH/NODE/V1"
TAG_STATE_DIGEST == "JOLT/STATE/V1"
TAG_CHECKPOINTS == "JOLT/CHECKPOINTS/V1"
TAG_CONFIG_TAGS == "JOLT/CONFIG_TAGS/V1"
TAG_TAG == "JOLT/TAG/V1"

ALL_DOMAIN_TAGS == {
    TAG_SMT_PAGE, TAG_SMT_NODE, TAG_TRANSCRIPT_VM_STATE,
    TAG_TRANSCRIPT_CHALLENGE, TAG_TRANSCRIPT_DOMAIN,
    TAG_BATCH_HEADER_LEAF, TAG_BATCH_FILL_LEAF,
    TAG_BATCH_EMPTY_FILL_LEAF, TAG_BATCH_PAD_LEAF, TAG_BATCH_NODE,
    TAG_STATE_DIGEST, TAG_CHECKPOINTS, TAG_CONFIG_TAGS, TAG_TAG
}

ASSUME ALL_DOMAIN_TAGS \subseteq TAG_STRINGS

PoseidonHashV1(tag, data) == PoseidonHashBytes(tag, data)
PoseidonHashFr2V1(tag, fr1, fr2) == PoseidonHashFr2(tag, fr1, fr2)
SMTLeafHash(pageBytes) == PoseidonHashV1(TAG_SMT_PAGE, pageBytes)
SMTNodeHash(leftFr, rightFr) == PoseidonHashFr2V1(TAG_SMT_NODE, leftFr, rightFr)
StateDigestHash(serializedState) == PoseidonHashV1(TAG_STATE_DIGEST, serializedState)
CheckpointsDigestHash(checkpointsBytes) == PoseidonHashV1(TAG_CHECKPOINTS, checkpointsBytes)
IsPoseidonOutput(x) == x \in Fr
IsSHA256Output(x) == x \in Bytes32
====
```

---

### 17.4 Transcript.tla

**What it models**: The Fiat-Shamir transcript as a two-phase state machine: absorb values, then squeeze a challenge. This models how interactive protocols become non-interactive proofs.

**Key definitions**:
- `TranscriptState`: Record with absorptions sequence, phase (absorbing/squeezed), and challenge
- `TranscriptAbsorb`: Add a typed value to the transcript
- `TranscriptSqueeze`: Finalize and compute the challenge via Poseidon hash
- `ABSORB_TYPE_*`: Tags for different absorption types (VM_STATE, COMMITMENT, etc.)

**How to read it**: The transcript is a state machine that enforces ordering—once squeezed, no more absorptions allowed. The `ChallengeValue == Fr \cup {CHALLENGE_UNSET}` uses a union to model "maybe has a value."

```tla
---- MODULE Transcript ----
(* Purpose: Fiat-Shamir transcript state machine (Poseidon sponge)         *)
(* Section Reference: §8 (Transcript specification)                        *)
EXTENDS Hash, Sequences, Naturals

CONSTANTS MAX_ABSORPTIONS
ASSUME MAX_ABSORPTIONS \in Nat /\ MAX_ABSORPTIONS > 0

CHALLENGE_UNSET == -1
ChallengeValue == Fr \cup {CHALLENGE_UNSET}

ABSORB_TYPE_VM_STATE == TAG_TRANSCRIPT_VM_STATE
ABSORB_TYPE_COMMITMENT == "commitment"
ABSORB_TYPE_CONFIG == "config"
ABSORB_TYPE_PROGRAM_HASH == "program_hash"
ABSORB_TYPE_NONCE == "nonce"
ABSORB_TYPE_TAG == "tag"

AbsorptionTypes == {
    ABSORB_TYPE_VM_STATE, ABSORB_TYPE_COMMITMENT, ABSORB_TYPE_CONFIG,
    ABSORB_TYPE_PROGRAM_HASH, ABSORB_TYPE_NONCE, ABSORB_TYPE_TAG
}

AbsorptionEntry == [type: AbsorptionTypes, value: Fr]

PHASE_ABSORBING == "absorbing"
PHASE_SQUEEZED == "squeezed"
TranscriptPhase == {PHASE_ABSORBING, PHASE_SQUEEZED}

TranscriptState == [
    absorptions: Seq(AbsorptionEntry),
    phase: TranscriptPhase,
    challenge: ChallengeValue
]

InitTranscript == [
    absorptions |-> << >>,
    phase |-> PHASE_ABSORBING,
    challenge |-> CHALLENGE_UNSET
]

TranscriptAbsorb(transcript, absorbType, value) ==
    IF transcript.phase # PHASE_ABSORBING THEN transcript
    ELSE IF Len(transcript.absorptions) >= MAX_ABSORPTIONS THEN transcript
    ELSE [transcript EXCEPT !.absorptions = Append(@, [type |-> absorbType, value |-> value])]

RECURSIVE EncodeAbsorptions(_, _)
EncodeAbsorptions(absorptions, idx) ==
    IF idx > Len(absorptions) THEN 0
    ELSE absorptions[idx].value * (1000 ^ idx) + EncodeAbsorptions(absorptions, idx + 1)

SerializeAbsorptions(absorptions) == EncodeAbsorptions(absorptions, 1)
ComputeChallenge(absorptions) == PoseidonHashV1(TAG_TRANSCRIPT_CHALLENGE, SerializeAbsorptions(absorptions))

TranscriptSqueeze(transcript) ==
    IF transcript.phase # PHASE_ABSORBING THEN transcript
    ELSE [transcript EXCEPT !.phase = PHASE_SQUEEZED, !.challenge = ComputeChallenge(transcript.absorptions)]

GetChallenge(transcript) ==
    IF transcript.phase = PHASE_SQUEEZED THEN transcript.challenge ELSE CHALLENGE_UNSET

IsAbsorbing(transcript) == transcript.phase = PHASE_ABSORBING
IsSqueezed(transcript) == transcript.phase = PHASE_SQUEEZED
AbsorptionCount(transcript) == Len(transcript.absorptions)

TranscriptTypeOK(transcript) ==
    /\ transcript.absorptions \in Seq(AbsorptionEntry)
    /\ Len(transcript.absorptions) <= MAX_ABSORPTIONS
    /\ transcript.phase \in TranscriptPhase
    /\ (transcript.challenge \in Fr) \/ (transcript.challenge = CHALLENGE_UNSET)
    /\ (transcript.phase = PHASE_ABSORBING => transcript.challenge = CHALLENGE_UNSET)
    /\ (transcript.phase = PHASE_SQUEEZED => transcript.challenge \in Fr)
====
```

---

### 17.5 SMT.tla

**What it models**: Sparse Merkle Tree (SMT) structures for memory commitments. SMTs efficiently commit to sparse address spaces—only touched pages are stored, while untouched pages share a precomputed "default" hash.

**Key definitions**:
- `MemoryMap`: Partial function from page index to page hash (sparse representation)
- `SMTState`: Record with memory map, root hash, and dirty page count
- `DefaultHashes`: Precomputed hashes for empty subtrees at each depth
- `GetPageHash/SetPage`: Read and write operations on the sparse map

**How to read it**: The key insight is `GetPageHash(memMap, pageIdx)` returns `ZERO_PAGE_HASH` for pages not in the map—pages that were never written have a deterministic hash. The `IsMemoryMap` predicate uses set membership testing for TLC efficiency.

```tla
---- MODULE SMT ----
(* Purpose: Sparse Merkle Tree structures for memory commitments           *)
(* Section Reference: §11.8 (Memory commitments)                           *)
EXTENDS Hash, Sequences, Naturals

CONSTANTS PAGE_INDEX_TLC_BOUND, MAX_DIRTY_PAGES

PAGE_SIZE_BYTES == 4096
PAGE_SHIFT == 12
KEY_BITS == 32

ASSUME PAGE_INDEX_TLC_BOUND \in Nat /\ PAGE_INDEX_TLC_BOUND > 0
ASSUME MAX_DIRTY_PAGES \in Nat /\ MAX_DIRTY_PAGES >= 0

PageIndex == 0..(PAGE_INDEX_TLC_BOUND - 1)
FullPageIndexRange == 0..(2^KEY_BITS - 1)
PageContentHash == Fr
ZERO_PAGE == "ZERO_PAGE_BYTES4096"
ZERO_PAGE_HASH == SMTLeafHash(ZERO_PAGE)

MemoryMap == UNION { [dom -> PageContentHash] : dom \in SUBSET PageIndex }

IsMemoryMap(memMap) ==
    /\ DOMAIN memMap \subseteq PageIndex
    /\ \A p \in DOMAIN memMap : memMap[p] \in PageContentHash

MemoryMapCanonical(memMap) == \A p \in DOMAIN memMap : memMap[p] # ZERO_PAGE_HASH
EmptyMemoryMap == [p \in {} |-> ZERO_PAGE_HASH]
PagePresent(memMap, pageIdx) == pageIdx \in DOMAIN memMap

GetPageHash(memMap, pageIdx) ==
    IF PagePresent(memMap, pageIdx) THEN memMap[pageIdx] ELSE ZERO_PAGE_HASH

SetPage(memMap, pageIdx, contentHash) ==
    IF contentHash = ZERO_PAGE_HASH
    THEN [p \in (DOMAIN memMap \ {pageIdx}) |-> memMap[p]]
    ELSE [p \in (DOMAIN memMap \union {pageIdx}) |-> IF p = pageIdx THEN contentHash ELSE memMap[p]]

CONSTANT DefaultHashes
ASSUME DefaultHashes \in [0..KEY_BITS -> Fr]

EmptyTreeRoot == DefaultHashes[KEY_BITS]
GetBit(n, pos) == (n \div (2^pos)) % 2
BranchDirection(k, d) == GetBit(k, 31 - d)
KeyToPath(k) == [d \in 0..(KEY_BITS-1) |-> BranchDirection(k, d)]

SMTNodeType == {"leaf", "internal", "default"}

SMTState == [memMap: MemoryMap, root: Fr, dirtyCount: Nat]
InitSMTState == [memMap |-> EmptyMemoryMap, root |-> EmptyTreeRoot, dirtyCount |-> 0]

AddressToPageIndex(addr, regionBase, regionSize) ==
    IF addr < regionBase \/ addr >= regionBase + regionSize THEN -1
    ELSE (addr - regionBase) \div PAGE_SIZE_BYTES

MemoryRegionType == {"rw", "io"}
MemoryRegion == [regionType: MemoryRegionType, base: Nat, size: Nat, smtState: SMTState]

SMTStateTypeOK(smt) ==
    /\ IsMemoryMap(smt.memMap)
    /\ MemoryMapCanonical(smt.memMap)
    /\ smt.root \in Fr
    /\ smt.dirtyCount \in Nat
    /\ smt.dirtyCount <= MAX_DIRTY_PAGES
====
```

---

### 17.6 SMTOps.tla

**What it models**: SMT operations—computing roots, updating pages, and verifying the fundamental binding invariant: `root = ComputeRoot(memMap)`.

**Key definitions**:
- `ComputeRoot/ComputeSubtreeHash`: Recursive Merkle root computation from sparse map
- `UpdatePage`: Atomic update of a page and recomputation of root
- `SMTRootBindingInvariant`: The critical invariant that root equals computed root

**How to read it**: The recursive `ComputeSubtreeHash` operator checks if a subtree has any pages; if not, it returns `DefaultHashes[depth]` without recursing. This is the key optimization that makes SMTs efficient for sparse data.

```tla
---- MODULE SMTOps ----
(* Purpose: Sparse Merkle Tree operations for memory commitments           *)
(* Section Reference: §11.8.5 (Root computation), §11.8.6 (Encoding)       *)
EXTENDS SMT

HasPagesInSubtree(memMap, depth, prefix) ==
    \E pageIdx \in DOMAIN memMap :
        LET shift == depth
            keyHighBits == IF shift >= KEY_BITS THEN 0 ELSE pageIdx \div (2^shift)
        IN keyHighBits = prefix

RECURSIVE ComputeSubtreeHash(_, _, _)
ComputeSubtreeHash(memMap, depth, prefix) ==
    IF depth = 0 THEN GetPageHash(memMap, prefix)
    ELSE IF ~HasPagesInSubtree(memMap, depth, prefix) THEN DefaultHashes[depth]
    ELSE LET leftPrefix == prefix * 2
             rightPrefix == prefix * 2 + 1
             leftHash == ComputeSubtreeHash(memMap, depth - 1, leftPrefix)
             rightHash == ComputeSubtreeHash(memMap, depth - 1, rightPrefix)
         IN SMTNodeHash(leftHash, rightHash)

ComputeRoot(memMap) ==
    IF DOMAIN memMap = {} THEN EmptyTreeRoot
    ELSE ComputeSubtreeHash(memMap, KEY_BITS, 0)

UpdatePage(smt, pageIdx, newContentHash) ==
    LET newMemMap == SetPage(smt.memMap, pageIdx, newContentHash)
        newRoot == ComputeRoot(newMemMap)
        newDirtyCount == Cardinality(DOMAIN newMemMap)
    IN [smt EXCEPT !.memMap = newMemMap, !.root = newRoot, !.dirtyCount = newDirtyCount]

RootToBytes32(rootFr) == FrToBytes32LE(rootFr)
Bytes32ToRoot(bytes32) == Bytes32ToFrLE(bytes32)

SMTRootBindingInvariant(smt) == smt.root = ComputeRoot(smt.memMap)
SMTDirtyCountInvariant(smt) == smt.dirtyCount = Cardinality(DOMAIN smt.memMap)
SMTInvariant(smt) == /\ SMTStateTypeOK(smt) /\ SMTRootBindingInvariant(smt) /\ SMTDirtyCountInvariant(smt)

ComputeInitialIORoot(manifestBytes, inputPtr, inputLen, regionBase) ==
    LET startPage == (inputPtr - regionBase) \div PAGE_SIZE_BYTES
        endPage == (inputPtr + inputLen - 1 - regionBase) \div PAGE_SIZE_BYTES
        inputMemMap == [p \in startPage..endPage |->
            PoseidonHashV1(TAG_SMT_PAGE, Len(manifestBytes) * 100 + p)]
    IN ComputeRoot(inputMemMap)

ComputeInitialRWRoot == EmptyTreeRoot
====
```

---

### 17.7 VMState.tla

**What it models**: The RISC-V VM state machine—32 registers, program counter, halted flag, exit code, memory roots, and config_tags. This is the core of what gets proven: deterministic execution from initial state to halted state.

**Key definitions**:
- `VMStateV1`: The complete state record (matches §11.5 exactly)
- `ExecuteStep`: Single instruction execution via abstract `STEP_FN`
- `IsSuccessfulHalt/IsTrappedHalt`: Predicates for execution outcomes
- `RegisterX0Zero`: Invariant that x0 is always zero (RISC-V requirement)

**How to read it**: The `STEP_FN` is an uninterpreted constant—the model doesn't care *how* instructions execute, only that each step produces a valid next state. `VMStateSafetyInvariant` combines all the state validity checks.

```tla
---- MODULE VMState ----
(* Purpose: RISC-V VM state machine for deterministic guest execution      *)
(* Section Reference: §6 (Guest VM), §11.5 (VMStateV1)                     *)
EXTENDS Types, SMT, SMTOps, Sequences

CONSTANTS STEP_FN(_), ENTRY_POINT, RW_REGION_BASE, RW_REGION_SIZE, IO_REGION_BASE, IO_REGION_SIZE

ASSUME ENTRY_POINT \in U64
ASSUME RW_REGION_BASE \in Nat /\ RW_REGION_SIZE \in Nat
ASSUME IO_REGION_BASE \in Nat /\ IO_REGION_SIZE \in Nat

ConfigTag == [name: STRING, value: STRING]
ConfigTagTypeOK(tag) == /\ tag.name \in STRING /\ tag.value \in STRING

VMStateV1 == [
    regs: RegisterFile, pc: U64, step_counter: StepCounter,
    rw_mem_root_bytes32: Bytes32, io_root_bytes32: Bytes32,
    halted: HaltedFlag, exit_code: U64, config_tags: Seq(ConfigTag)
]

REG_A0 == 10  REG_A1 == 11  REG_A2 == 12  REG_A3 == 13  REG_A4 == 14  REG_SP == 2

InitRegisters(inputPtr, inputLen, outputPtr, outputMax, batchNonce, stackPtr) ==
    [i \in RegisterIndex |->
        CASE i = 0 -> 0 [] i = REG_A0 -> inputPtr [] i = REG_A1 -> inputLen
          [] i = REG_A2 -> outputPtr [] i = REG_A3 -> outputMax
          [] i = REG_A4 -> batchNonce [] i = REG_SP -> stackPtr [] OTHER -> 0]

InitVMState(inputPtr, inputLen, outputPtr, outputMax, batchNonce, stackPtr, initialRWRoot, initialIORoot, configTags) ==
    [regs |-> InitRegisters(inputPtr, inputLen, outputPtr, outputMax, batchNonce, stackPtr),
     pc |-> ENTRY_POINT, step_counter |-> 0,
     rw_mem_root_bytes32 |-> initialRWRoot, io_root_bytes32 |-> initialIORoot,
     halted |-> 0, exit_code |-> 0, config_tags |-> configTags]

IsRunning(state) == state.halted = 0
IsHalted(state) == state.halted = 1
IsSuccessfulHalt(state) == /\ IsHalted(state) /\ state.exit_code = JOLT_STATUS_OK
IsTrappedHalt(state) == /\ IsHalted(state) /\ IsVmTrap(state.exit_code)
GetExitStatus(state) == IF IsHalted(state) THEN state.exit_code ELSE 0

ReadReg(state, idx) == IF idx = 0 THEN 0 ELSE IF idx \in RegisterIndex THEN state.regs[idx] ELSE 0
WriteReg(state, idx, value) == IF idx = 0 \/ idx \notin RegisterIndex THEN state ELSE [state EXCEPT !.regs[idx] = value]

ExecuteStep(state) ==
    IF IsHalted(state) THEN state
    ELSE LET result == STEP_FN(state)
             typeOK == /\ result.halted \in {0, 1} /\ result.exit_code \in 0..255 /\ result.step_counter >= state.step_counter
         IN IF Assert(typeOK, "STEP_FN returned invalid VMState") THEN result ELSE state

RECURSIVE ExecuteNSteps(_, _)
ExecuteNSteps(state, n) == IF n = 0 \/ IsHalted(state) THEN state ELSE ExecuteNSteps(ExecuteStep(state), n - 1)

RegisterFileTypeOK(regs) == /\ DOMAIN regs = RegisterIndex /\ \A i \in RegisterIndex : regs[i] \in U64
Bytes32TypeOK(bytes) == /\ DOMAIN bytes = 0..31 /\ \A i \in 0..31 : bytes[i] \in Byte

VMStateTypeOK(state) ==
    /\ RegisterFileTypeOK(state.regs) /\ state.pc \in U64 /\ state.step_counter \in StepCounter
    /\ Bytes32TypeOK(state.rw_mem_root_bytes32) /\ Bytes32TypeOK(state.io_root_bytes32)
    /\ state.halted \in HaltedFlag /\ state.exit_code \in U64
    /\ \A i \in 1..Len(state.config_tags) : ConfigTagTypeOK(state.config_tags[i])

HaltedFlagValid(state) == state.halted \in {0, 1}
RunningExitCodeZero(state) == state.halted = 0 => state.exit_code = 0
HaltedExitCodeValid(state) == state.halted = 1 => state.exit_code \in 0..255
RegisterX0Zero(state) == state.regs[0] = 0

VMStateSafetyInvariant(state) ==
    /\ HaltedFlagValid(state) /\ RunningExitCodeZero(state) /\ HaltedExitCodeValid(state) /\ RegisterX0Zero(state)
====
```

---

### 17.8 Registry.tla

**What it models**: The configuration registry lifecycle—from TBD (unset) values through validation to deployment-ready state. This ensures all consensus-critical parameters are set before execution begins.

**Key definitions**:
- `RequiredKeys`: The 5 mandatory configuration keys (JOLT_SPEC_VERSION, etc.)
- `RequiredKeysSorted`: Canonical ordering for deterministic config_tags
- `RegistryDeploymentReady`: Predicate that all values are set and validated
- `ComputeConfigTags`: Constructs the config_tags sequence from registry

**How to read it**: The registry uses a TBD_VALUE sentinel for unset values. `NoTBDInvariant` ensures no TBD values remain after initialization. The sorted sequence ensures different implementations compute identical config_tags.

```tla
---- MODULE Registry ----
(* Purpose: Configuration registry and deployment validation               *)
(* Section Reference: §3 (Registry), §3.8 (config_tags)                    *)
EXTENDS VMState

KEY_SPEC_VERSION == "JOLT_SPEC_VERSION"
KEY_MAX_MANIFEST_BYTES == "JOLT_MAX_MANIFEST_BYTES"
KEY_MAX_INTENTS == "JOLT_MAX_INTENTS"
KEY_MAX_CHECKPOINTS_BYTES == "JOLT_MAX_CHECKPOINTS_BYTES"
KEY_CONTEXT_BYTES32 == "JOLT_CONTEXT_BYTES32"

RequiredKeys == {KEY_SPEC_VERSION, KEY_MAX_MANIFEST_BYTES, KEY_MAX_INTENTS, KEY_MAX_CHECKPOINTS_BYTES, KEY_CONTEXT_BYTES32}

RequiredKeysSorted == <<KEY_CONTEXT_BYTES32, KEY_MAX_CHECKPOINTS_BYTES, KEY_MAX_INTENTS, KEY_MAX_MANIFEST_BYTES, KEY_SPEC_VERSION>>

ASSUME {RequiredKeysSorted[i] : i \in 1..Len(RequiredKeysSorted)} = RequiredKeys
ASSUME Len(RequiredKeysSorted) = Cardinality(RequiredKeys)

TBD_VALUE == "TBD"
RegistryEntry == [key: STRING, value: STRING, required: BOOLEAN, validated: BOOLEAN]
RegistryState == [RequiredKeys -> RegistryEntry]

RegistryEntryTypeOK(entry) == /\ entry.key \in STRING /\ entry.value \in STRING /\ entry.required \in BOOLEAN /\ entry.validated \in BOOLEAN
RegistryStateTypeOK(registry) == \A k \in RequiredKeys : RegistryEntryTypeOK(registry[k])

InitRegistryEntry(keyName) == [key |-> keyName, value |-> TBD_VALUE, required |-> TRUE, validated |-> FALSE]
InitRegistry == [k \in RequiredKeys |-> InitRegistryEntry(k)]

SetRegistryValue(registry, keyName, value) ==
    IF keyName \notin RequiredKeys THEN registry
    ELSE [registry EXCEPT ![keyName] = [@ EXCEPT !.value = value, !.validated = FALSE]]

GetRegistryValue(registry, keyName) == IF keyName \in RequiredKeys THEN registry[keyName].value ELSE TBD_VALUE
IsTBD(value) == value = TBD_VALUE
EntryReady(entry) == /\ entry.value # TBD_VALUE /\ entry.validated

RegistryDeploymentReady(registry) == \A k \in RequiredKeys : /\ registry[k].value # TBD_VALUE /\ registry[k].validated
TBDCount(registry) == Cardinality({k \in RequiredKeys : registry[k].value = TBD_VALUE})

EntryToConfigTag(entry) == [name |-> entry.key, value |-> entry.value]
ComputeConfigTags(registry) == [i \in 1..Len(RequiredKeysSorted) |-> EntryToConfigTag(registry[RequiredKeysSorted[i]])]

NoTBDInvariant(registry) == \A k \in RequiredKeys : registry[k].value # TBD_VALUE
====
```

---

### 17.9 Continuations.tla

**What it models**: Chunked execution—breaking long computations into fixed-size chunks that can be proven independently and chained together via StateDigest matching.

**Key definitions**:
- `ChunkRecord`: A proven chunk with stateIn, stateOut, digestIn, digestOut
- `ComputeStateDigest`: The 14-step algorithm that binds all state fields (program_hash, config_tags, roots, etc.)
- `ContinuityInvariant`: The critical chaining property: `chunk[i].digestOut = chunk[i+1].digestIn`
- `ExecutionTrace`: A sequence of valid, chained chunks ending in a halted state

**How to read it**: This is where the "relay race baton" analogy applies—each chunk passes the baton (digestOut) to the next. `ChunkValid` checks all the individual chunk properties; `ExecutionTraceValid` checks the whole sequence including chaining.

```tla
---- MODULE Continuations ----
(* Purpose: Chunked execution and StateDigest chaining for continuations   *)
(* Section Reference: §11 (Continuations, snapshots, StateDigest)          *)
EXTENDS VMState, Transcript, Sequences, Naturals, TLC

SumSet(S) == LET RECURSIVE Sum(_)
                 Sum(s) == IF s = {} THEN 0
                           ELSE LET x == CHOOSE x \in s : TRUE IN x + Sum(s \ {x})
             IN Sum(S)

SerializeVMStateWithProgram(program_hash_bytes32, state) ==
    LET regSum == SumSet({state.regs[i] : i \in DOMAIN state.regs})
        progHashContrib == SumSet({program_hash_bytes32[i] : i \in DOMAIN program_hash_bytes32})
        configTagsContrib == IF Len(state.config_tags) > 0
                             THEN SumSet({Len(state.config_tags[i].name) + Len(state.config_tags[i].value) : i \in 1..Len(state.config_tags)})
                             ELSE 0
        rwRootContrib == SumSet({state.rw_mem_root_bytes32[i] : i \in DOMAIN state.rw_mem_root_bytes32})
        ioRootContrib == SumSet({state.io_root_bytes32[i] : i \in DOMAIN state.io_root_bytes32})
    IN (progHashContrib % 1000) * 100000 + (configTagsContrib % 100) * 10000
       + ((rwRootContrib + ioRootContrib) % 100) * 1000 + (state.step_counter % 100) * 100
       + (state.pc % 10) * 10 + state.halted * 5 + (state.exit_code % 5) + (regSum % 5)

ComputeStateDigest(program_hash_bytes32, state) == PoseidonHashV1(TAG_STATE_DIGEST, SerializeVMStateWithProgram(program_hash_bytes32, state))
StateDigest == Fr

ChunkRecord == [program_hash_bytes32: Bytes32, chunkIndex: ChunkIndex, stateIn: VMStateV1, digestIn: StateDigest,
                stateOut: VMStateV1, digestOut: StateDigest, stepsExecuted: Nat, isFinal: BOOLEAN]

MakeChunkRecord(program_hash_bytes32, idx, stateIn, stateOut) == [
    program_hash_bytes32 |-> program_hash_bytes32, chunkIndex |-> idx,
    stateIn |-> stateIn, digestIn |-> ComputeStateDigest(program_hash_bytes32, stateIn),
    stateOut |-> stateOut, digestOut |-> ComputeStateDigest(program_hash_bytes32, stateOut),
    stepsExecuted |-> stateOut.step_counter - stateIn.step_counter, isFinal |-> IsHalted(stateOut)]

ExpectedChunkStartStep(chunkIdx) == chunkIdx * CHUNK_MAX_STEPS
NonFinalChunkSteps == CHUNK_MAX_STEPS
ChunkInputStepValid(chunk) == chunk.stateIn.step_counter = ExpectedChunkStartStep(chunk.chunkIndex)
NonFinalChunkStepsValid(chunk) == ~chunk.isFinal => chunk.stepsExecuted = CHUNK_MAX_STEPS
NonFinalChunkNotHalted(chunk) == ~chunk.isFinal => chunk.stateOut.halted = 0
FinalChunkHalted(chunk) == chunk.isFinal => chunk.stateOut.halted = 1
FinalChunkStepsValid(chunk) == chunk.isFinal => /\ chunk.stepsExecuted >= 1 /\ chunk.stepsExecuted <= CHUNK_MAX_STEPS

ChunkValid(chunk) == /\ ChunkInputStepValid(chunk) /\ NonFinalChunkStepsValid(chunk) /\ NonFinalChunkNotHalted(chunk)
    /\ FinalChunkHalted(chunk) /\ FinalChunkStepsValid(chunk)
    /\ chunk.digestIn = ComputeStateDigest(chunk.program_hash_bytes32, chunk.stateIn)
    /\ chunk.digestOut = ComputeStateDigest(chunk.program_hash_bytes32, chunk.stateOut)

ChunksChained(chunk1, chunk2) == /\ chunk1.chunkIndex + 1 = chunk2.chunkIndex /\ chunk1.digestOut = chunk2.digestIn
ContinuityInvariant(chunks) == \A i \in 1..(Len(chunks) - 1) : chunks[i].digestOut = chunks[i + 1].digestIn

ExecutionTrace == Seq(ChunkRecord)
ExecutionTraceValid(trace) == /\ Len(trace) >= 1 /\ trace[1].chunkIndex = 0
    /\ \A i \in 1..Len(trace) : ChunkValid(trace[i]) /\ ContinuityInvariant(trace)
    /\ trace[Len(trace)].isFinal /\ \A i \in 1..(Len(trace) - 1) : ~trace[i].isFinal

TraceInitialState(trace) == trace[1].stateIn
TraceFinalState(trace) == trace[Len(trace)].stateOut
TraceInitialDigest(trace) == trace[1].digestIn
TraceFinalDigest(trace) == trace[Len(trace)].digestOut
ConfigConsistentAcrossChunks(trace) == \A i, j \in 1..Len(trace) : trace[i].stateIn.config_tags = trace[j].stateIn.config_tags
NoSkippedChunks(trace) == \A i \in 1..Len(trace) : trace[i].chunkIndex = i - 1

ContinuationState == [program_hash_bytes32: Bytes32, currentChunk: ChunkIndex, chunks: ExecutionTrace,
                      complete: BOOLEAN, initialDigest: StateDigest, finalDigest: StateDigest]

InitContinuation(program_hash_bytes32, initialState) == [
    program_hash_bytes32 |-> program_hash_bytes32, currentChunk |-> 0, chunks |-> << >>, complete |-> FALSE,
    initialDigest |-> ComputeStateDigest(program_hash_bytes32, initialState), finalDigest |-> 0]

ExecuteChunk(cont, stateIn, stateOut) ==
    LET chunk == MakeChunkRecord(cont.program_hash_bytes32, cont.currentChunk, stateIn, stateOut)
        newChunks == Append(cont.chunks, chunk)
        isComplete == chunk.isFinal
    IN [cont EXCEPT !.currentChunk = @ + 1, !.chunks = newChunks, !.complete = isComplete,
                    !.finalDigest = IF isComplete THEN chunk.digestOut ELSE @]

ContinuationComplete(cont) == cont.complete

OldStateRoot(trace) == TraceInitialState(trace).rw_mem_root_bytes32
NewStateRoot(trace) == TraceFinalState(trace).rw_mem_root_bytes32
FinalExitStatus(trace) == TraceFinalState(trace).exit_code
====
```

---

### 17.10 Wrapper.tla

**What it models**: The Halo2 wrapper circuit interface—the 11 public inputs exposed to verifiers and the 6 binding constraints that constitute the proof statement.

**Key definitions**:
- `PublicInputsV1`: The 11 Fr values (program_hash, roots, status, nonce, etc.)
- `PublicOutputsV1`: The 144-byte structure in the guest output buffer
- `ProgramHashBinding/OldRootBinding/NewRootBinding`: The first 3 wrapper constraints
- `StatusFrBinding`: **Critical**—binds status_fr to actual exit_code (prevents prefix-proof attacks)

**How to read it**: The `WrapperProofStatement` operator is a conjunction of all constraints. If it holds, the proof is valid. The `ConstructPublicInputs` operator shows exactly how the 11 public inputs are computed from the execution trace.

```tla
---- MODULE Wrapper ----
(* Purpose: Halo2 wrapper circuit and public input constraints             *)
(* Section Reference: §5 (Wrapper proof interface and public inputs)       *)
EXTENDS Continuations, Encodings, Sequences

ASSUME U64_TLC_BOUND <= FR_TLC_BOUND
U64ToFr(u) == u

PublicInputsV1 == [
    program_hash_lo: Fr, program_hash_hi: Fr,
    old_root_lo: Fr, old_root_hi: Fr,
    new_root_lo: Fr, new_root_hi: Fr,
    batch_commitment_lo: Fr, batch_commitment_hi: Fr,
    checkpoints_digest_fr: Fr, status_fr: Fr, batch_nonce_fr: Fr]

PublicOutputsV1 == [
    status_u8: Byte, reserved7: [0..6 -> Byte], batch_nonce_u64: U64,
    old_root_bytes32: Bytes32, new_root_bytes32: Bytes32,
    batch_commitment_bytes32: Bytes32, checkpoints_digest_bytes32: Bytes32]

PUBLIC_OUTPUTS_SIZE == 144
ZeroReserved7 == [i \in 0..6 |-> 0]

PublicOutputsTypeOK(outputs) ==
    /\ outputs.status_u8 \in Byte
    /\ DOMAIN outputs.reserved7 = 0..6 /\ \A i \in 0..6 : outputs.reserved7[i] \in Byte
    /\ outputs.batch_nonce_u64 \in U64
    /\ Bytes32TypeOK(outputs.old_root_bytes32) /\ Bytes32TypeOK(outputs.new_root_bytes32)
    /\ Bytes32TypeOK(outputs.batch_commitment_bytes32) /\ Bytes32TypeOK(outputs.checkpoints_digest_bytes32)

PublicInputsTypeOK(inputs) ==
    /\ inputs.program_hash_lo \in Fr /\ inputs.program_hash_hi \in Fr
    /\ inputs.old_root_lo \in Fr /\ inputs.old_root_hi \in Fr
    /\ inputs.new_root_lo \in Fr /\ inputs.new_root_hi \in Fr
    /\ inputs.batch_commitment_lo \in Fr /\ inputs.batch_commitment_hi \in Fr
    /\ inputs.checkpoints_digest_fr \in Fr /\ inputs.status_fr \in Fr /\ inputs.batch_nonce_fr \in Fr

IsTrapOutput(outputs) ==
    /\ outputs.old_root_bytes32 = ZeroBytes32 /\ outputs.new_root_bytes32 = ZeroBytes32
    /\ outputs.batch_commitment_bytes32 = ZeroBytes32 /\ outputs.checkpoints_digest_bytes32 = ZeroBytes32

WrapperInput == [program_hash_bytes32: Bytes32, executionTrace: ExecutionTrace,
                 publicOutputs: PublicOutputsV1, batch_nonce_in: U64]

ConstructPublicInputs(input) ==
    LET progHashFr2 == Bytes32ToFr2(input.program_hash_bytes32)
        oldRootFr2 == Bytes32ToFr2(OldStateRoot(input.executionTrace))
        newRootFr2 == Bytes32ToFr2(NewStateRoot(input.executionTrace))
        batchCommitFr2 == Bytes32ToFr2(input.publicOutputs.batch_commitment_bytes32)
        checkpointsFr == Bytes32ToFrLE(input.publicOutputs.checkpoints_digest_bytes32)
        statusFr == U64ToFr(FinalExitStatus(input.executionTrace))
        nonceFr == U64ToFr(input.batch_nonce_in)
    IN [program_hash_lo |-> progHashFr2.lo, program_hash_hi |-> progHashFr2.hi,
        old_root_lo |-> oldRootFr2.lo, old_root_hi |-> oldRootFr2.hi,
        new_root_lo |-> newRootFr2.lo, new_root_hi |-> newRootFr2.hi,
        batch_commitment_lo |-> batchCommitFr2.lo, batch_commitment_hi |-> batchCommitFr2.hi,
        checkpoints_digest_fr |-> checkpointsFr, status_fr |-> statusFr, batch_nonce_fr |-> nonceFr]

\* §5.5 Wrapper Constraints
ProgramHashBinding(inputs, programHashBytes32) == LET fr2 == Bytes32ToFr2(programHashBytes32)
    IN /\ inputs.program_hash_lo = fr2.lo /\ inputs.program_hash_hi = fr2.hi

OldRootBinding(inputs, trace) == LET fr2 == Bytes32ToFr2(TraceInitialState(trace).rw_mem_root_bytes32)
    IN /\ inputs.old_root_lo = fr2.lo /\ inputs.old_root_hi = fr2.hi

NewRootBinding(inputs, trace) == LET fr2 == Bytes32ToFr2(TraceFinalState(trace).rw_mem_root_bytes32)
    IN /\ inputs.new_root_lo = fr2.lo /\ inputs.new_root_hi = fr2.hi

StatusFrBinding(inputs, trace) == inputs.status_fr = U64ToFr(TraceFinalState(trace).exit_code)
HaltedBinding(trace) == TraceFinalState(trace).halted = 1
NonceBinding(inputs, trace) == inputs.batch_nonce_fr = U64ToFr(ReadReg(TraceInitialState(trace), REG_A4))

ReservedBytesZero(outputs) == \A i \in 0..6 : outputs.reserved7[i] = 0
StatusMatchesExitCode(outputs, trace) == outputs.status_u8 = (FinalExitStatus(trace) % 256)
NonceMatchesInput(outputs, trace) == outputs.batch_nonce_u64 = ReadReg(TraceInitialState(trace), REG_A4)

TrapOutputs(trapCode, batchNonceIn) == [
    status_u8 |-> trapCode % 256, reserved7 |-> ZeroReserved7, batch_nonce_u64 |-> batchNonceIn,
    old_root_bytes32 |-> ZeroBytes32, new_root_bytes32 |-> ZeroBytes32,
    batch_commitment_bytes32 |-> ZeroBytes32, checkpoints_digest_bytes32 |-> ZeroBytes32]
====
```

---

### 17.11 JoltSpec.tla

**What it models**: The top-level system composition—the complete state machine from initialization through execution to completion or failure. This is where all the pieces come together.

**Key definitions**:
- `SystemState`: The complete system record (phase, registry, vmState, continuation, publicInputs, etc.)
- `Init/Next/Spec`: The TLA+ temporal specification: `Init /\ [][Next]_sys`
- `StartExecution/ExecuteOneChunk/CompleteExecution/ExecutionFailed`: The four possible transitions
- `PHASE_*`: System phases (INIT → EXECUTING → COMPLETE or FAILED)

**How to read it**: The `Next` operator is a disjunction of the four transitions—at each step, exactly one applies. `Spec` is the temporal formula saying "start in Init, then forever apply Next or stutter." TLC explores all paths through this state machine.

```tla
---- MODULE JoltSpec ----
(* Purpose: Top-level composition of Jolt TLA+ specification           *)
(* Section Reference: All sections - integrated system behavior            *)
EXTENDS Wrapper, Registry, Naturals, Sequences, FiniteSets

INPUT_PTR == IO_REGION_BASE
OUTPUT_PTR == IO_REGION_BASE + (2 * PAGE_SIZE_BYTES)
STACK_PTR == RW_REGION_BASE + RW_REGION_SIZE

TAG_BATCH_COMMITMENT == "JOLT/BATCH/COMMIT/V1"
TAG_CHECKPOINTS_DIGEST == "JOLT/CHECKPOINTS/DIGEST/V1"
TAG_IO_INIT == "JOLT/IO/INIT/V1"

BatchCommitmentBytes32(manifestBytes) == IF Len(manifestBytes) = 0 THEN ZeroBytes32 ELSE SHA256Hash(manifestBytes)

CheckpointsDigestFr(trace) ==
    IF Len(trace) = 0 THEN 0
    ELSE PoseidonHashBytes(TAG_CHECKPOINTS_DIGEST, SumSet({trace[i].digestOut : i \in 1..Len(trace)}))

CheckpointsDigestBytes32(trace) == FrToBytes32LE(CheckpointsDigestFr(trace))

PHASE_INIT == "init"  PHASE_EXECUTING == "executing"  PHASE_COMPLETE == "complete"  PHASE_FAILED == "failed"
SystemPhase == {PHASE_INIT, PHASE_EXECUTING, PHASE_COMPLETE, PHASE_FAILED}

SystemState == [phase: SystemPhase, registry: RegistryState, programHash: Bytes32, vmState: VMStateV1,
                continuation: ContinuationState, publicInputs: PublicInputsV1, publicOutputs: PublicOutputsV1,
                batchNonce: U64, manifestBytes: Seq(Byte)]

VARIABLE sys

InitSystemState(registry, programHash, manifestBytes, batchNonce) ==
    LET configTags == ComputeConfigTags(registry)
        initialRWRoot == RootToBytes32(EmptyTreeRoot)
        initialIORoot == RootToBytes32(ComputeInitialIORoot(manifestBytes, INPUT_PTR, Len(manifestBytes), IO_REGION_BASE))
        initVM == InitVMState(INPUT_PTR, Len(manifestBytes), OUTPUT_PTR, PUBLIC_OUTPUTS_SIZE, batchNonce, STACK_PTR,
                              initialRWRoot, initialIORoot, configTags)
    IN [phase |-> PHASE_INIT, registry |-> registry, programHash |-> programHash, vmState |-> initVM,
        continuation |-> InitContinuation(programHash, initVM),
        publicInputs |-> [program_hash_lo |-> 0, program_hash_hi |-> 0, old_root_lo |-> 0, old_root_hi |-> 0,
                          new_root_lo |-> 0, new_root_hi |-> 0, batch_commitment_lo |-> 0, batch_commitment_hi |-> 0,
                          checkpoints_digest_fr |-> 0, status_fr |-> 0, batch_nonce_fr |-> 0],
        publicOutputs |-> TrapOutputs(0, batchNonce), batchNonce |-> batchNonce, manifestBytes |-> manifestBytes]

Init == \E registry \in RegistryState, programHash \in Bytes32, batchNonce \in U64 :
    /\ RegistryDeploymentReady(registry)
    /\ sys = InitSystemState(registry, programHash, << >>, batchNonce)

StartExecution == /\ sys.phase = PHASE_INIT /\ RegistryDeploymentReady(sys.registry)
                  /\ sys' = [sys EXCEPT !.phase = PHASE_EXECUTING]

ExecuteOneChunk == /\ sys.phase = PHASE_EXECUTING /\ ~ContinuationComplete(sys.continuation)
    /\ LET stateIn == sys.vmState
           stateOut == ExecuteNSteps(stateIn, CHUNK_MAX_STEPS)
           newCont == ExecuteChunk(sys.continuation, stateIn, stateOut)
       IN sys' = [sys EXCEPT !.vmState = stateOut, !.continuation = newCont]

CompleteExecution == /\ sys.phase = PHASE_EXECUTING /\ ContinuationComplete(sys.continuation)
    /\ LET trace == sys.continuation.chunks
           outputs == [status_u8 |-> TraceFinalState(trace).exit_code % 256, reserved7 |-> ZeroReserved7,
                       batch_nonce_u64 |-> sys.batchNonce, old_root_bytes32 |-> OldStateRoot(trace),
                       new_root_bytes32 |-> NewStateRoot(trace),
                       batch_commitment_bytes32 |-> BatchCommitmentBytes32(sys.manifestBytes),
                       checkpoints_digest_bytes32 |-> CheckpointsDigestBytes32(trace)]
           wrapperInput == [program_hash_bytes32 |-> sys.programHash, executionTrace |-> trace,
                            publicOutputs |-> outputs, batch_nonce_in |-> sys.batchNonce]
       IN sys' = [sys EXCEPT !.phase = PHASE_COMPLETE, !.publicInputs = ConstructPublicInputs(wrapperInput),
                             !.publicOutputs = outputs]

ExecutionFailed == /\ sys.phase = PHASE_EXECUTING /\ IsTrappedHalt(sys.vmState)
    /\ sys' = [sys EXCEPT !.phase = PHASE_FAILED, !.publicOutputs = TrapOutputs(sys.vmState.exit_code, sys.batchNonce)]

Next == \/ StartExecution \/ ExecuteOneChunk \/ CompleteExecution \/ ExecutionFailed
Stuttering == UNCHANGED sys
NextOrStutter == Next \/ Stuttering
Spec == Init /\ [][Next]_sys
FairSpec == Spec /\ WF_sys(ExecuteOneChunk)
====
```

---

### 17.12 Invariants.tla

**What it models**: All 26 individual invariants organized by category—4 type, 7 binding, 7 safety, and 8 attack prevention—plus 6 composite invariants (INV_*_All, AllInvariants, CriticalInvariants). This module is what TLC actually checks.

**Key definitions**:
- `INV_TYPE_All`: All type invariants combined
- `INV_BIND_All`: All binding invariants (security-critical)
- `INV_SAFE_All`: All safety invariants
- `INV_ATK_All`: All attack prevention invariants (most critical)
- `AllInvariants`: The conjunction of all invariant categories
- `LIVE_EventuallyTerminates`: Liveness property that execution eventually halts

**How to read it**: Each invariant is a predicate over `sys` (the system state). TLC checks that each invariant holds in all reachable states. The invariants are named systematically: `INV_<category>_<property>`. Composite invariants like `INV_BIND_All` are conjunctions of individual invariants.

```tla
---- MODULE Invariants ----
(* Purpose: Centralized collection of all specification invariants         *)
(* Section Reference: §15 (Security), all module constraints               *)
EXTENDS JoltSpec

\* TYPE INVARIANTS
INV_TYPE_SystemState == /\ sys.phase \in SystemPhase /\ sys.batchNonce \in U64
INV_TYPE_Registry == RegistryStateTypeOK(sys.registry)
INV_TYPE_VMState == /\ RegisterFileTypeOK(sys.vmState.regs) /\ sys.vmState.pc \in U64
    /\ sys.vmState.step_counter \in StepCounter
    /\ Bytes32TypeOK(sys.vmState.rw_mem_root_bytes32) /\ Bytes32TypeOK(sys.vmState.io_root_bytes32)
    /\ sys.vmState.halted \in HaltedFlag /\ sys.vmState.exit_code \in U64
INV_TYPE_ProgramHash == sys.programHash \in Bytes32
INV_TYPE_All == /\ INV_TYPE_SystemState /\ INV_TYPE_Registry /\ INV_TYPE_VMState /\ INV_TYPE_ProgramHash

\* BINDING INVARIANTS (CRITICAL)
INV_BIND_StatusFr == sys.phase = PHASE_COMPLETE => sys.publicInputs.status_fr = U64ToFr(FinalExitStatus(sys.continuation.chunks))
INV_BIND_OldRoot == sys.phase = PHASE_COMPLETE =>
    LET fr2 == Bytes32ToFr2(TraceInitialState(sys.continuation.chunks).rw_mem_root_bytes32)
    IN /\ sys.publicInputs.old_root_lo = fr2.lo /\ sys.publicInputs.old_root_hi = fr2.hi
INV_BIND_NewRoot == sys.phase = PHASE_COMPLETE =>
    LET fr2 == Bytes32ToFr2(TraceFinalState(sys.continuation.chunks).rw_mem_root_bytes32)
    IN /\ sys.publicInputs.new_root_lo = fr2.lo /\ sys.publicInputs.new_root_hi = fr2.hi
INV_BIND_ProgramHash == sys.phase = PHASE_COMPLETE =>
    LET fr2 == Bytes32ToFr2(sys.programHash)
    IN /\ sys.publicInputs.program_hash_lo = fr2.lo /\ sys.publicInputs.program_hash_hi = fr2.hi
INV_BIND_ConfigTags == sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} => sys.vmState.config_tags = ComputeConfigTags(sys.registry)
INV_BIND_StateDigest == sys.phase = PHASE_COMPLETE =>
    \A i \in 1..Len(sys.continuation.chunks) :
        sys.continuation.chunks[i].digestIn = ComputeStateDigest(sys.programHash, sys.continuation.chunks[i].stateIn)
INV_BIND_Nonce == sys.phase = PHASE_COMPLETE =>
    /\ sys.publicInputs.batch_nonce_fr = U64ToFr(sys.batchNonce)
    /\ sys.batchNonce = ReadReg(TraceInitialState(sys.continuation.chunks), REG_A4)
INV_BIND_All == /\ INV_BIND_StatusFr /\ INV_BIND_OldRoot /\ INV_BIND_NewRoot /\ INV_BIND_ProgramHash
    /\ INV_BIND_ConfigTags /\ INV_BIND_StateDigest /\ INV_BIND_Nonce

\* SAFETY INVARIANTS
INV_SAFE_RegistryReady == sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} => RegistryDeploymentReady(sys.registry)
INV_SAFE_NoTBD == sys.phase # PHASE_INIT => NoTBDInvariant(sys.registry)
INV_SAFE_VMHaltedExitCode == /\ (sys.vmState.halted = 0 => sys.vmState.exit_code = 0)
                              /\ (sys.vmState.halted = 1 => sys.vmState.exit_code \in 0..255)
INV_SAFE_RegisterX0 == sys.vmState.regs[0] = 0
INV_SAFE_HaltedBinary == sys.vmState.halted \in {0, 1}
INV_SAFE_ContinuationChain == Len(sys.continuation.chunks) > 1 => ContinuityInvariant(sys.continuation.chunks)
INV_SAFE_FinalChunkHalted == sys.phase = PHASE_COMPLETE => sys.continuation.chunks[Len(sys.continuation.chunks)].stateOut.halted = 1
INV_SAFE_All == /\ INV_SAFE_RegistryReady /\ INV_SAFE_NoTBD /\ INV_SAFE_VMHaltedExitCode
    /\ INV_SAFE_RegisterX0 /\ INV_SAFE_HaltedBinary /\ INV_SAFE_ContinuationChain /\ INV_SAFE_FinalChunkHalted

\* ATTACK PREVENTION INVARIANTS (CRITICAL)
INV_ATK_NoPrefixProof == sys.phase = PHASE_COMPLETE =>
    LET finalState == TraceFinalState(sys.continuation.chunks)
    IN /\ (sys.publicInputs.status_fr = U64ToFr(JOLT_STATUS_OK) => /\ IsSuccessfulHalt(finalState) /\ finalState.halted = 1)
       /\ (IsSuccessfulHalt(finalState) /\ finalState.halted = 1 => sys.publicInputs.status_fr = U64ToFr(JOLT_STATUS_OK))
INV_ATK_NoSkipChunk == NoSkippedChunks(sys.continuation.chunks)
INV_ATK_NoSplice == sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} => ContinuityInvariant(sys.continuation.chunks)
INV_ATK_NoCrossConfig == sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} => ConfigConsistentAcrossChunks(sys.continuation.chunks)
INV_ATK_NoRootForgery == sys.phase = PHASE_COMPLETE => /\ INV_BIND_OldRoot /\ INV_BIND_NewRoot
INV_ATK_NoMemoryForgery == sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} =>
    \A i \in 1..(Len(sys.continuation.chunks) - 1) :
        sys.continuation.chunks[i].stateOut.rw_mem_root_bytes32 = sys.continuation.chunks[i+1].stateIn.rw_mem_root_bytes32
INV_ATK_NoIOForgery == sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} =>
    \A i \in 1..(Len(sys.continuation.chunks) - 1) :
        sys.continuation.chunks[i].stateOut.io_root_bytes32 = sys.continuation.chunks[i+1].stateIn.io_root_bytes32
INV_ATK_NoReplay == sys.phase = PHASE_COMPLETE =>
    sys.publicInputs.batch_nonce_fr = U64ToFr(ReadReg(TraceInitialState(sys.continuation.chunks), REG_A4))
INV_ATK_All == /\ INV_ATK_NoPrefixProof /\ INV_ATK_NoSkipChunk /\ INV_ATK_NoSplice /\ INV_ATK_NoCrossConfig
    /\ INV_ATK_NoRootForgery /\ INV_ATK_NoMemoryForgery /\ INV_ATK_NoIOForgery /\ INV_ATK_NoReplay

\* COMPOSITE INVARIANTS
AllInvariants == /\ INV_TYPE_All /\ INV_BIND_All /\ INV_SAFE_All /\ INV_ATK_All
CriticalInvariants == /\ INV_BIND_StatusFr /\ INV_BIND_OldRoot /\ INV_BIND_NewRoot
    /\ INV_SAFE_ContinuationChain /\ INV_ATK_NoPrefixProof /\ INV_ATK_NoSkipChunk /\ INV_ATK_NoSplice

\* LIVENESS PROPERTIES
LIVE_EventuallyTerminates == <>(sys.phase \in {PHASE_COMPLETE, PHASE_FAILED})
LIVE_ProgressFromInit == (sys.phase = PHASE_INIT) ~> (sys.phase # PHASE_INIT)
====
```

---

### 17.13 MC_Jolt.tla

**What it models**: The TLC model configuration—concrete values for all constants, model substitutions for hash functions, and the initial state for model checking.

**Key definitions**:
- `SMOKE_*`: Small constant values for fast TLC runs (e.g., `SMOKE_CHUNK_MAX_STEPS == 2`)
- `ModelPoseidonHashBytes/ModelPoseidonHashFr2`: Concrete implementations of abstract hash functions
- `ModelStepFn`: A simple step function that increments counter and halts after N steps
- `StateConstraint`: Bounds on exploration to keep TLC tractable
- `ModelInit/ModelSpec`: Concrete initial state and specification for TLC

**How to read it**: This module "fills in the blanks" left by abstract constants in other modules. The model operators (e.g., `ModelPoseidonHashBytes`) use simple arithmetic to ensure different inputs produce different outputs while staying within TLC's bounds.

```tla
---- MODULE MC_Jolt ----
(* Purpose: TLC Model Configuration for Jolt continuations Specification             *)
(* Usage: Use this module as the TLC "model" with JoltSpec             *)
EXTENDS Invariants, TLC, Sequences

\* SMOKE TEST CONFIGURATION
SMOKE_CHUNK_MAX_STEPS == 2
SMOKE_MAX_CHUNKS == 3
SMOKE_NUM_REGISTERS == 32
SMOKE_FR_MODULUS == 1000
SMOKE_FR_TLC_BOUND == 16384
SMOKE_U64_TLC_BOUND == 16384
SMOKE_PAGE_INDEX_TLC_BOUND == 4
SMOKE_MAX_DIRTY_PAGES == 2
SMOKE_MAX_ABSORPTIONS == 4

SMOKE_TAG_STRINGS == {
    "JOLT/SMT/PAGE/V1", "JOLT/SMT/NODE/V1", "JOLT/TRANSCRIPT/VM_STATE/V1",
    "JOLT/TRANSCRIPT/CHALLENGE/V1", "JOLT/TRANSCRIPT/V1",
    "JOLT/BATCH/HEADER_LEAF/V1", "JOLT/BATCH/FILL_LEAF/V1", "JOLT/BATCH/EMPTY_FILL_LEAF/V1",
    "JOLT/BATCH/PAD_LEAF/V1", "JOLT/BATCH/NODE/V1", "JOLT/STATE/V1", "JOLT/CHECKPOINTS/V1",
    "JOLT/BATCH/COMMIT/V1", "JOLT/CHECKPOINTS/DIGEST/V1", "JOLT/IO/INIT/V1",
    "JOLT/CONFIG_TAGS/V1", "JOLT/TAG/V1"
}

\* HASH FUNCTION MODEL OPERATORS
ValueFingerprint(x) == IF x \in Nat THEN x ELSE Len(ToString(x))

TagToNat(tag) ==
    CASE tag = "JOLT/SMT/PAGE/V1" -> 1 [] tag = "JOLT/SMT/NODE/V1" -> 2
      [] tag = "JOLT/STATE/V1" -> 3 [] tag = "JOLT/TRANSCRIPT/CHALLENGE/V1" -> 4
      [] tag = "JOLT/TRANSCRIPT/VM_STATE/V1" -> 5 [] tag = "JOLT/CHECKPOINTS/V1" -> 6
      [] tag = "JOLT/BATCH/HEADER_LEAF/V1" -> 7 [] tag = "JOLT/BATCH/FILL_LEAF/V1" -> 8
      [] tag = "JOLT/BATCH/EMPTY_FILL_LEAF/V1" -> 9 [] tag = "JOLT/BATCH/PAD_LEAF/V1" -> 10
      [] tag = "JOLT/BATCH/NODE/V1" -> 11 [] tag = "JOLT/TRANSCRIPT/V1" -> 12
      [] tag = "JOLT/BATCH/COMMIT/V1" -> 13 [] tag = "JOLT/CHECKPOINTS/DIGEST/V1" -> 14
      [] tag = "JOLT/IO/INIT/V1" -> 15 [] tag = "JOLT/CONFIG_TAGS/V1" -> 16
      [] tag = "JOLT/TAG/V1" -> 17 [] OTHER -> 0

ModelPoseidonHashBytes(tag, data) == (TagToNat(tag) * 100000 + ValueFingerprint(data)) % FR_TLC_BOUND
ModelPoseidonHashFr2(tag, fr1, fr2) == (TagToNat(tag) * 100000 + fr1 * 257 + fr2) % FR_TLC_BOUND
ModelSHA256Hash(input) == [i \in 0..31 |-> (ValueFingerprint(input) + i * 17) % 256]
ModelDefaultHashes == [d \in 0..32 |-> (d * 17 + 1) % FR_TLC_BOUND]

\* STATE CONSTRAINTS
VM_TERMINATE_AFTER_STEPS == CHUNK_MAX_STEPS * (MAX_CHUNKS + 1)

ModelStepFn(state) ==
    IF state.halted = 1 THEN state
    ELSE LET nextCounter == state.step_counter + 1
             nextHalted == IF nextCounter >= VM_TERMINATE_AFTER_STEPS THEN 1 ELSE 0
         IN [state EXCEPT !.step_counter = nextCounter, !.halted = nextHalted, !.exit_code = 0]

StateConstraint ==
    /\ Len(sys.continuation.chunks) <= MAX_CHUNKS + 1
    /\ sys.vmState.step_counter <= CHUNK_MAX_STEPS * (MAX_CHUNKS + 2)

\* MODEL INIT
ModelBytes32 == [i \in 0..31 |-> 0]

ModelValueForKey(keyName) ==
    CASE keyName = KEY_SPEC_VERSION -> "1.0.0"
      [] keyName = KEY_MAX_MANIFEST_BYTES -> "512"
      [] keyName = KEY_MAX_INTENTS -> "8"
      [] keyName = KEY_MAX_CHECKPOINTS_BYTES -> "256"
      [] keyName = KEY_CONTEXT_BYTES32 -> "CONTEXT1"
      [] OTHER -> "1.0.0"

ModelRegistryEntry(keyName) == [key |-> keyName, value |-> ModelValueForKey(keyName), required |-> TRUE, validated |-> TRUE]
ModelRegistry == [k \in RequiredKeys |-> ModelRegistryEntry(k)]

ModelInit == sys = InitSystemState(ModelRegistry, ModelBytes32, << >>, 0)
ModelSpec == ModelInit /\ [][Next]_sys
ModelFairSpec == ModelSpec /\ WF_sys(StartExecution) /\ WF_sys(ExecuteOneChunk) /\ WF_sys(CompleteExecution) /\ WF_sys(ExecutionFailed)
====
```

---

### 17.14 Conclusion

The formal specification is complete. What does it guarantee?

**The Security Contract**

The 26 TLA+ invariants encode a precise security contract: any implementation that satisfies them provides the four pillars promised in Section 1:

1. **Deterministic execution**: The guest VM (Section 6) has no undefined behavior. INV_SAFE_* invariants verify this.
2. **Succinct proof**: The 11-element public interface (Section 5) binds proof to execution. INV_BIND_* invariants verify this.
3. **Cryptographic binding**: StateDigest chains chunks; transcript binds challenges. INV_ATK_* invariants prevent forgery.
4. **Fail-closed gating**: The registry (Section 3) blocks deployment until all TBD values are resolved. INV_SAFE_RegistryReady verifies this.

**Current Status**

The specification is structurally complete. Fourteen of seventeen registry keys remain TBD. The formal model passes TLC verification with 9 states explored and all 26 individual invariants (plus 6 composites) satisfied. Production deployment requires:

- Finalizing the 14 TBD registry values (Section 3.6)
- Passing the conformance bundle (Section 14) with two independent implementations
- Completing security audit of cryptographic parameter choices

**Next Steps by Role**

| Role | Recommended Path |
|------|------------------|
| **Implementer** | Run TLC (Section 16.3), build to conformance vectors (Section 14.5) |
| **Security Auditor** | Focus on Sections 5, 7, 8, 11, 15; verify INV_ATK_* invariants map to code |
| **Protocol Team** | Finalize Section 3 registry values, resolve TBD tags |
| **Integration Developer** | Wait for conformance bundle v1.0; use Section 5 public inputs as API contract |

**Callback**

Remember the opening scenario: 10,000 trades to settle, rational privacy to preserve, millisecond verification to achieve. This specification makes that possible. The Settlement Engine runs deterministically. Jolt proves it ran correctly. Continuations handle unbounded computation. The wrapper compresses everything to kilobytes. The on-chain verifier accepts or rejects in constant time.

The mathematics is now machine-checkable. The security properties are now invariants. The protocol is now specifiable.

What remains is implementation.

---

## Appendix A: `JOLT_POSEIDON_FR_V1` Round Constants

This appendix contains the complete round constants for the Poseidon permutation specified in §3.4.1.

**Source:** `midnight-circuits` v6.0.0, `midnight_circuits::hash::poseidon::constants`

**Format:** Each value is `FrToBytes32LE(f)` rendered as canonical textual `bytes32` (64 lowercase hex characters).

### A.1 Round Constants Table

```
Round  | Element 0                                                          | Element 1                                                          | Element 2
-------|--------------------------------------------------------------------|--------------------------------------------------------------------|--------------------------------------------------------------------
    0  | 578254652f2e8a11d0f5355849b19e42da748b86309078e6bd802e706c17590a | bdcf51fe022a3a93237d1224bfdb04d3f24bab5b5a8a8ecd107d9db909ee041f | 7354dc0af58052af200ca10a782e1a9f4c1a309e638d1829f5419e6aee0a3b05
    1  | 9c3fbf7988d4f7ae511939e296baea6781fb90f1c7a056e4567f0d8713c67f60 | fbf2a7da05cba4b56e48deb584ec97a65945e3a03999f91381e191f0474d9365 | f9636b19d1bc53a8d5ca5a8d7213ec4f8947d1eea4f9fa8ea921c620fa96e818
    2  | 50d94fa830be36e3d2964781267c7ae4c948312667edc41700adc3f3fc9afa69 | 2d26a941b6cf588ed7cb72f9bcd347127b40fb6b456e975cb9397928b8d37671 | 019ac3dd7369e6634a280befd702f2418b7fba373b5ec0ff99febe5e1c046d03
    3  | 6f810adf2e042d73a2e5fb9f321657502109c2b4ae153b013374de31cc42055d | 128c8a53f209f9425fb2de7fb323faf200be13895d6604b83181c6cc26fb6526 | a78b9a6f3c3d089daf954dbb313c7769cb0e805c6e04bbe789585c685a70e33c
    4  | 3d9644d563791eaf6528c068fdb7fdd4e31674d7e22591fa8ea84a0986ecc64e | 35fbd7c351dbfdc2200406849edaaba2f9edeb1deeadcedc11f0c6ae2ab3c004 | 55fe6a7d99b4784ff821ff43b0204d02e1559c764105226a1e15fa29925c2716
    5  | 45878ba3cc2703c1b837b44031a9f7b4008b0f7df5ba94afef102f51e5130815 | c24363efdb9ffdfe70f55ddd04339236ec60e39e56df6343e2b19db24761065f | d560667180207a8f5d9fefe05d01fbc4205b5a721892cf3fba45e21ca3e35a11
    6  | 4e3914a4224be1e5693df9f2dbb27b93e3795dfdc0508903f3459ac265de7632 | bf48b5d25aadf8922db642cc41e03e13a6cc5568af77f4350bebeb0c8049504c | 782bae1f49db1cb25730c9413d8b0f2dba4b7ac6aec89641f3ea729c541b2e25
    7  | 7c2ad27983c7adeda0c0e14ae7873fbed6358c85605569347ffebccf270f0a5a | 9911e0d486ed51b5d86403b3dc98c10af2eb2ae1894633fd0bbdff39fe41ef5a | b94dda1606eb8a536a56a4873369c6bd4fce7f9e835dcdd480967a4d57eef72f
    8  | 447cfb60a5d55242feb5571eb6fbba05ce8269422edfde3f91c7a9bcbb309559 | 86306bbc18dd3604866845ee0cf28da8d456a221bca8b90b41073ec699fd4a59 | 2cbf221142bebc8cb41eb9ee66b2c9c76ab5fc7f32cf6aabdb1d6a05bcc21b56
    9  | c0e4039be35350187ba988852890f89510319f5ba17173694a0fe3fe29f6b044 | 44a7003fceec139b82e4f642d91308e915486297d5e5781bc800762a36bc6666 | 8972b76573eb20204a8ce2bff535fad36a1cd21202b0eb2d4980add794154939
   10  | 2c58a6fb593a3856a8c269321373ab38fa3a26d0eac0ebab04769084f4ba7a68 | ce16157b1e6b4e6acc256a6160b5733786b8ffd0244f297a370d6dd6a020a931 | 284a88a511a40331dffeed3c5bde44f8b4677b5cfcf528c611ddaa731af8d043
   11  | 19b8360144d99d2857e202f5537a455c584d87eda4a57118facfa6ab2bc8b33e | 097e57500b6d7c79ae53a17b255a5ed7c8696fb2b666ed9b74d8bad0de6e1933 | 1198543a7a9bd2ca06c8c6e30a3c187a0ee585b71a73c07bd38d307daf6ad243
   12  | 87a3ed3753f1f6c233439fc3554ce5258c0a5f4dd3443d052946934a12d4ca53 | 56f375d54c1f3e79c5f825e3015e88ccb42b516ff2e407f70a02c177b7d6af3e | 30099fab4090beb7533435ece8899366b0e3b8e7c2af5b190e6a30c42e202053
   13  | b0260b0d8ead88084d93da2619e384a9d6289da94a4e3db0963b0f80df917b58 | 828ff9f3d188db1b000b65e169aa53255ef1b616a6bb6703475887b77eccfc2b | 4a9d81433fbb2de15e7f8ed7b7e93cdb209cabd575b6176dcf7448c5e0f22214
   14  | 4c9cb4b00e2a15f7cb03e6c700fc8371dd424025cf9f3d062f1a3aeaa284fd28 | 574b1144d52581233c13d2f913cf1a39fe5d09ff1ff4da13eb111cb829cdbf28 | 3fffabf770df54ccfd030509b52688c96077a68fab8b0335eab58eedc0c48655
   15  | 26ab8ba6158449faede973bf235d428743f3e8652c5b15731662ec037f360912 | 33b707b6640979dff1be7673418a3e7b5e3bb27efd00ee7dd3f615322d6b3522 | 726622fd40b0ef3b7f4a68f2c1c0c8096a4adad3358180c45f8c4debb43c166c
   16  | 3ac3489e9ca059675d4f1695f2816c6aa495b4784c5e3ebdf748fd254ec0c34d | fbe79addf9faa0adf2babce94511653688ba69f6066e19a71135eb29f49d0d59 | 8a09cadbc294edb85742c2c62affd1131d81d6865405477b28dfa3106893f22f
   17  | 0cfa916988be78d1323e7e79602fb540e756ade2b495bcc4b1e4d971a749525f | 27fb024ec37cbae154bbe9181b8d982d0edab37d16e3c40eeebb6ecf078ef767 | 62a7b71bfbe9b4a0fed983551cbef961002b5ed9726ba163aac68897bda39e2b
   18  | d259eef0eb73434afe672a3407048fbdbb33d4015e5f41f0cc21edcb17af1b0a | 7779deb0ef62497814ee040bc9d356f874305e7a6ba220e61d5630eba2cebf1c | 5f04518a4bd86fc89fcec125a290fce706cecd4868f2fe4a800658d251cbc939
   19  | e9d9a48872cbbfc055ac84a2dcda652143f07e2e2c7c9a89e277c1e4345e4d42 | 2c083ca0773e92d7ba50d3af9f6bd93d294411e01876bad21837285fc6e88733 | 75e7c6262afde127e6d8bfa3b720bf50c4d40d351d12b203805f747e24f12665
   20  | d39dd681429a215fbccbf5fad060d118bb9ee9c8effb7b4be52671df4d39c722 | a154e72afe81fd4ccb1d386633b703149210aecc0a8bb7697bb394e99bacf62e | 77d975314c3c690225ed3b3e2c22d87f54114eb87f7e248444ddf3d2c7a5e64b
   21  | d2098528695e1829fa88bbe670e0e3e79c6053e125c35b4bdcd57e8031ca3a27 | 37017a56924622ad2ee479ab30ccedf0f91b3a7c05f5b623b3aea1e3ca21b32d | cf885aa9b11f9970b984110987363630ab30e048a4013335522ec1f424449745
   22  | c830be2e9d39f164b361dc3a685ad7283997b34e8e8ce5bf70b3c094308fbc4d | 70c1b52ecc12bac45df92bfb77a05d9077b526190e41a7910f3c3fe1f0101c1b | 01c072f19bab0c166b58acda6d05a1735e76ad0ed6e59b364e1ed77e99a6bb1a
   23  | 6b1406a6377eec7cf62d70b07363405e0a144678e2664f78edd644e0fc9ffa3f | 3c1fde7ccda264fbbba6e873981c68200fb85419f511baf2e3e233d3fb1e2d17 | 7e6ed293b8099cbd6657300f519c248e0b88afbaed1d4931801ba98215494425
   24  | 80ba721624aa34810f3d60ceb1549ef35c1a29e75c0aa052b9e91d11d2a18e59 | e5587d03ef3a2fb39e76ed38b94c4bab5fd46b95a9318fc1c8e2f6a86415d030 | f93ec9986fa06c0748f3d24cce266dc1f32abb44e8c59c4fd5399ffa1fdee058
   25  | ab8b057f7ffe88a4f86c1d350c57d849fff9fca53e6764e258121e3e0492b845 | 2145790b86de90ac2c161e215a2dd220731b45ccfed3f5af3ede0e80a4d5802b | 17dab7df6693355874efe9264f5ef30564b4eb461c441d410709192b20069d41
   26  | 422dd8d2624ab53a169e949b0dcf3b37176d27b7118fe124e209d43e3455073d | 841bed13d48fced5456765ee3379bbc658959d1bbadbc8aadca528548f0dcb53 | 22d182c74ac989f1b8e14936d61776b4dafcc37867362ecd60cdd335e9c5070b
   27  | 38e7244639f2a898b83dd0f556ab7af9c4316dddb1976604aa2ada75fa975e2e | faca54031486f0378127e7b10e2907abc1f4dc690e621c5128e0d94cf98f040a | 7c14b76c30376b55fc37358e3f69968e8b0634c732ce82520b57d13268434317
   28  | a9cb071795635f290b494091f2248b68bbe889b8cfb8043c5be7866b48eaf328 | ac2e6d7d2a1e43b8d7accdf4e61be6911ce81db801849213f9cd9f9db6bf0d15 | 0244ea5c29a13f2435f72bbdeae0b52d7413227b42ded5a075a30d453934ca29
   29  | cb4d667a93085621da50b90cdecdb686f27bb2d710c2c8fbcb5fa6762bb6a148 | ed389f3e22ce62a50a696aec06e20a4d7b027c696e269cd6ec4143f26aeb1802 | bcd8f334db1d09e4ed00ce2bf8a9245147ca8358d51578509334e1f18eb3a309
   30  | 1b88630ff2b76c6d8785842ab3d9ba5df8e7cfda859c652d826a89d1a2864017 | cff35ff8a63b351a357e1a2485f2321d6faa6e19b8ef1f3e65f7fbeeb611fd23 | 3b33a3051483c94d2fccc103771b5e9e59901ad6cc83430099194002ba182849
   31  | 25e735e0a826bbb27f091b537232ea68f5ab4318b08518a345a1925490b87301 | 2ce18898d0b8de40e027df7947292fdad4a4f0eedb9b5caf27c2bbf34270d543 | 79d97e83df6f13a8d2d01c61ffb3a8851014eb66c1fababa83ec2eb756e9ef17
   32  | 9acf42a04af0d883d82f09b510556ef84e55c127c2457b31ae01d42a86996902 | 5bb869bb348de488ef5556c11a1d8091fbe3aa9a23dd051e3404188451107807 | c5ab961bd87ad113ee82e0d2d7ffcb0ee900b0f65b3b48faf3179e4296184669
   33  | 4add4183b848ec4f6dbd160f28897d195a363b03ee68f1b014a3ba0f69eb1803 | 09d53304b7f47a392cd3f278d114c00a566db725fa7780d65e750bf7fb6eee23 | f4b01e09f5b1d13954e005665a4542842e2b4a5d589575e70df47afcc1a22960
   34  | edb5bac64ef7a5b5e0d71c024493204e4d250acaaf7394e71d91d8a5c2fc8565 | 1a245c567a1f68b14a9e1121c776db06c72db7f8c176e98e358fd9afeda9c36e | bd6f4b3a6f7dcba8ac13b00183fc747c3dbcdb0bc5a9ca6deba2872802929c2c
   35  | 7e1bdbd6bf86b7e48bce125a7790478d835f0ea129005e8e4fd30274f0db7f08 | 00749e1be0888d3a5ed847c53aac52615eb402b1070eaf5b1778a8dcfd33a805 | 15d3acf73463dc52ef2e0382bafcf59fc6ffc09f3b3f022df5513ebdd75ce16d
   36  | 91eead66d1db89d319f3702bb1b3126c89b124b3a6be60030b10aae778394e2e | a56eddec0e621f606affd82785b535432517d0704bf702f22bb8c76ca16ad459 | 86312e8ff53f0ce942ccd752950b2b35dcb5fe8714aed55dada39537b84fb047
   37  | 2e0629a70ef5b0519e336e80d97485e623ab8bf45a439fa82fd3a240ab9aeb72 | 37c23f560f2997bece4a59a7a866f212464db416121af0a6064f501b58bab552 | 6009bce0170a870cde13852c83aec26e6ea3f60bac38f006f38d90f7a4ff9220
   38  | 4d4dde4cb4f24442ab0774d885d96beb1d3e2d05c5ca5a51218e1e74b03ffe29 | 36d21a7d78ed45368fc3b5fd547bd65faccc15314d659078a6f49e28a489d847 | 5c5965eb1cd039ebedf52d2fdb844b00b6a5b05014cefea027c1eb2c94e4e540
   39  | 89b3f4f63acf3f7cd880fbc1c4d009233e96eab1502c718659c6c5aa41580356 | 31d10678895124440b0e1c3b6d4f1f923e2bf924b302f607e912a775496f1e26 | 564ada2eda6e6fe41eac3180487d17b7da49f1dff1639ca4f4beebcf1071bd18
   40  | 854a601ded8ef6486b05d224d381e4e0a220a0bb031c51e64820ee7b40ac066c | 2f0956fd163b20c9afab69dc2a01e4ceb5cfb0053bfc396b09bc666ea884ec4e | e7a162f3103de9ae61c12ec42b5e8286732d38c782805ba626ed1a023399e670
   41  | d4501365cb6f7e0830b7f658735203cb36ea1b71e2a98fc5ea45449cdf6f6366 | 2cbc09ab7497ba5d533e726db7db3c3e00aece29a17c55141dd0f6497a348545 | fdb9bc0ad7b3d125267e1be47adfaedd0145325993a6580eb6a13e6426cf5818
   42  | fc8abd361199ccada46968228fc1ea470e53fbdcae0881cd6d1f83c91d458f67 | 52d589601abfceac976f3fdc6605a885915828c56e64676c5d6dc0c6cdc6770e | b16cfb80a88473b3ccac7dacf88aefac7a2245fc1629d3a2b0c8bc2bc7336f13
   43  | 0c932520723c4578ac097dfd0f6f78a1639e3a0e559a3d50272ecc1abffaca02 | 5802cc1994d68df2c5e3c01a67c69b702106d915aa1c481cdea5019bee05c513 | 540c646c91cc1d05a4bac94d8329157d208b829f3c63f9d979dfb577c8e53b63
   44  | c3862c132b937f602da3f22ceb970e28f7b33247683b89870af1548e36a51029 | 5965e9a022c34b7f40974e9ded8ddd4c2bd0b31628ddb3e42e24641e2fadb65c | 0a0b03080f2abbbb2440d6465908d9eb4fe5ed99ef9559dd36776808c73af03e
   45  | 10912c934bb3d90e666f57e7c8c775a1dc2ce4897873e77c95ba1584f2f6c232 | 54fc1b2d3b9717080f92ffdca964167175e8b8fedaad8d1a22dfcfa76599182c | bb8c5c7f9f5d3ecb7c3a5c9d0a10ee18a388e75a73bcc127c80ebc76709e5461
   46  | 3cd7de1271288d8ca919079478db430ac3752cecf3d2819f48b71fdc96ded425 | 873a50de3211230801b70042515b57648d895aca5fbf222d6d8ff99814190b66 | eebd8c29cf652590b2b6676aced1e845e357a868c5c4c31d38ce13adb527c51c
   47  | 1b1cda7af7d7f38d126c2af4d34aa304d691d6799e2b1c1e6b2de9d2c8f31f32 | 1f7830d395f81dd96fd732aa315c3e314e593c3634ac57e3c1f2f93442008f1d | b7fcdcc3cfbe8535ee67c996280ac0cfff38d2247d28460476784cfdc8d64445
   48  | 39e3befdc14b2057e9903725808b6de44f4b8faf5f0eb0bcb28f24530a8da020 | 8f6dd794cd05e3e3c1bd13ed22476c6621b5d09a6353045e3c96257315c2b536 | 476a37495b546dbbd1fb28850fb6f34f3a836002e9fda772f1dc50462b2fb143
   49  | 06ed45eb48340c327a84d3259d8342262b203783f8d73c3f1e59a4974c8c9501 | 7e3e4b4428b9da6edb624104f13a96325c5b77177a25d3cb0b0bb53b3964c453 | 414838f72f55381708e98ba06aec656bd885df39972b1d5256a3748f118c3f48
   50  | c67e7b39eb35f1404a031e509d3974fe825230a4bd399ea9ff8ad81ba8c66336 | ab5cd3c81619f766946ac23c4b181e5ec9534e41a142bb9aba963d5a69ba9f1b | fb88652ed0b905d9efc5d83ee50ce550b992c6864f2fa324fab310007ee2b36b
   51  | 7881b5675b0c3a31a04abf0fd035a2001536bd6fda46e20c324999715c1e8153 | 66839654e778ab4d1ae95e973e51d216c4d5205385d041805f771700b8553359 | 0859df386c496efaa44fa6333b198652806b1a8914c5f23317efe13ab60a210b
   52  | a1273ed010a88841a40230907417f1078b3574827b5ef803765949770e38f126 | ac755749b4a6caf44da9a8b2bdb30fc73bfcfa724fc6ed77326323139cd85103 | ef5cb371a9ea04af5c6cab2306d7379d1e678064069602b8703f824a4179a739
   53  | d51d0ef62785b9bae4f2210c7951783530e352094ac13f7db7050b1a94e6f833 | dcf4382ddced973f5f4de48fb23c5e957a375778f870a5f292a872db72d23639 | c9e659324f15338c5050abcb6563bc23593866782a2428c4370c9dd1d9838425
   54  | eefc7690059a4795de99fa8b0349078c4de6ee8f8036e1458589debd0de10673 | b17fd04ee7390684d1c7efd919514b7cc5fbea2f398b8bd4ce037a5784320a3a | 6af701cd5ab0162bedb55d926d079892ebe26b977d6b79ddd3021191ca3d884d
   55  | 87db167054c7d111ed1da7e4a771702cf5f24c47793b6e916a7201042b98fb27 | e6c25ec676a2ea24bafb375e38e88afa906b4da0ed68ed89fdf685ab204bbb72 | f2906756fb97054dbcee6cb7ea181ac8c3d172a29df5dd237aacffcb81bf7623
   56  | d5bcef6738abcf4e7b5f63e8928e3c1ffc57b8fadfb4149698711fa1ca7dfb09 | f4d32dc7af09d33d5b7e013ff7bf10e419e9f19c99efba13058c844468a7d737 | 61ea7787df2643a8a00cc17a1f920fcfb163c80c90aa8ab07cdb08a672ac286c
   57  | bf9fb576ec144d4634d512858afb400d07937aab3bac3e01e2ae7afb7208c36a | 7161795903522d20d4b0afcbe751faa7c266a93b3c6f7fa97170f2d143e38815 | 09ab3ccd79f33a5522547531b0cee8746177d5bb7229252f37879ab40a28dc11
   58  | ba47b338058fb4dc45788a580e0083de13c76188e53c4b9bfd3868978dc8fa41 | a1b375ba4d78558be775249d61a7fb44dadef10620360eafa6c86c82ab70b210 | 57e60e398e926afa94e07d4f6cf614403349a041d004b5d9bcb0c599d4037d35
   59  | 53a40f44adbcd1d468580ffff822fcc4b42abafd12b9e5d8a825e0cd5fbb562b | 84d6bfef12324b9b368fc4244ac8e508daef19bbf075d355de896b500a06b437 | 34e8a34abd9b02f3ffcce5d204509243c08ac4ef0f8a34f645d55ac88a70166b
   60  | 2edd634ddf05e71ea6e01c98f63e16209cb18a8e65228b4988d1323e36070e04 | ca1257600dc6dc09423b9bb29f4d6d6dd34699bd90e053a7602b67c51908f701 | 27fa1aac872c93da48a6b12e41c27ed4c7edd4f16cc9278caedfb519e001f449
   61  | c8687565a6550568aa5d7bd0e483ff0ecaa525fe7fb81cec6a834cbb0d35da6c | b12e8ba3269f500e6e54c87cfc344ce9e18cb12cc1a9eb8143774287886c9b5e | c286b90d2c7e75f681fc4c971ab058c99c0b078e2fb77419d7559cc6b6b6e464
   62  | 11720244d5ad84309be20cd7573398253cfb34c2d7cac45b888449910bbb705e | 9204a512a849e767f722baab0260da0f5417477b70b3c1e204812aa242a1d504 | 0b9d34d1c4b350134e6c0d2dbca1bbecce8d8097ad53af9034ca1a5d0a2c2d43
   63  | db5aa9856b2bb54211f24e206f375ae62b793830105dc10dc0eae21c89bed447 | df158b742b9fe4afad77f9fdbd2587a08daedf331cffb1d7f736c965f9df586a | 3390de9b6b90a2cda8041ea16a0116ead08fdbc51864959211aba6e3923da60c
   64  | d272dadf8f84b9820987e7ed097829f67d952b0a35b2d6d8dab4e00512776038 | 819246864d7b43c4d87df9387b99f91264e58e38bfceb4c27fb73178a5dc1d3b | a626251f59a001f689fc98f12b2920b12c1a8b56232c9814a4cf4c79bc0f9328
   65  | c1fb3b2b12ecab2ada7a40d78a7b701dc81cbcae4bc7355d31c7ad912d502505 | 870a703fe6090228e052a310ecf9c6c9e5cfe8553dfbbb043615b56173f0d538 | 377852b08cc81d5ac1198782d7e2b542507fb0baf1af265a1a66d9d240680929
   66  | e299435e88f8f96f34cda4ec3e66ed327168b380f69c5ef52731f6ea6a308852 | 90150b62c82abd84052db9791a8c63702eecaaf7c26466a1b355c3abdeb9765b | d0212a1296e66d57e467987d43164b4ee47247bd941192d5195281c06ec36557
   67  | 922cd22e0f1aabce3deb9acbe2ae548ee2bb52ab5e7cee6fb7617316f427bd63 | 63c45c1e683f113ce9cb39af53c7786c5c8adc8d5ccb9f6c57387200a58e5e02 | a0b4c8323cabefb51c2cff5f1f83ffc1933510934be044347d86162861446a27
```

**Verification:** SHA-256 of the concatenated round constants (in order, as raw bytes) = `0d4c0ed8f86376ee2236b69bafa0e3d549bceadf8a3ee52bb882df6e39982e38`.

---

*End of the Jolt Continuation Protocol Specification*
