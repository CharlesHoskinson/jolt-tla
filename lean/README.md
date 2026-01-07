# Jolt Lean 4 Verification Kernel

Formal verification kernel for Jolt zkVM continuation semantics.

## Overview

A TLA+ model checker explores states. It runs the spec, trying configurations, hunting for one that breaks an invariant. If it checks a million states and finds no violation, you gain confidence—but not certainty. The state space might have a trillion configurations. The bug hides in state one trillion and one.

Lean works differently. Instead of searching for counterexamples, it constructs proofs. You write a theorem: "Every valid execution preserves the binding invariants." Lean's type checker verifies the proof term you provide. If the proof compiles, the theorem holds—not probabilistically, not up to bounded model size, but mathematically. The guarantee is the same one that makes 2+2=4 true: logical deduction from axioms.

This matters for security-critical systems. The Jolt zkVM processes proofs that move assets. An attacker who finds a gap in the continuation protocol—a way to splice chunks, skip steps, or forge memory—can drain funds. TLA+ model checking gives high confidence the protocol is sound. The Lean kernel converts that confidence into proof.

TLA+ excels at exploration: "Does my protocol make sense? Are there deadlocks? Can I reach this weird state?" Model checking answers these mechanically. But once the design stabilizes, you want guarantees that scale beyond what any computer can enumerate. Use TLA+ to design and debug, use Lean to lock down security properties.

## Verified Invariants

The kernel implements the same 29 invariants specified in `tla/Invariants.tla`:

**Type invariants** ensure values stay within their mathematical domains. A field element must be less than the field modulus. A register index must be 0-31. A step counter must be non-negative. Type confusion bugs are how real exploits happen. The kernel proves type safety structurally—ill-typed states cannot be constructed.

**Binding invariants** enforce cryptographic commitments. The StateDigest binds every observable property of VM state: program hash, registers, memory roots, step counter, halt status, configuration. If any component differs, the digest differs. The kernel proves this via axioms about Poseidon hashing and explicit encoding functions that convert state components to field elements.

**Safety invariants** capture protocol correctness. Chunks must execute the right number of steps. The final chunk must be halted. Register x0 must always read zero (RISC-V requirement). The kernel proves these by showing the transition function preserves them and the initial state satisfies them.

**Attack prevention invariants** name specific attacks—prefix, skip, splice, replay, config swap, memory forgery—and prove each cannot succeed against a verifier following the protocol. The proofs show the attack requires producing a StateDigest that matches the expected chain, which requires forging a hash preimage or violating SMT binding. Under standard cryptographic assumptions, this is computationally infeasible.

The soundness theorem ties everything together. If a batch of chunks passes verification (consecutive indices, matching digests at boundaries, valid final state), then the execution it claims to represent actually happened.

## Axioms

No formal system proves everything from nothing. The kernel accepts 10 cryptographic assumptions without proof inside Lean. These match standard cryptographic literature: Poseidon collision resistance, Merkle tree binding, deterministic hashing.

| Axiom | Assumption | Basis |
|-------|------------|-------|
| `poseidon_collision_resistant` | Different inputs → different hashes | Poseidon security proof |
| `poseidon_deterministic` | Same input → same hash | Function property |
| `transcript_domain_separation` | Different types → different sponge states | Sponge construction |
| `smt_root_binding` | Same root → same memory contents | Merkle tree binding |
| `smt_collision_resistant` | Different contents → different roots | Hash function security |
| `stateDigest_deterministic` | Same VM state → same digest | Function property |
| `stateDigest_collision_resistant` | Different states → different digests | Poseidon + encoding |
| `chunk_index_bound` | Chunk indices bounded | Modeling assumption |
| `public_input_assembly` | Circuit assembles public inputs correctly | Implementation |
| `status_fr_injective` | Running/halted → distinct field elements | Encoding spec |

The kernel has no `sorry` placeholders. Every theorem is fully proven down to these axioms.

## Attack Prevention

The attack prevention theorems are the kernel's main deliverable:

- **`no_prefix_attack`** — Incomplete execution (halted=false in final chunk) cannot produce a valid batch
- **`no_skip_attack`** — Missing chunks break the digest chain
- **`no_splice_attack`** — Chunks from different executions have different program hashes; mixing them produces mismatched digests
- **`no_replay_attack`** — Batch nonce included in wrapper proof; resubmitting old proofs fails
- **`no_config_attack`** — Configuration tags hashed into StateDigest
- **`no_memory_forgery`** — SMT roots included in StateDigest; false memory claims require hash collision

## Structure

```
lean/
├── NearFall/
│   ├── TLATypes.lean      # Fr, Bytes32, U64 — matching Types.tla
│   ├── Types.lean         # SystemState, phases
│   ├── Encoding.lean      # Field encoding — matching Encodings.tla
│   ├── Transcript.lean    # Poseidon sponge — matching Transcript.tla
│   ├── SMT.lean           # Sparse Merkle Tree — matching SMT.tla
│   ├── VMState.lean       # RISC-V state — matching VMState.tla
│   ├── Continuations.lean # Chunk records, StateDigest
│   ├── Invariants.lean    # 29 TLA+ invariants
│   ├── Checker.lean       # Runtime validation
│   ├── Soundness.lean     # Security proofs
│   └── Basic.lean         # Package exports
├── Tests/
├── lakefile.toml
└── lean-toolchain         # Lean 4.16.0
```

## Build

```bash
# Install Lean 4 via elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build
cd jolt-tla/lean
lake build

# Tests
lake build Tests
```

## Invariant Summary

| Category | Count | Description |
|----------|-------|-------------|
| TYPE | 4 | Type well-formedness |
| BIND | 10 | Cryptographic binding |
| SAFE | 7 | Protocol correctness |
| ATK | 8 | Attack prevention |
| **Total** | **29** | |

## Future Work

**Proof improvements**
- Reduce axiom count by deriving composite assumptions from primitives
- Add computational reflection via `native_decide`
- Universe polymorphism audit

**Coverage expansion**
- Instruction-level verification for RISC-V opcodes
- Memory operation proofs for load/store
- Transcript absorption invariants

**Tooling**
- Proof extraction for independent verification
- Test vector generation for cross-implementation testing
- CI integration

## License

Apache 2.0
