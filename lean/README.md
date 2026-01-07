# Jolt Lean 4 Kernel

Formal verification kernel for Jolt zkVM trace-based conformance checking.

## Overview

This kernel provides machine-checked proofs that zkVM execution traces satisfy the 29 security invariants specified in the TLA+ model. It bridges the gap between the TLA+ specification and a production implementation.

## Quick Start

```bash
# Install Lean 4 (via elan)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build the kernel
lake build

# Run tests
lake build Tests
```

## Project Structure

```
lean/
├── NearFall/
│   ├── TLATypes.lean      # Primitive types (Fr, Bytes32, U64)
│   ├── Types.lean         # Core definitions
│   ├── Encoding.lean      # Field element encoding
│   ├── Transcript.lean    # Poseidon transcript
│   ├── SMT.lean           # Sparse Merkle Tree
│   ├── VMState.lean       # RISC-V VM state
│   ├── Continuations.lean # Chunk execution & StateDigest
│   ├── Invariants.lean    # 29 TLA+ invariants
│   ├── Checker.lean       # Runtime validation
│   ├── Soundness.lean     # Security proofs
│   └── Basic.lean         # Package exports
├── Tests/                 # Test suite
├── lakefile.toml          # Build configuration
└── lean-toolchain         # Lean 4.26.0
```

## Invariant Coverage

| Category | Count | Description |
|----------|-------|-------------|
| TYPE     | 4     | Type well-formedness |
| BIND     | 10    | Cryptographic binding |
| SAFE     | 7     | Protocol correctness |
| ATK      | 8     | Attack prevention |
| **Total**| **29**| Full TLA+ alignment |

## Axiom Budget

10 cryptographic axioms (all justified by standard assumptions):

| Axiom | Justification |
|-------|---------------|
| Poseidon collision resistance | Hash function security |
| Poseidon determinism | Function property |
| Domain separation | Transcript construction |
| SMT binding | Merkle tree security |
| SMT collision resistance | Hash function security |
| StateDigest determinism | Function property |
| StateDigest collision resistance | Hash function security |
| Chunk bound | Modeling assumption |
| Public input assembly | Circuit construction |
| Status Fr injectivity | Field encoding |

## Security Properties

The soundness theorem proves:

- **No splice attacks**: Chunk digests form unbreakable chain
- **No skip attacks**: All chunks must be consecutive
- **No replay attacks**: Nonce binding prevents reuse
- **No config attacks**: Configuration included in digest
- **No memory forgery**: SMT roots verified at boundaries
- **No prefix attacks**: Only complete executions accepted

## Relationship to TLA+

This kernel implements the invariants from `tla/Invariants.tla`:

| TLA+ Module | Lean Module |
|-------------|-------------|
| Types.tla | TLATypes.lean |
| VMState.tla | VMState.lean |
| Continuations.tla | Continuations.lean |
| Invariants.tla | Invariants.lean |
| SMT.tla | SMT.lean |

## Requirements

- Lean 4 v4.26.0+
- Lake build system

## License

Apache 2.0
