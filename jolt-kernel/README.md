# Jolt Kernel

Minimal auditable Lean 4 kernel for Jolt zkVM verification.

## Overview

Jolt Kernel is the **production audit target** for Jolt zkVM's continuation proving system. It provides machine-checked proofs for public input binding and continuation chaining with a minimal Trusted Computing Base (TCB).

**Key properties:**
- **2 cryptographic axioms** (PoseidonPermute, stateDigest collision resistance)
- **0 sorry statements**
- **Single audit file** (`Jolt/Kernel.lean`)

## Relationship to jolt-tla

| Repository | Purpose | Axioms | Audience |
|------------|---------|--------|----------|
| **jolt-kernel** | Production verification kernel | 2 | Security auditors |
| [jolt-tla](https://github.com/CharlesHoskinson/jolt-tla) | TLA+ spec + Lean invariant proofs | 10 | Protocol designers |

`jolt-kernel` is the minimal core extracted from `jolt-tla/lean`. Use `jolt-tla` for understanding the full protocol; use `jolt-kernel` for security audits.

## Quick Start

```bash
# Install Lean 4 (via elan)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build
cd jolt-kernel
lake build

# Verify axiom count
grep -c "^axiom" Jolt/*.lean  # Should be 2
```

## Trusted Computing Base

The kernel has exactly **2 cryptographic axioms**:

| # | Axiom | Module | Justification |
|---|-------|--------|---------------|
| 1 | `PoseidonPermute` | Transcript.lean | Poseidon permutation (cryptographic primitive) |
| 2 | `stateDigest_collision_resistant` | StateDigest.lean | Collision resistance (from Poseidon security) |

Both axioms are **cryptographic security assumptions** that cannot be proven mathematically. They represent the trust boundary of the system.

## Security Properties

The kernel guarantees that if all checkers pass:

1. **No chunk skipping** - Consecutive indices enforced
2. **No chunk splicing** - Digest chain prevents mixing executions
3. **No cross-config attacks** - Config tags in digest
4. **No memory forgery** - SMT binding in digest
5. **No replay attacks** - Batch nonce binding

## Structure

```
jolt-kernel/
├── Jolt/
│   ├── Types.lean         # Fr, Bytes32, U64, Vec
│   ├── Encoding.lean      # Bytes32 <-> Fr2 encoding
│   ├── Transcript.lean    # Poseidon sponge (1 axiom)
│   ├── ConfigTags.lean    # RFC 8785 JCS config tags
│   ├── StateDigest.lean   # 14-step digest algorithm (1 axiom)
│   ├── Wrapper.lean       # PublicInputsV1 binding
│   ├── Continuations.lean # Chunk chaining validation
│   ├── Logic.lean         # Helper logic
│   └── Kernel.lean        # AUDIT TARGET: consolidated exports
├── Tests/
├── reports/               # QA reports
├── lakefile.toml
└── lean-toolchain         # Lean 4.26.0
```

## Audit Instructions

1. **Read only `Jolt/Kernel.lean`** - All exports and theorems
2. **Verify axiom count**: `#print axioms Jolt.Kernel.wrapper_sound`
3. **Check for sorry**: `grep -r "sorry" Jolt/` (should find only comments)
4. **Review TCB**: Only `PoseidonPermute` should appear in axiom traces

## Kernel Theorems

| Theorem | Proves |
|---------|--------|
| `encoding_roundtrip_sound` | Bytes32 <-> Fr2 roundtrip |
| `encoding_injective` | Different inputs -> different encodings |
| `configTags_sound` | Tags sorted and unique |
| `wrapper_sound` | Public inputs correctly bound |
| `continuations_sound` | Chunk chain valid |
| `stateDigest_deterministic` | Digest is a function |

## Requirements

- Lean 4 v4.26.0+
- Lake build system

## License

Apache 2.0
