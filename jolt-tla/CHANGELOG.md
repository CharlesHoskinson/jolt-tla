# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [0.3.0] - 2026-01-08

### Added
- `JOLT_POSEIDON_FR_V1` complete parameter specification (spec.md §3.4.1)
  - State width t=3, rate r=2, capacity c=1
  - 8 full rounds, 60 partial rounds
  - S-box x⁵ on BLS12-381/Fr
  - MDS matrix and 204 round constants pinned
- `JOLT_WRAPPER_PROOF_SYSTEM_V1` for Midnight compatibility (spec.md §5.2)
  - BLS12-381 curve, KZG PCS with k=14
  - Wire format: `proof[v5]`, `verifier-key[v6]`
  - 11 public inputs in specified order
  - Nonce replay protection
- `WrapperValidationTests.tla` with 15 fail-closed validation tests
- `INV_TYPE_PoseidonParams` invariant (30th invariant)
- Oracle CLI executable specification in Lean 4
  - `oracle status` - Health check
  - `oracle digest` - Compute state digest from JSON
  - `oracle verify chain` - Verify continuation chain
  - `oracle generate vectors` - Generate test vectors
  - `oracle repl` - Interactive REPL mode
- Full Lean 4 implementation of Jolt core modules
  - Jolt/Encoding/ - Bytes32, Fr2 conversions
  - Jolt/Field/ - Fr arithmetic
  - Jolt/JSON/ - JCS canonicalization, Parser
  - Jolt/Poseidon/ - Hash implementation
  - Jolt/Registry/ - Config validation
  - Jolt/State/ - VMState, Digest
  - Jolt/Transcript/ - Fiat-Shamir sponge
  - Jolt/Wrapper/ - Public inputs

### Changed
- TBD registry keys: 15 → 14
- Invariant count: 29 → 30
- Lean kernel line count: ~4K → ~8K lines (with Oracle CLI)
- lakefile.toml → lakefile.lean (for git dependencies)

## [0.2.0] - 2026-01-01

### Added
- Initial TLA+ specification for Jolt continuations
- 29 verified invariants covering type safety, cryptographic binding, protocol correctness, and attack prevention
- Lean 4 NearFall verification kernel
- Full prose specification (spec.md, ~40K words)

[0.3.0]: https://github.com/CharlesHoskinson/jolt-tla/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/CharlesHoskinson/jolt-tla/releases/tag/v0.2.0
