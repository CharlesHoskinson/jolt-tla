# Jolt Oracle (Rust)

Rust implementation of the Jolt Oracle specification, providing a verified drop-in replacement for the Lean 4 oracle with byte-identical output for all conformance test vectors.

## Architecture

```
Track 0: Conformance Baseline          Track 1: Native Rust Replacement
─────────────────────────────          ────────────────────────────────
jolt_oracle/ (Lean 4)                  jolt-oracle-rs/
    ↓                                      ↓
lake exe oracle (canonical)            cargo build --release
    ↓                                      ↓
conformance corpus (golden vectors)    differential testing
    ↓                                      ↓
test harness ─────────────────────────────→ compare
```

## Building

```bash
# Build
cargo build --release

# Run tests
cargo test

# Run CLI
cargo run -- --help
cargo run -- version
cargo run -- export-metadata
```

## Project Structure

```
jolt-oracle-rs/
├── Cargo.toml
├── build.rs              # Consumes metadata.json, generates code
├── src/
│   ├── lib.rs
│   ├── error.rs          # ErrorCode enum (uses generated code)
│   ├── field/
│   │   ├── mod.rs
│   │   └── fr.rs         # BLS12-381 scalar field (Fr)
│   ├── poseidon/
│   │   ├── mod.rs
│   │   ├── permute.rs    # 68-round Poseidon permutation
│   │   └── sponge.rs     # Sponge construction
│   ├── json/
│   │   └── mod.rs        # I-JSON / JCS (Phase 3)
│   ├── state/
│   │   └── mod.rs        # VM state & digest (Phase 2)
│   ├── runner.rs         # LeanRunner subprocess backend
│   └── main.rs           # CLI
└── TODO.md               # Implementation roadmap
```

## Codegen from Lean

The `build.rs` script reads `../jolt_oracle/metadata.json` (exported by `lake exe oracle export-metadata`) and generates:

- `error_generated.rs` - All ErrorCode variants with correct discriminants
- `modulus_generated.rs` - BLS12-381 scalar field modulus
- `params_generated.rs` - Poseidon MDS matrix and round constants

This ensures the Rust implementation stays in sync with the Lean specification.

## QA Invariants

| ID | Invariant |
|----|-----------|
| QG-1 | **Conformance**: Rust matches Lean on `Ok(payload)` byte-for-byte, or `Err(ErrorCode)` with same discriminant |
| QG-2 | **Determinism**: Identical outputs on Linux x86_64 and macOS aarch64 |
| QG-3 | **Fail-closed**: Invalid inputs return specific ErrorCode; no panics |

## Dependencies

- `bls12_381` - BLS12-381 scalar field arithmetic
- `ff` - Finite field traits
- `thiserror` - Error handling
- `clap` - CLI framework
- `serde`/`serde_json` - JSON serialization
- `hex` - Hex encoding

## License

MIT OR Apache-2.0
