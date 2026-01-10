# Jolt Oracle Rust Implementation Roadmap

## Completed

### Phase 0: Conformance Corpus
- [x] `lake exe oracle export-metadata` command in Lean
- [x] `lake exe oracle generate-corpus` command in Lean
- [x] `permuteWithTrace` for Poseidon trace vectors (POS-006)
- [x] Wired commands into CLI/Main.lean

### Phase 1: Baseline Integration
- [x] Create `jolt-oracle-rs/` Cargo workspace
- [x] `build.rs` consumes `metadata.json` (BUILD-001)
- [x] Generate `error.rs` from metadata (BUILD-003)
- [x] Generate `params.rs` from metadata (BUILD-004)
- [x] Generate `modulus.rs` from metadata
- [x] Fr implementation with BLS12-381 Scalar
- [x] Poseidon permutation (68 rounds)
- [x] Poseidon sponge construction
- [x] LeanRunner subprocess backend
- [x] CLI scaffolding

---

## Remaining Work

### Phase 2: Native Rust Core
- [ ] FR-001..006: Full Fr conformance testing against Lean
- [ ] POS-001..005: Poseidon conformance with corpus vectors
- [ ] POS-006: Poseidon trace comparison for divergence localization
- [ ] DIG-001..003: State digest implementation
  - [ ] VMStateV1 type
  - [ ] computeStateDigest matching Lean field order
- [ ] Differential test harness (Rust vs Lean subprocess)

### Phase 3: JSON Subsystem
- [ ] JSON-001: UTF-8 validation
- [ ] JSON-002: Reject unpaired surrogates
- [ ] JSON-003: Reject duplicate keys after unescaping
- [ ] JSON-004A: Number validation (finite IEEE-754)
- [ ] JSON-004B: Integer bounds (±2^53-1)
- [ ] JSON-005: Unescape before duplicate check
- [ ] JSON-006: Reject NaN/Infinity literals
- [ ] JCS-001..002: UTF-16 key comparator
- [ ] JCS-003: ECMAScript number serialization
- [ ] JCS-004..005: Canonicalization conformance

### Phase 4: CLI & Release
- [ ] CLI `digest` command
- [ ] CLI `verify` command
- [ ] CLI `generate` command
- [ ] Linux-musl static build
- [ ] Cross-platform CI (Linux x86_64, macOS aarch64)
- [ ] ErrorCode coverage check in CI

---

## CI Pipeline (Target)

| Job | Purpose |
|-----|---------|
| A | Rust hygiene (fmt, clippy, no HashMap/panic in consensus paths) |
| B | Metadata/codegen drift detection |
| C | Conformance (full corpus) |
| D | Cross-platform replay |
| E | Supply chain (cargo audit) |
| F | ErrorCode coverage |

---

## Milestones

### Milestone A: Conformance Established
- [ ] All CONF-* requirements satisfied
- [ ] Lean passes its own corpus
- [ ] Rust harness can invoke LeanRunner and compare

### Milestone B: Core Replacement
- [ ] All FR-*, POS-*, DIG-* requirements satisfied
- [ ] Differential tests pass with RustRunner only
- [ ] Poseidon trace comparisons enabled

### Milestone C: Standalone Binary
- [ ] All JSON-*, JCS-*, ERR-* requirements satisfied
- [ ] CLI fully functional
- [ ] Static Linux binary, no Lean runtime
- [ ] Cross-platform conformance clean
