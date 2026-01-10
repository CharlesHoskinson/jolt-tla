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
- [x] FR-001..006: Full Fr conformance testing against Lean
  - [x] FR-001: Canonical encoding (zero, one, max valid)
  - [x] FR-002: Canonical validation on input from bytes
  - [x] FR-003: E300_NonCanonicalFr for non-canonical values
  - [x] FR-004: Canonical LE 32-byte output
  - [x] FR-005: Arithmetic (add, sub, mul, neg, pow5, square)
  - [x] Golden vector tests matching Lean output
  - [x] 43 conformance tests passing
- [x] POS-001..006: Poseidon conformance with corpus vectors
  - [x] POS-001: Parameters (t=3, r=2, RF=8, RP=60)
  - [x] POS-002: 68 rounds structure (4 full + 60 partial + 4 full)
  - [x] POS-003: Round constants from metadata.json (204 constants)
  - [x] POS-004: Sponge absorb in rate-sized chunks
  - [x] POS-005: Bit-identical output (determinism, collision resistance)
  - [x] POS-006: Trace mode for divergence localization
  - [x] 43 conformance tests passing
- [x] DIG-001..003: State digest implementation
  - [x] VMStateV1 type (with validation)
  - [x] Bytes32, ConfigTag types
  - [x] Transcript with type-tagged absorb methods
  - [x] computeStateDigest matching Lean field order
  - [x] All 4 golden vector tests passing
- [x] Differential test harness (Rust vs Lean subprocess)
  - [x] OracleRunner trait with RustDigestRunner
  - [x] LeanDigestRunner subprocess wrapper
  - [x] DiffTestHarness comparison logic
  - [x] ReproBundle for mismatch debugging
  - [x] BatchResult for running multiple tests
  - [x] Integration tests with golden vectors (44 tests passing)

### Phase 3: JSON Subsystem
- [x] JSON-001: UTF-8 validation
- [x] JSON-002: Reject unpaired surrogates
- [x] JSON-003: Reject duplicate keys after unescaping
- [x] JSON-004A: Number validation (finite IEEE-754)
- [x] JSON-004B: Integer bounds (±2^53-1)
- [x] JSON-005: Unescape before duplicate check
- [x] JSON-006: Reject NaN/Infinity literals
- [x] JCS-001..002: UTF-16 key comparator
- [x] JCS-003: ECMAScript number serialization
- [x] JCS-004..005: Canonicalization conformance
- [x] DoS protection limits (E110-E115)
- [x] 56 JSON conformance tests passing

### Phase 4: CLI & Release
- [x] CLI `digest` command
  - [x] JSON input from file or stdin
  - [x] Computes state digest from program_hash and VMStateV1
  - [x] JSON output with ok/err result
  - [x] 7 CLI integration tests passing
- [x] CLI `verify` command
  - [x] JSON input with program_hash, state, and expected_digest
  - [x] Computes digest and compares with expected
  - [x] JSON output with valid/invalid status
  - [x] Returns exit code 0 for match, 1 for mismatch
  - [x] 7 verify CLI integration tests passing
- [x] CLI `generate` command
  - [x] Generate test vectors from input files
  - [x] Supports state_digest vector type
  - [x] JSON output with vectors array (name, type, input, expected)
  - [x] Optional -o flag for output file
  - [x] 7 generate CLI integration tests passing
- [x] Linux-musl static build
  - [x] `.cargo/config.toml` with musl linker configuration
  - [x] `Makefile` with `release-musl` target
  - [x] `scripts/setup-cross.sh` for target installation
- [x] Cross-platform CI (Linux x86_64, macOS aarch64)
  - [x] GitHub Actions workflow `.github/workflows/rust.yml`
  - [x] Jobs: hygiene, test, build-linux-musl, build-macos-arm64, build-windows, audit
  - [x] Artifact upload for all platform binaries
- [x] ErrorCode coverage check in CI
  - [x] `scripts/check-error-coverage.sh` script
  - [x] CI job in rust.yml workflow
  - [x] Makefile target `error-coverage`
  - [x] Distinguishes required (E1xx) from deferred (E2xx-E7xx) codes
- [x] Metadata drift detection in CI
  - [x] `scripts/check-metadata-drift.sh` script
  - [x] CI job in rust.yml workflow
  - [x] Makefile target `metadata-drift`
  - [x] Validates metadata.json structure and Poseidon parameters
  - [x] Verifies BLS12-381 modulus, error code count, round constants
- [x] Corpus conformance testing in CI
  - [x] `src/conformance/corpus.rs` - Corpus runner implementation
  - [x] `tests/corpus_conformance.rs` - Integration tests
  - [x] CI job in rust.yml workflow
  - [x] Runs all vectors from corpus.json against Rust implementation
- [x] Cross-platform replay testing in CI
  - [x] `tests/fixtures/replay/` - Test input fixtures
  - [x] `scripts/run-replay-tests.sh` - Runs oracle on fixtures
  - [x] `scripts/compare-replay-outputs.sh` - Compares outputs
  - [x] CI job in rust.yml workflow
  - [x] Verifies Linux, macOS, Windows produce identical digests

---

## CI Pipeline (Implemented)

| Job | Purpose | Status |
|-----|---------|--------|
| A | Rust hygiene (fmt, clippy) | Done |
| B | Run tests | Done |
| C | Build Linux musl static | Done |
| D | Build macOS ARM64 | Done |
| E | Build Windows x86_64 | Done |
| F | Supply chain (cargo audit) | Done |
| G | ErrorCode coverage | Done |
| H | Metadata drift detection | Done |
| I | Corpus conformance | Done |
| J | Cross-platform replay | Done |

### Future CI Enhancements
- [ ] Conformance (full corpus against Lean oracle subprocess)

---

## Milestones

### Milestone A: Conformance Established
- [ ] All CONF-* requirements satisfied
- [ ] Lean passes its own corpus
- [ ] Rust harness can invoke LeanRunner and compare

### Milestone B: Core Replacement
- [x] All FR-*, POS-*, DIG-* requirements satisfied
  - [x] FR-001..006: Fr field conformance (43 tests)
  - [x] POS-001..006: Poseidon conformance (43 tests)
  - [x] DIG-001..003: State digest (4 golden vectors)
- [x] Differential tests pass with RustRunner only
- [x] Poseidon trace comparisons enabled (permute_with_trace)

### Milestone C: Standalone Binary
- [x] All JSON-*, JCS-* requirements satisfied
  - [x] JSON-001..006: I-JSON parsing validation (56 tests)
  - [x] JCS-001..005: Canonicalization conformance
- [x] CLI fully functional
  - [x] `digest` command (7 tests)
  - [x] `verify` command (7 tests)
  - [x] `generate` command (7 tests)
- [x] Static Linux binary, no Lean runtime
  - [x] musl target configured
  - [x] CI builds static binary
- [x] Cross-platform CI configured
  - [x] Linux x86_64 (musl static)
  - [x] macOS ARM64
  - [x] Windows x86_64
