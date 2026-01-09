# Jolt Executable Spec Oracle — TODO

**Status:** Core implementation complete
**Last Updated:** 2026-01-09

---

## Summary

| Category | Status |
|----------|--------|
| Core Types & Encoding | ✅ Complete |
| JSON Parser (ASCII-only) | ✅ Complete (46 tests) |
| Poseidon Hash | ✅ Complete |
| SHA-256 Hash | ✅ Complete |
| Transcript System | ✅ Complete |
| Registry Validation | ✅ Complete |
| Registry Hash | ✅ Complete |
| State & Digest | ✅ Complete |
| Bundle/Tar | ✅ Complete |
| Oracle API | ✅ Complete |
| CLI Commands | ✅ Complete |
| REPL | ✅ Complete |
| Test Vectors | ✅ Complete |

---

## P0 — Critical Path ✅

### 1. CLI Commands ✅
- [x] `digest` command - compute StateDigestV1 from JSON
- [x] `verify chain` command - verify continuation chains
- [x] `verify vectors` command - run conformance test vectors
- [x] `status` command - show oracle health dashboard
- [x] `diff` command - compare state files
- [x] `explain` command - error code documentation
- [x] `watch` command - live refresh dashboard
- [x] `generate` command - generate test vectors

### 2. REPL ✅
- [x] Interactive command-line interface
- [x] Script sourcing (`:source file.oracle`)
- [x] Batch mode (`--batch file.oracle`)
- [x] Variable system (`$var`, `$_`, `$?`)
- [x] Aliases and command history
- [x] Config persistence
- [x] Terminal capability detection

### 3. Poseidon Constants Verification ✅
- [x] Confirm JOLT_POSEIDON_FR_V1 constants match reference implementation
- [x] Run `validateConstants` and ensure it returns `true`
- [x] MDS matrix and round constants validated

---

## P1 — Should Complete ✅

### 4. Golden Test Vectors ✅
- [x] Generate StateDigestV1 vectors:
  - Minimal state (all zeros)
  - Typical state (realistic values)
  - Halted state with exit code
  - State with config tags
- [x] Generate chain verification vectors:
  - Invalid chain (broken linkage) - E500_ChainBreak
  - Invalid chunk (skipped index) - E502_InvalidChunkIndex
- [x] Export as JSON for cross-implementation testing
- [x] Document expected outputs in `test_vectors/golden_v1.json`

### 5. Registry Integration ✅
- [x] Parse registry bundle (canonical tar)
- [x] Validate all entries against schema (17 required keys)
- [x] Compute registry hash (SHA-256 of JCS canonical bytes)
- [x] Reject external handles in registry.json

---

## P2 — Nice to Have

### 6. Tag Validation Decision
- [ ] Resolve interpretation of §8.6:
  - Strict: Tags must match `^[A-Z][A-Z0-9_]*(/V[0-9]+)?$`
  - Current: `/V` suffix not enforced for transcript tags
- [ ] Document decision in `Transcript/TagValidation.lean`

### 7. TLA+ Cross-Validation
- [ ] Generate execution traces from TLA+ model
- [ ] Feed to Lean oracle
- [ ] Compare outputs
- [ ] Document any discrepancies

### 8. Performance
- [ ] Profile Poseidon permutation
- [ ] Benchmark full StateDigestV1 computation
- [ ] Consider `@[extern]` for hot paths if needed

### 9. Documentation
- [ ] CLI usage examples in README
- [ ] Error code reference table
- [ ] Architecture diagram
- [ ] Decision log for spec interpretations

### 10. NEEDS_EVIDENCE Items
- [ ] `Wrapper/ProofSystem.lean:115` - hashSHA256 (wrapper VK hash)
- [ ] `Wrapper/ProofSystem.lean:118` - personalization bytes

---

## Completed ✅

### Core Types & Encoding
- [x] Fr (BLS12-381 scalar field arithmetic)
- [x] Bytes32 (32-byte fixed arrays)
- [x] Fr2 encoding (31+1 byte split per §2.2.1)
- [x] ASCII utilities (explicit ranges, not Unicode-aware)
- [x] ByteOrder (little-endian conversions)

### JSON Parser
- [x] Lexer with raw number preservation
- [x] Recursive descent parser
- [x] Duplicate key detection
- [x] Number validation (no exponents, no fractions)
- [x] Integer range check (±2^53-1)
- [x] **ASCII-only profile** (rejects codepoints > 127)
- [x] Resource limits (depth, size, string length, etc.)
- [x] JCS canonicalization (RFC 8785)
- [x] UTF-16 code unit sorting for object keys

### Cryptographic Hash Functions
- [x] Poseidon (width=3, RF=8, RP=60, α=5)
- [x] MDS matrix (3×3 Cauchy over BLS12-381)
- [x] 204 round constants from JOLT_POSEIDON_FR_V1
- [x] Poseidon sponge (absorb/squeeze with domain separation)
- [x] SHA-256 (FIPS 180-4 compliant)

### Transcript System
- [x] Domain separation ("JOLT/TRANSCRIPT/V1")
- [x] Type tags (BYTES=1, U64=2, TAG=3, VEC=4)
- [x] Tag validation per §8.6 ([A-Z0-9/_])
- [x] absorb_bytes, absorb_u64, absorb_tag, absorb_vec

### Registry
- [x] Key validation (^JOLT_[A-Z0-9_]+_V[0-9]+$)
- [x] ConfigTags projection (17 required keys)
- [x] Schema validation framework
- [x] Registry hash computation (SHA-256 of JCS)
- [x] External handle rejection

### State & Digest
- [x] VMStateV1 structure (pc, regs, step_counter, etc.)
- [x] StateDigestV1 computation (14-step algorithm per §11.10.2)
- [x] Correct absorption order (pc → regs[0..31] → step_counter)
- [x] config_tags from prover claim (not recomputed)

### Bundle
- [x] Canonical tar creation per §14.3
- [x] Canonical tar parsing
- [x] Path validation (no absolute, no .., no special chars)
- [x] Bytewise lexicographic member ordering
- [x] Zero mtime enforcement
- [x] Registry.json extraction

### Infrastructure
- [x] Error taxonomy (E100-E708)
- [x] CLI with all commands
- [x] REPL with full feature set
- [x] Test harness (149 tests passing)
- [x] Build system (lake, 40+ modules)
- [x] Nix flake for reproducible builds

---

## QA Gates

```
[✅] lake build              → 0 errors
[✅] lake exe test           → 149/149 pass
[✅] grep -r "sorry" Jolt/   → 0 matches
[✅] grep -r "noncomputable" → 0 matches
[✅] Poseidon validateConstants == true
[✅] CLI digest <test.json>  → working
[✅] CLI verify <chain.json> → working
[✅] TLA+ model check        → no errors (nix run .#tla-check)
```

---

## Build Info

- **Lean Version:** 4.26.0 (via elan)
- **Modules:** 40+
- **Tests:** 149
- **TLA+ Specs:** 12 modules

---

## Reference

- Spec: `jolt-tla/spec.md`
- TLA+: `jolt-tla/tla/`
- Test Vectors: `jolt_oracle/test_vectors/golden_v1.json`
