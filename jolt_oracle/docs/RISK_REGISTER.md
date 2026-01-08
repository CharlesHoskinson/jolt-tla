# Jolt Oracle Risk Register

## Overview

This document tracks cryptographic assumptions, trust boundaries, known limitations, and spec interpretation decisions for the Jolt Executable Spec Oracle.

## 1. Cryptographic Assumptions

### A1: Poseidon Hash Security

**Assumption:** The Poseidon hash function with JOLT_POSEIDON_FR_V1 parameters provides 128-bit security against collision and preimage attacks.

**Parameters:**
- Field: BLS12-381 scalar field (255-bit prime)
- Width: t = 3
- Full rounds: RF = 8
- Partial rounds: RP = 60
- S-box: x^5

**Justification:** Parameters follow recommendations from the Poseidon paper for 128-bit security on prime fields.

**Reference:** https://eprint.iacr.org/2019/458.pdf

---

### A2: BLS12-381 Discrete Log Hardness

**Assumption:** The discrete logarithm problem on the BLS12-381 scalar field is computationally infeasible.

**Justification:** BLS12-381 is a widely deployed pairing-friendly curve with 128-bit security level, used in Ethereum 2.0, Zcash, and other production systems.

---

### A3: Fiat-Shamir Transform Security

**Assumption:** The Fiat-Shamir transform using Poseidon-based transcripts produces pseudorandom challenges indistinguishable from uniform random field elements.

**Justification:** Standard cryptographic assumption for Fiat-Shamir in the random oracle model, instantiated with collision-resistant hash.

---

## 2. Trust Boundaries

### T1: Lean 4 Runtime

**Trusted Component:** Lean 4 runtime and compiler (v4.26.0)

**Scope:** Correct execution of Lean programs, memory safety, arithmetic operations

**Mitigation:** Use stable Lean releases, avoid experimental features

---

### T2: No External Dependencies

**Trusted Components:** None (beyond Lean runtime)

**Scope:** The oracle has no FFI calls, no network dependencies, no database connections

**Verification:** `grep -r "@[extern]" Jolt/` returns empty

---

### T3: Input Boundaries

**Trust Boundary:** All external inputs are validated before processing

**Components:**
- JSON parser rejects malformed input
- Registry validator enforces key format
- Tar validator rejects absolute paths
- Fr encoding rejects non-canonical values

---

## 3. Known Limitations

### L1: No Proof Verification

**Limitation:** The oracle does not verify zkSNARK proofs (FR-12)

**Impact:** Cannot perform end-to-end proof verification

**Status:** Deferred to future implementation with FFI

---

### L2: No VM Simulation

**Limitation:** The oracle does not execute RISC-V instructions (FR-08)

**Impact:** Cannot independently verify execution traces

**Status:** Major feature requiring ~2000+ LOC; deferred

---

### L3: Single-Threaded Execution

**Limitation:** All computations run single-threaded

**Impact:** Performance may be slower than optimized implementations

**Mitigation:** Oracle is reference implementation, not production prover

---

### L4: Memory-Bound Large Inputs

**Limitation:** Large inputs (multi-GB) may cause memory exhaustion

**Mitigation:** Input size limits enforced in JSON parser:
- Max nesting depth
- Max array size
- Max string length

---

## 4. Spec Interpretation Decisions

### D1: Exit Code Range

**Spec Reference:** Section 11.5, 11.10.2

**Interpretation:** Exit code is validated as 0..255 when halted=1, any value when halted=0

**Implementation:** `VMStateV1.validateTermination` in `State/VMState.lean`

---

### D2: Config Tags Ordering

**Spec Reference:** Section 3.8

**Interpretation:** Config tags are absorbed in array order as provided by prover, not re-sorted

**Rationale:** Digest must commit to prover's claimed ordering; validation against registry projection is separate

---

### D3: Tag Format Validation

**Spec Reference:** Section 8.6

**Interpretation:** Tags must match `[A-Z0-9/_]+` (ASCII uppercase, digits, underscore, slash)

**Note:** The `/V` suffix is NOT enforced within tags (decision documented in TODO.md P2-6)

---

### D4: Fr2 Bounds

**Spec Reference:** Section 2.2.1

**Interpretation:** Fr2 encoding rejects:
- lo >= 2^248 (would overflow 31 bytes)
- hi >= 256 (would overflow 1 byte)

**Implementation:** Strict rejection with specific error codes E301, E302

---

### D5: Canonical Fr Encoding

**Spec Reference:** Section 2.1.1

**Interpretation:** Fr values must be in range [0, modulus). Values >= modulus are rejected, not reduced.

**Implementation:** `Fr.fromBytes32LECanonical` returns error E300 for non-canonical values

---

## 5. Error Code Stability

**Commitment:** Error codes E100-E707 are stable within major version

**Policy:** New error codes may be added; existing codes will not change meaning

**Reference:** `Jolt/Errors.lean` for complete taxonomy

---

## 6. Version Compatibility

**Current Version:** Implements spec sections 2-14

**Breaking Changes:** Any change to:
- Poseidon constants
- Transcript domain tags
- State digest algorithm
- Error code meanings

...requires a new major version.

---

## 7. Audit Trail

| Date | Item | Action |
|------|------|--------|
| 2026-01-08 | A1-A3 | Initial cryptographic assumptions documented |
| 2026-01-08 | T1-T3 | Trust boundaries defined |
| 2026-01-08 | L1-L4 | Known limitations documented |
| 2026-01-08 | D1-D5 | Spec interpretations documented |

---

## References

- Jolt Specification (spec.md)
- Poseidon Paper: https://eprint.iacr.org/2019/458.pdf
- BLS12-381: https://hackmd.io/@benjaminion/bls12-381
- Lean 4 Documentation: https://lean-lang.org/
