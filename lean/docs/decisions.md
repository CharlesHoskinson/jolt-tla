# Specification Interpretation Decisions

This document records decisions made when implementing the Jolt Oracle where the prose specification was ambiguous or required interpretation.

---

## D001: Transcript Tag Version Suffix

**Spec Reference:** §8.6

**Question:** Must transcript tags have a `/V[0-9]+` version suffix?

**Decision:** Version suffix is NOT required for transcript tags.

**Rationale:**
- §8.6 defines transcript tag format as: ASCII, `[A-Z0-9/_]`, starts with `JOLT/`, minimum length 5
- §3.3 separately defines registry key format which DOES require `/V[0-9]+$`
- The spec explicitly distinguishes these two formats
- Implementation accepts tags like `JOLT/STATE` without version suffix

**Code Location:** `Jolt/Transcript/TagValidation.lean`

---

## D002: JSON ASCII-Only Profile

**Spec Reference:** §2.3

**Question:** How should non-ASCII characters in JSON input be handled?

**Decision:** Reject any codepoint > 127 with E115_NonASCIICharacter.

**Rationale:**
- The spec mandates an ASCII-only JSON profile for deterministic parsing
- Unicode normalization (NFC/NFD) is non-deterministic across implementations
- Rejecting non-ASCII early prevents downstream canonicalization issues
- JCS (RFC 8785) sorting of keys uses UTF-16 code units; ASCII subset avoids complexity

**Code Location:** `Jolt/JSON/Parser.lean`

---

## D003: JSON Number Representation

**Spec Reference:** §2.3.1

**Question:** Should JSON numbers with exponents (e.g., `1e10`) be accepted?

**Decision:** Reject with E107_ExponentNotation.

**Rationale:**
- Scientific notation creates ambiguity (is `1.0e2` equal to `100`?)
- JCS requires specific number serialization format
- All values representable within oracle's needs fit in integer notation
- Fractions rejected with E108_FractionalNumber for same reason

**Code Location:** `Jolt/JSON/Parser.lean`

---

## D004: Registry Key Validation

**Spec Reference:** §3.2, §3.3

**Question:** What constitutes a valid registry key?

**Decision:** Keys must match `^JOLT_[A-Z0-9_]+_V[0-9]+$`

**Rationale:**
- Prefix `JOLT_` ensures namespace isolation
- Middle part `[A-Z0-9_]+` allows descriptive names
- Suffix `_V[0-9]+` mandates explicit versioning
- Examples: `JOLT_POSEIDON_FR_V1`, `JOLT_WRAPPER_VK_HASH_V1`

**Code Location:** `Jolt/Registry/Validate.lean`

---

## D005: External Handle Rejection

**Spec Reference:** §3.3

**Question:** Should registry.json contain external handles (VK_HASH, REGISTRY_HASH, CONFORMANCE_HASH)?

**Decision:** External handles must NOT be present in registry.json.

**Rationale:**
- External handles are computed values, not registry parameters
- Including them would create circular dependencies
- Registry hash must be deterministic from 17 non-external keys only
- Presence of external handles throws E201_ExternalHandlePresent

**Code Location:** `Jolt/Registry/Validate.lean`, `Jolt/Registry/Hash.lean`

---

## D006: StateDigest Absorption Order

**Spec Reference:** §11.10.2

**Question:** In what order should VMStateV1 fields be absorbed into the transcript?

**Decision:** Strict ordering: pc → regs[0..31] → step_counter → ...

**Rationale:**
- §11.10.2 specifies exact 14-step algorithm
- Order determines digest value; any deviation breaks conformance
- Registers absorbed in index order (x0 through x31)
- Implementation follows spec literally

**Code Location:** `Jolt/State/Digest.lean`

---

## D007: Register x0 Invariant

**Spec Reference:** §11.5

**Question:** How should register x0 be handled?

**Decision:** regs[0] must always be 0; non-zero throws E407_RegisterX0NonZero.

**Rationale:**
- RISC-V ABI defines x0 as hardwired zero
- Any state with non-zero x0 is invalid by definition
- Check performed during state validation, before digest computation

**Code Location:** `Jolt/State/VMState.lean`

---

## D008: Canonical Tar Format

**Spec Reference:** §14.3

**Question:** What makes a tar archive "canonical"?

**Decision:** All of the following must hold:
1. Members in bytewise lexicographic path order
2. All mtime fields are zero
3. No absolute paths or `..` components
4. No PAX extended headers
5. Regular files only (no directories, symlinks)
6. USTAR format headers

**Rationale:**
- Deterministic archive format enables reproducible builds
- Zero mtime prevents timestamp-based variations
- Sorted members enable efficient comparison
- PAX headers vary across implementations

**Code Location:** `Jolt/Bundle/Tar.lean`

---

## D009: Fr2 Encoding Split Point

**Spec Reference:** §2.2.1

**Question:** How should 32 bytes be split for Fr2 (two field elements)?

**Decision:** Split at byte 31: low 31 bytes → Fr1, high 1 byte → Fr2.

**Rationale:**
- BLS12-381 Fr modulus is ~255 bits
- 31 bytes (248 bits) fits in one Fr element
- Remaining 1 byte (8 bits) fits in second Fr element
- Little-endian byte order throughout

**Code Location:** `Jolt/Encoding/Fr2.lean`

---

## D010: Halted Flag Values

**Spec Reference:** §11.5

**Question:** What values are valid for the `halted` field?

**Decision:** Only {0, 1} are valid; other values throw E404_InvalidHalted.

**Rationale:**
- halted is a boolean concept (running vs stopped)
- Spec defines halted ∈ {0, 1}
- Non-boolean values indicate corruption or implementation error

**Code Location:** `Jolt/State/VMState.lean`

---

## D011: Poseidon Parameters Source

**Spec Reference:** §3.4

**Question:** Where do JOLT_POSEIDON_FR_V1 constants come from?

**Decision:** MDS matrix and round constants extracted from midnight-circuits v6.0.0.

**Rationale:**
- Jolt spec references JOLT_POSEIDON_FR_V1 as authoritative
- Parameters: width=3, RF=8, RP=60, α=5
- 204 round constants (68 rounds × 3 width)
- 3×3 MDS Cauchy matrix over BLS12-381

**Code Location:** `Jolt/Poseidon/Constants.lean`

---

## D012: Registry Hash Algorithm

**Spec Reference:** §3.3

**Question:** How is JOLT_PARAMETER_REGISTRY_HASH_V1 computed?

**Decision:** SHA-256 of JCS (RFC 8785) canonical bytes.

**Rationale:**
- JCS provides deterministic JSON serialization
- SHA-256 is widely implemented and collision-resistant
- Registry.json bytes must equal canonical form (no whitespace variations)
- Hash computed only over 17 required non-external keys

**Code Location:** `Jolt/Registry/Hash.lean`, `Jolt/Hash/SHA256.lean`

---

## Open Questions

### Q1: Wrapper VK Hash Personalization

**Spec Reference:** §12.2

**Status:** NEEDS_EVIDENCE

**Question:** What personalization bytes are used for wrapper VK hash?

**Notes:**
- `Wrapper/ProofSystem.lean:115-118` marks this as NEEDS_EVIDENCE
- Requires extraction from midnight-zk reference implementation

---

## Changelog

| Date | Decision | Author |
|------|----------|--------|
| 2026-01-09 | D001-D012 | Initial documentation |
