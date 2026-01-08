# TLA+ / Lean Alignment Matrix

This document tracks alignment between the TLA+ formal specification and the Lean oracle implementation. When updating one, check the other.

## Quick Reference

| Concept | spec.md | TLA+ | Lean |
|---------|---------|------|------|
| Required registry keys | §3.4 | `tla/Registry.tla:RequiredKeys` | `Jolt/Registry/ConfigTags.lean:RequiredNonExternalTags` |
| External handle tags | §3.4 | `tla/Registry.tla:ExternalHandleTags` | `Jolt/Registry/ConfigTags.lean:ExternalHandleTags` |
| Transcript type tags | §8.4 | `tla/Transcript.tla:TYPE_*_FR` | `Jolt/Transcript/Types.lean:TYPE_*` |
| Tag format validation | §8.6 | `tla/Hash.tla:IsValidTagFormat` | `Jolt/Transcript/TagValidation.lean:isValidTagFormat` |
| status_fr semantics | §5.2 | `tla/Wrapper.tla:StatusToFr` | `Jolt/Wrapper/PublicInputs.lean:Status` |
| TAR canonicalization | §14.3 | `tla/Tar.tla:ValidTar` | `Jolt/Bundle/Tar.lean:validateTar` |
| StateDigest algorithm | §11.10.2 | `tla/Continuations.tla:ComputeStateDigest` | `Jolt/State/Digest.lean:computeStateDigest` |
| Public inputs count | §5.2 | `tla/Wrapper.tla:PublicInputsV1` (11 Fr) | `Jolt/Wrapper/PublicInputs.lean:PublicInputs` (11 Fr) |

## Registry Keys (17 Required)

### Required Keys (must appear in registry.json)

| Key | TLA+ | Lean | Status |
|-----|------|------|--------|
| `JOLT_POSEIDON_FR_V1` | Yes | Yes | Aligned |
| `JOLT_PCS_V1` | Yes | Yes | Aligned |
| `JOLT_TRANSCRIPT_SCHEDULE_V1` | Yes | Yes | Aligned |
| `JOLT_RISCV_PROFILE_V1` | Yes | Yes | Aligned |
| `JOLT_RISCV_UNPRIV_SPEC_V1` | Yes | Yes | Aligned |
| `JOLT_GUEST_MEMMAP_V1` | Yes | Yes | Aligned |
| `JOLT_TOOLCHAIN_V1` | Yes | Yes | Aligned |
| `JOLT_MAX_MANIFEST_BYTES_V1` | Yes | Yes | Aligned |
| `JOLT_MAX_INTENTS_V1` | Yes | Yes | Aligned |
| `JOLT_MAX_CHECKPOINTS_BYTES_V1` | Yes | Yes | Aligned |
| `JOLT_BATCH_MANIFEST_ENCODING_V1` | Yes | Yes | Aligned |
| `JOLT_BATCH_COMMITMENT_V1` | Yes | Yes | Aligned |
| `JOLT_CHECKPOINTS_ENCODING_V1` | Yes | Yes | Aligned |
| `JOLT_CONTEXT_BYTES32_V1` | Yes | Yes | Aligned |
| `JOLT_CONTINUATIONS_V1` | Yes | Yes | Aligned |
| `JOLT_IMPL_COMMIT_V1` | Yes | Yes | Aligned |
| `JOLT_WRAPPER_PROOF_SYSTEM_V1` | Yes | Yes | Aligned |

### External Handles (must NOT appear in registry.json)

| Key | TLA+ | Lean | Status |
|-----|------|------|--------|
| `JOLT_PARAMETER_REGISTRY_HASH_V1` | Yes | Yes | Aligned |
| `JOLT_WRAPPER_VK_HASH_V1` | Yes | Yes | Aligned |
| `JOLT_CONFORMANCE_BUNDLE_HASH_V1` | Yes | Yes | Aligned |

## Transcript Type Tags

Per spec §8.4, these are Fr discriminator values:

| Type | Value | TLA+ | Lean | Status |
|------|-------|------|------|--------|
| TYPE_BYTES | 1 | Yes (`TYPE_BYTES_FR`) | Yes | Aligned |
| TYPE_U64 | 2 | Yes (`TYPE_U64_FR`) | Yes | Aligned |
| TYPE_TAG | 3 | Yes (`TYPE_TAG_FR`) | Yes | Aligned |
| TYPE_VEC | 4 | Yes (`TYPE_VEC_FR`) | Yes | Aligned |

## status_fr Semantics

**Decision: Match Lean Jolt enum {0,1,2}**

| Value | Meaning | TLA+ | Lean | Status |
|-------|---------|------|------|--------|
| 0 | Success | Yes (`STATUS_SUCCESS`) | Yes | Aligned |
| 1 | Failure | Yes (`STATUS_FAILURE`) | Yes | Aligned |
| 2 | Pending | Yes (`STATUS_PENDING`) | Yes | Aligned |

Note: This differs from the original spec.md which used exit_code (0-255). The enum approach was chosen to match Lean Jolt implementation.

## Domain Tags (17 Total)

All domain tags are centralized in `tla/Hash.tla` with `IsValidTagFormat` validation per §8.6.

| Tag | Purpose | TLA+ Location | Status |
|-----|---------|---------------|--------|
| `JOLT/SMT/PAGE/V1` | SMT leaf hash | `Hash.tla:TAG_SMT_PAGE` | Aligned |
| `JOLT/SMT/NODE/V1` | SMT internal node | `Hash.tla:TAG_SMT_NODE` | Aligned |
| `JOLT/TRANSCRIPT/VM_STATE/V1` | Transcript VM state | `Hash.tla:TAG_TRANSCRIPT_VM_STATE` | Aligned |
| `JOLT/TRANSCRIPT/CHALLENGE/V1` | Challenge derivation | `Hash.tla:TAG_TRANSCRIPT_CHALLENGE` | Aligned |
| `JOLT/TRANSCRIPT/V1` | Transcript init | `Hash.tla:TAG_TRANSCRIPT_DOMAIN` | Aligned |
| `JOLT/BATCH/HEADER_LEAF/V1` | Batch header leaf | `Hash.tla:TAG_BATCH_HEADER_LEAF` | Aligned |
| `JOLT/BATCH/FILL_LEAF/V1` | Batch fill leaf | `Hash.tla:TAG_BATCH_FILL_LEAF` | Aligned |
| `JOLT/BATCH/EMPTY_FILL_LEAF/V1` | Empty fill leaf | `Hash.tla:TAG_BATCH_EMPTY_FILL_LEAF` | Aligned |
| `JOLT/BATCH/PAD_LEAF/V1` | Batch pad leaf | `Hash.tla:TAG_BATCH_PAD_LEAF` | Aligned |
| `JOLT/BATCH/NODE/V1` | Batch tree node | `Hash.tla:TAG_BATCH_NODE` | Aligned |
| `JOLT/BATCH/COMMIT/V1` | Batch commitment | `Hash.tla:TAG_BATCH_COMMITMENT` | Aligned |
| `JOLT/STATE/V1` | StateDigest | `Hash.tla:TAG_STATE_DIGEST` | Aligned |
| `JOLT/CONFIG_TAGS/V1` | Config binding | `Hash.tla:TAG_CONFIG_TAGS` | Aligned |
| `JOLT/TAG/V1` | Per-tag separator | `Hash.tla:TAG_TAG` | Aligned |
| `JOLT/CHECKPOINTS/V1` | Checkpoints hash | `Hash.tla:TAG_CHECKPOINTS` | Aligned |
| `JOLT/CHECKPOINTS/DIGEST/V1` | Checkpoints digest | `Hash.tla:TAG_CHECKPOINTS_DIGEST` | Aligned |
| `JOLT/IO/INIT/V1` | IO initialization | `Hash.tla:TAG_IO_INIT` | Aligned |

Tag format validation: Tags must start with `JOLT/`, use charset `[A-Z0-9/_]`, and be ASCII-only.

## Verification Surfaces

### TLA+ (Abstracted)
- Hash functions: idealized as collision-resistant
- Field arithmetic: bounded for TLC tractability (FR_TLC_BOUND)
- StateDigest: uses fingerprint-based model (not actual Poseidon permutation)

### Lean Oracle (Exact)
- Poseidon permutation with actual round constants
- Exact byte encoding per spec
- Full validation logic with error reporting

### Alignment Automation

Run `./scripts/check_alignment.sh` to verify constants match between TLA+ and Lean.

## New Modules (v0.3.1)

| Module | Purpose | Lean Counterpart |
|--------|---------|------------------|
| `Tar.tla` | TAR archive validation (§14.3) | `Jolt/Bundle/Tar.lean` |
| `JSON.tla` | JSON safety + JCS (§2.6.1) | `Jolt/JSON/*.lean` |
| `Bundle.tla` | Conformance bundle | `Jolt/Bundle/*.lean` |
| `RegistryValidationTests.tla` | Registry test cases | - |
| `TranscriptValidationTests.tla` | Transcript test cases | - |

## Updating This Document

When you modify:
1. `tla/Registry.tla` → Update Registry Keys section
2. `tla/Transcript.tla` → Update Transcript Type Tags section
3. `tla/Hash.tla` → Update Domain Tags section
4. `tla/Wrapper.tla` → Update status_fr section
5. Any Lean file → Update corresponding TLA+ status

## Related Documents

- `docs/architecture.md` - System design
- `docs/invariants.md` - Invariant catalog
- `spec.md` - Normative specification
