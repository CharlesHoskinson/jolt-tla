# Jolt Kernel Scope

## In Scope (Kernel Implements)

| Module | Spec Section | Description |
|--------|--------------|-------------|
| Types.lean | S5, S7 | Bytes32, U64, Fr (as Fin r), Fr2 |
| Encoding.lean | S7.2 | Bytes32ToFr2, Fr2ToBytes32, injectivity |
| Transcript.lean | S8 | Sponge state machine, absorb_tag |
| ConfigTags.lean | S3.8 | RFC 8785 JCS (manual implementation) |
| StateDigest.lean | S11.10 | 14-step StateDigestV1 algorithm |
| Wrapper.lean | S5.2, S5.6 | PublicInputsV1, binding checker |
| Continuations.lean | S11 | Chunk chaining validation |
| Kernel.lean | - | Consolidated exports and theorems |

## Trusted Computing Base (Out of Scope)

| Constant | Type | Notes |
|----------|------|-------|
| `PoseidonPermute` | `Vector Fr t -> Vector Fr t` | Cryptographic assumption |

## Kernel Theorems

Every `check : a -> Bool` has `theorem check_sound : check x = true -> Spec x`

## Design Decisions (GPT Research-Backed)

| Component | Decision | Rationale |
|-----------|----------|-----------|
| Fr type | `def Fr := Fin r` | Enforces canonicity, rejects non-canonical (Q2) |
| Vectors | `Vector a n` | Array-backed, O(1) access (Q4) |
| Bytes32 | `Vector UInt8 32` | Type-level length guarantee (Q4) |
| Prop/Bool | `checkFoo = decide SpecFoo` | Easy soundness via `Bool.of_decide_true` (Q3) |
| Poseidon | `constant PoseidonPermute` | Minimal axiom, document as TCB (Q5) |

## Audit Checklist

- [ ] FEYNMAN CHECK: Can auditor read only Jolt/Kernel.lean?
- [ ] HALMOS CHECK: Every check has check_sound theorem?
- [ ] RUSSELL CHECK: Boundaries explicit?
