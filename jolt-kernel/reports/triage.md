# Jolt Kernel QA Triage Report

**Date:** 2026-01-06
**Lean Version:** 4.26.0
**Git HEAD:** 602437fee3dd94769d80fd395195dd18e2420d99

## Stop-the-Line Gate Status

| Gate | Status | Details |
|------|--------|---------|
| GATE A (sorry in P0) | ✅ CLEAR | No sorries found in P0 modules |
| GATE B (unauthorized TCB) | ⛔ **TRIGGERED** | 9 unauthorized axioms found |
| GATE C (spec divergence) | ⚠️ UNKNOWN | spec.md not available |
| GATE D (soundness break) | ✅ CLEAR | No soundness breaks found (but axioms untested) |

## Ship Decision

- [x] Build passes ✅
- [x] Tests pass (no test suite defined) ⚠️
- [ ] **All gates CLEAR** ❌
- [ ] **No CRITICAL findings unresolved** ❌

**SHIP DECISION: ⛔ NO SHIP**

**Reason:** 9 unauthorized axioms violate KERNEL_SCOPE.md which allows only `PoseidonPermute` as TCB.

---

## CRITICAL Findings (3)

### F001: 7 Unauthorized Axioms in Encoding.lean
- **Severity:** CRITICAL
- **File:** Jolt/Encoding.lean:141-174
- **Issue:** 7 axioms bypass proof requirements for byte encoding
- **Axioms:**
  - `bytesToNatLE_natToBytesLE`
  - `natToBytesLE_bytesToNatLE`
  - `bytesToNatLE_bound`
  - `bytes31_bound` (trivially provable: 256^31 = 2^248)
  - `roundtrip_sound`
  - `injective_sound`
  - `Bytes32ToFr2_succeeds`
- **Status:** NEEDS_HUMAN

### F002: Unauthorized Axiom in ConfigTags.lean
- **Severity:** CRITICAL
- **File:** Jolt/ConfigTags.lean:98
- **Issue:** `checkConfigTags_sound` axiomatized instead of proven
- **Status:** NEEDS_HUMAN

### F003: Unauthorized Axiom in StateDigest.lean
- **Severity:** HIGH (downgraded from CRITICAL)
- **File:** Jolt/StateDigest.lean:200
- **Issue:** `stateDigest_collision_resistant` axiomatized
- **Note:** This may be a legitimate cryptographic assumption, but should either be proven from PoseidonPermute or explicitly documented as TCB extension
- **Status:** NEEDS_HUMAN

---

## HIGH Findings (1)

### F004: Documentation Mismatch
- **File:** Jolt/Kernel.lean:153
- **Issue:** `AXIOM_COUNT = 1` but actual count is 10
- **Status:** NEEDS_HUMAN

---

## Remaining Work

### Priority 1: Fix Trivially Provable Axioms
- `bytes31_bound : 256^31 = 2^248` can be proven via computation

### Priority 2: Prove Arithmetic Lemmas
- `bytesToNatLE_natToBytesLE` - by induction
- `natToBytesLE_bytesToNatLE` - by induction
- `bytesToNatLE_bound` - by induction

### Priority 3: Prove Soundness Theorems
- `roundtrip_sound` - depends on arithmetic lemmas
- `injective_sound` - depends on arithmetic lemmas
- `Bytes32ToFr2_succeeds` - depends on bounds
- `checkConfigTags_sound` - by induction on list

### Priority 4: Resolve Crypto Axiom
- Either prove `stateDigest_collision_resistant` from PoseidonPermute
- Or document it as second TCB axiom with justification

---

## Axiom Summary

| Category | Count | Items |
|----------|-------|-------|
| Allowed (TCB) | 1 | PoseidonPermute |
| Provable Arithmetic | 4 | bytesToNatLE_*, natToBytesLE_*, bytes31_bound |
| Provable Soundness | 4 | roundtrip_sound, injective_sound, Bytes32ToFr2_succeeds, checkConfigTags_sound |
| Crypto Assumption | 1 | stateDigest_collision_resistant |
| **Total Unauthorized** | **9** | |

---

## Verification Commands

```bash
# Current axiom count
grep -rn "^axiom" Jolt/*.lean | wc -l
# Expected: 1 (PoseidonPermute only)
# Actual: 10

# Audit specific theorem
#print axioms Jolt.Kernel.wrapper_sound

# Check for sorries
grep -rn "sorry" Jolt/*.lean
# Expected: None in code (only comments)
```

---

## Conclusion

The Jolt kernel builds successfully and contains well-structured code with proper soundness theorems for Wrapper and Continuations modules. However, **9 unauthorized axioms** significantly expand the TCB beyond the documented single axiom (PoseidonPermute).

**Action Required:** Convert axioms to theorems before the kernel can be considered verified.
