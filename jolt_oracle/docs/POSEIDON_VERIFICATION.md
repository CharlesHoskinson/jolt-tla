# JOLT_POSEIDON_FR_V1 Constants Verification

## Overview

This document provides verification evidence for the Poseidon hash constants used in the Jolt Oracle implementation per spec section 3.4.1.

## Parameter Summary

| Parameter | Value | Source |
|-----------|-------|--------|
| Field | BLS12-381 scalar field Fr | Spec 2.1.1 |
| Width (t) | 3 | Spec 3.4.1 |
| Rate (r) | 2 | Spec 3.4.1 |
| Capacity (c) | 1 | Spec 3.4.1 |
| Full rounds (RF) | 8 | Spec 3.4.1 |
| Partial rounds (RP) | 60 | Spec 3.4.1 |
| S-box exponent (alpha) | 5 | Spec 3.4.1 |
| Security level | 128 bits | Spec 3.4.1 |

## Constants Source

**Source:** midnight-circuits v6.0.0
**Module:** `midnight_circuits::hash::poseidon::constants`

### MDS Matrix (3x3)

The MDS matrix is stored as FrToBytes32LE hex strings (64 lowercase hex characters).

| Position | Hex Value (LE) |
|----------|----------------|
| M[0][0] | `ce1ab50741de1861779eba534074d58aa6d8e21012246d5dfd22b981c314811b` |
| M[0][1] | `63d7c0fc137271e3b4094cecca0c99751733f59c89215d0ed22ecbc44c2ef33d` |
| M[0][2] | `c1ede1a0ae34cd3e0b08911560337f00b48e54bf798725beda64667adfc4053f` |
| M[1][0] | `74b3a831cd01f5d7b1e70f954b3174ca06ae3f6dd74a2a434ed1853907214d40` |
| M[1][1] | `f14956950316faf72f42797631b2e9734b4d529e0e62bc81bdc6644270c82c0b` |
| M[1][2] | `1f1a7f638cfca8e2b448438319b50b6d495d0341c688935afa5950a54d66df0f` |
| M[2][0] | `4091c4907ec55df90a735ab601ad9731035d5cf4474ae2434321a6cdbe3d1d5e` |
| M[2][1] | `8aa75a2f00b9c77df35489ae5f6dcb4412c6a57ee79618939daf53fc9c2fd76b` |
| M[2][2] | `dbe09df98eb84fbbd9468ed59cbdff1e83ef4b05a980f8ca7ba05f3aaac59749` |

### Round Constants

- **Total constants:** 204 (68 rounds x 3 elements)
- **Storage:** `Jolt/Poseidon/Constants.lean`
- **Format:** FrToBytes32LE hex strings

## Verification Functions

The implementation provides these validation functions in `Jolt/Poseidon/Constants.lean`:

### `validateConstants : Bool`
Verifies structural correctness:
- MDS matrix has correct dimensions (3x3)
- Round constants array has correct size (204 elements)

### `validateMdsMatrix : Bool`
Verifies MDS matrix values by round-trip encoding:
- Encodes each Fr element to hex
- Compares against expected hex strings
- Ensures no encoding/decoding errors

### `roundConstantsArePlaceholder : Bool`
Safety check to detect uninitialized constants (all zeros).

## Test Coverage

The test suite (`Tests/Main.lean`) includes:

1. **testPoseidonMDS** - Validates MDS matrix dimensions and hex encoding
2. **testPoseidonRoundConstants** - Validates round constant count (204)
3. **testPoseidonConfig** - Validates complete configuration

## Verification Steps

To verify Poseidon constants:

```bash
cd jolt_oracle
lake build
lake exe test
```

Expected output includes:
```
=== Poseidon Constants Tests ===
PASS: Poseidon MDS matrix
PASS: Poseidon round constants structure
PASS: Poseidon config
```

## Known-Answer Test Vectors

The following test vectors can be used to verify Poseidon implementation correctness:

### Vector 1: Zero Input
- **Input:** `[Fr.zero, Fr.zero, Fr.zero]`
- **Expected:** Determined by reference implementation

### Vector 2: Unit Input
- **Input:** `[Fr.one, Fr.zero, Fr.zero]`
- **Expected:** Determined by reference implementation

**Status:** Test vectors pending generation from midnight-circuits reference.

## Cross-Reference Checklist

- [x] Width = 3 matches spec 3.4.1
- [x] Full rounds = 8 matches spec 3.4.1
- [x] Partial rounds = 60 matches spec 3.4.1
- [x] S-box exponent = 5 matches spec 3.4.1
- [x] 204 round constants (68 x 3)
- [x] 9 MDS matrix elements (3 x 3)
- [x] MDS stored as FrToBytes32LE hex
- [x] Source documented as midnight-circuits v6.0.0
- [ ] Known-answer vectors validated (pending)

## References

- Jolt Specification Section 3.4.1
- Jolt Specification Appendix A
- midnight-circuits v6.0.0 source
- Poseidon Paper: https://eprint.iacr.org/2019/458.pdf
