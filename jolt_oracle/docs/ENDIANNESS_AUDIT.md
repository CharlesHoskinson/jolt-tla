# Endianness Audit Report

## Summary

This document audits endianness handling in the Jolt Oracle implementation per spec section 2.5.

**Finding:** The implementation correctly uses **little-endian** throughout, consistent with the specification.

**Note:** Requirements document FR-04 mentioned "Big-Endian Binary Enforcement" but the actual spec section 2.5 mandates little-endian for canonical integer encodings.

## Audit Results

### 1. Fr.lean - Field Element Encoding

| Function | Endianness | Status |
|----------|------------|--------|
| `fromBytes32LECanonical` | Little-endian | CORRECT |
| `toBytes32LE` | Little-endian | CORRECT |
| `fromHex64LE` | Little-endian | CORRECT |
| `toHex64LE` | Little-endian | CORRECT |

**Evidence:**

`fromBytes32LECanonical` (lines 70-79):
```lean
for i in [:32] do
  val := val + (getByte bytes i).toNat * (256 ^ i)
```
Reads byte 0 as least significant (LE).

`toBytes32LE` (lines 82-88):
```lean
for _ in [:32] do
  bytes := bytes.push (val % 256).toUInt8
  val := val / 256
```
Writes least significant byte first (LE).

### 2. Fr2.lean - 31+1 Split Encoding

| Function | Endianness | Status |
|----------|------------|--------|
| `bytes32ToFr2` | Little-endian | CORRECT |
| `fr2ToBytes32` | Little-endian | CORRECT |

**Evidence:**

`bytes32ToFr2` (lines 16-21):
```lean
for i in [:31] do
  loVal := loVal + bytes.data[i]!.toNat * (256 ^ i)
let hiVal := bytes.data[31]!.toNat
```
First 31 bytes in LE order form `lo`, byte 31 is `hi`.

`fr2ToBytes32` (lines 30-47):
```lean
for _ in [:31] do
  bytes := bytes.push (lo % 256).toUInt8
  lo := lo / 256
bytes := bytes.push hiVal.toUInt8
```
Writes `lo` in LE order, then `hi` byte.

### 3. Transcript U64 Encoding

| Function | Method | Status |
|----------|--------|--------|
| `absorbU64` | Fr.fromU64 (numeric) | N/A |

**Note:** U64 values are converted numerically to Fr elements via `Fr.fromU64`, not byte-encoded. The sponge absorbs Fr elements directly, so byte endianness doesn't apply here.

### 4. Poseidon Constants

| Component | Format | Status |
|-----------|--------|--------|
| MDS matrix | FrToBytes32LE hex | CORRECT |
| Round constants | FrToBytes32LE hex | CORRECT |

All constants are stored as 64-character lowercase hex strings representing LE bytes.

## Specification Reference

From spec section 2.5:
> "Canonical integer encodings in this specification are **little-endian**"

## Test Coverage

The existing tests verify round-trip encoding:
- Fr → Bytes32 → Fr
- Bytes32 → Fr2 → Bytes32
- Fr ↔ Hex64

All round-trip tests pass, confirming encoding consistency.

## Conclusion

**PASS** - All byte encodings in the implementation use little-endian order, consistent with the specification. No changes required.

## Audit Checklist

- [x] Fr.fromBytes32LECanonical uses LE
- [x] Fr.toBytes32LE uses LE
- [x] Fr.fromHex64LE uses LE
- [x] Fr.toHex64LE uses LE
- [x] Fr2 31+1 split uses LE for lo bytes
- [x] Poseidon constants stored as LE hex
- [x] Round-trip tests pass
- [x] No BE (big-endian) functions in codebase
