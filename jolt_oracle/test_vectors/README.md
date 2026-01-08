# Jolt Oracle Test Vectors

## Overview

This directory contains golden test vectors for Jolt Oracle conformance testing.

## Files

- `golden_v1.json` - Version 1.0 test vectors for state digest and chain verification

## Vector Types

### 1. State Digest Vectors (`type: "state_digest"`)

Test the `computeStateDigest` function per spec section 11.10.2.

**Input:**
- `program_hash`: 64-char hex string (32 bytes)
- `state`: VMStateV1 object

**Expected Output:**
- `status`: "ok" or "error"
- `digest_hex`: 64-char hex string (for ok status)
- `error_code`: Error code string (for error status)

### 2. Chain Verification Vectors (`type: "chain_verification"`)

Test the `verifyChain` function per spec section 11.

**Input:**
- `program_hash`: 64-char hex string
- `chunks`: Array of chunk objects

**Expected Output:**
- `status`: "ok" or "error"
- `error_code`: Error code string (for error status)

## Generating Expected Values

The `TODO_COMPUTE_WITH_ORACLE` placeholders in `golden_v1.json` must be filled in by running the oracle:

```bash
cd jolt_oracle
lake build
lake exe oracle generate state test_vectors/input_minimal.json
```

Or use the REPL:

```bash
lake exe oracle repl
> :load state test_vectors/input_minimal.json
> digest $state
```

## Verification

Run all test vectors:

```bash
lake exe oracle verify vectors test_vectors/golden_v1.json
```

Expected output:
```
Running 7 state digest vectors...
  minimal_state_zeros: PASS
  typical_state: PASS
  halted_state: PASS
  state_with_config_tags: PASS
  invalid_register_x0: PASS (expected error)
  invalid_halted_value: PASS (expected error)
  invalid_exit_code_when_halted: PASS (expected error)

Running 4 chain vectors...
  valid_single_chunk: PASS
  valid_three_chunks: PASS
  invalid_broken_linkage: PASS (expected error)
  invalid_skipped_chunk: PASS (expected error)

All 11 vectors passed
```

## Adding New Vectors

1. Add new vector object to `golden_v1.json`
2. Run oracle to compute expected value
3. Update expected output in JSON
4. Run full verification to confirm

## Schema

See `CLI/Schema/TestVector.lean` for the full JSON schema definition.
