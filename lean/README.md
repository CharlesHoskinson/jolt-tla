# Jolt Executable Spec Oracle

A Lean 4 implementation serving as the canonical specification for Jolt zkVM consensus-critical computations.

## Overview

The Jolt Oracle defines correctness for zkVM state transitions. If a Rust implementation differs from the oracle's output, the Rust implementation is considered incorrect. The oracle generates conformance test vectors that all implementations must pass.

## Features

- **State Digest Computation** - Poseidon-based state hashing per JOLT_POSEIDON_FR_V1
- **Chain Verification** - Validate continuation chain linkage
- **Conformance Testing** - Run test vectors against the specification
- **Interactive REPL** - Explore and debug state computations
- **Batch Processing** - Script-driven automation

## Installation

### Prerequisites

- [Lean 4.26.0](https://leanprover.github.io/lean4/doc/setup.html) (via elan)

### Build

```bash
cd jolt_oracle
lake build
```

### Run Tests

```bash
lake exe test
```

Expected output: `149 passed, 0 failed`

## Usage

### Interactive REPL

```bash
lake exe oracle
```

Or use the built executable directly:

```bash
.lake/build/bin/oracle.exe
```

### CLI Commands

| Command | Description |
|---------|-------------|
| `status` | Show oracle health dashboard |
| `digest <file>` | Compute state digest |
| `verify chain <file>` | Verify continuation chain |
| `verify vectors <file>` | Run conformance test vectors |
| `diff <a> <b>` | Compare two state files |
| `explain <code>` | Explain error code |
| `generate <type> <file>` | Generate test vector |

### CLI Examples

**Compute state digest from JSON:**

```bash
# Compute StateDigestV1 for a state file
lake exe oracle digest state.json

# Output:
# StateDigest: 0x1a2b3c4d...
# Program Hash: 0x5e6f7a8b...
# Step Counter: 1000
```

**Verify a continuation chain:**

```bash
# Verify all chunks link correctly
lake exe oracle verify chain continuation_chain.json

# Output (success):
# Chain: 5 chunks verified
# Start digest: 0x...
# End digest: 0x...
# Final state: halted=1, exit_code=0

# Output (failure):
# ERROR E500: Chain break at chunk 3
# Expected: 0x...
# Got: 0x...
```

**Run conformance test vectors:**

```bash
# Verify implementation against golden vectors
lake exe oracle verify vectors test_vectors/golden_v1.json

# Output:
# Vector 1/10: minimal_state ✓
# Vector 2/10: typical_state ✓
# ...
# 10/10 vectors passed
```

**Compare two state files:**

```bash
lake exe oracle diff state_a.json state_b.json

# Output:
# pc: 0x1000 → 0x1004
# regs[1]: 0 → 42
# step_counter: 100 → 101
```

**Get error code explanation:**

```bash
lake exe oracle explain E500

# E500_ChainBreak
# Category: Chain Verification
# Description: Continuation chunk does not link to previous chunk.
#              end_digest[i] must equal start_digest[i+1].
# Spec Reference: §11.8
```

**Generate test vectors:**

```bash
# Generate minimal state vector
lake exe oracle generate state minimal_vector.json

# Generate chain verification vector
lake exe oracle generate chain chain_vector.json
```

### REPL Commands

| Command | Description |
|---------|-------------|
| `:help` | Show help |
| `:load <file> [as <var>]` | Load file into variable |
| `:set <key> <value>` | Set variable |
| `:show <var>` | Display variable |
| `:source <file>` | Run script |
| `:quit` | Exit REPL |

### REPL Session Example

```
$ lake exe oracle
Jolt Oracle v1.0.0
Type :help for commands

oracle> :load state.json as s
Loaded state.json → $s

oracle> digest $s
StateDigest: 0x1a2b3c4d...

oracle> :set program_hash 0x5e6f7a8b...
$program_hash = 0x5e6f7a8b...

oracle> verify $s with $program_hash
✓ State digest verified

oracle> $_
0x1a2b3c4d...

oracle> $?
0

oracle> :quit
```

### Batch Mode

```bash
lake exe oracle repl --batch script.oracle
```

Options:
- `--strict` - Stop on first error (default)
- `--continue` - Continue after errors
- `--quiet` - Suppress command echo

**Example batch script (verify.oracle):**

```
# Load states and verify chain
:load chunk_0.json as c0
:load chunk_1.json as c1
:load chunk_2.json as c2
verify chain [$c0, $c1, $c2]
```

## Architecture

### Directory Structure

```
jolt_oracle/
├── Jolt/                    # Core library
│   ├── Field/Fr.lean        # BLS12-381 scalar field
│   ├── Encoding/            # Bytes32, Fr2 encoding
│   ├── Poseidon/            # Hash function
│   ├── Hash/SHA256.lean     # Registry hash
│   ├── Transcript/          # Domain separation
│   ├── State/               # VMState, Digest
│   ├── Registry/            # Config validation
│   ├── JSON/                # Parser, JCS
│   ├── Bundle/              # Tar handling
│   └── Wrapper/             # Proof system types
├── CLI/                     # Command-line interface
│   ├── Commands/            # Subcommands
│   ├── Report/              # Error reporting
│   └── REPL/                # Interactive shell
└── Tests/                   # Test suites
```

### Component Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                         CLI / REPL                               │
│  ┌─────────┐ ┌─────────┐ ┌────────┐ ┌──────────┐ ┌────────────┐ │
│  │ digest  │ │ verify  │ │  diff  │ │ generate │ │  explain   │ │
│  └────┬────┘ └────┬────┘ └───┬────┘ └────┬─────┘ └─────┬──────┘ │
└───────┼──────────┼──────────┼───────────┼──────────────┼────────┘
        │          │          │           │              │
        ▼          ▼          ▼           ▼              ▼
┌─────────────────────────────────────────────────────────────────┐
│                        Oracle API                                │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │  computeStateDigest   verifyChain   generateTestVector     │ │
│  └────────────────────────────────────────────────────────────┘ │
└───────────────────────────────┬─────────────────────────────────┘
                                │
        ┌───────────────────────┼───────────────────────┐
        ▼                       ▼                       ▼
┌───────────────┐    ┌─────────────────────┐    ┌──────────────┐
│    State      │    │     Transcript      │    │   Registry   │
│  ┌─────────┐  │    │  ┌───────────────┐  │    │ ┌──────────┐ │
│  │VMStateV1│  │    │  │Domain Separate│  │    │ │ Validate │ │
│  │ Digest  │  │    │  │ absorb_bytes  │  │    │ │ConfigTags│ │
│  └────┬────┘  │    │  │ absorb_u64    │  │    │ │  Hash    │ │
│       │       │    │  └───────┬───────┘  │    │ └────┬─────┘ │
└───────┼───────┘    └──────────┼──────────┘    └──────┼───────┘
        │                       │                      │
        └───────────────────────┼──────────────────────┘
                                ▼
┌─────────────────────────────────────────────────────────────────┐
│                     Cryptographic Layer                          │
│  ┌──────────────────────────┐  ┌─────────────────────────────┐  │
│  │       Poseidon           │  │          SHA-256            │  │
│  │  ┌───────┐ ┌──────────┐  │  │  ┌─────────────────────┐    │  │
│  │  │Sponge │ │ Constants│  │  │  │   FIPS 180-4        │    │  │
│  │  │permute│ │ MDS, RC  │  │  │  │   Registry Hash     │    │  │
│  │  └───────┘ └──────────┘  │  │  └─────────────────────┘    │  │
│  └──────────────────────────┘  └─────────────────────────────┘  │
└───────────────────────────────┬─────────────────────────────────┘
                                │
                                ▼
┌─────────────────────────────────────────────────────────────────┐
│                        Field Layer                               │
│  ┌──────────────────┐  ┌────────────────┐  ┌──────────────────┐ │
│  │       Fr         │  │    Bytes32     │  │       Fr2        │ │
│  │ BLS12-381 scalar │  │  Fixed 32-byte │  │  31+1 split enc  │ │
│  │  +, -, *, ^5     │  │   toFr, toHex  │  │ bytes32ToFr2     │ │
│  └──────────────────┘  └────────────────┘  └──────────────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

### Data Flow

```
Input (JSON)
     │
     ▼
┌──────────┐  ASCII-only      ┌────────────┐
│  Parser  │─────────────────►│ Validation │
└──────────┘  profile         └─────┬──────┘
                                    │
     ┌──────────────────────────────┘
     ▼
┌──────────┐                  ┌────────────┐
│VMStateV1 │─────────────────►│ Transcript │
└──────────┘                  └─────┬──────┘
                                    │ absorb fields
     ┌──────────────────────────────┘
     ▼
┌──────────┐  squeeze         ┌────────────┐
│ Poseidon │─────────────────►│StateDigest │
│  Sponge  │                  │    (Fr)    │
└──────────┘                  └────────────┘
```

## Specification Compliance

| Component | Spec Section |
|-----------|--------------|
| Fr modulus | §2.1.1 |
| Fr2 encoding | §2.2.1 |
| Poseidon parameters | §3.4 |
| Transcript tags | §8.6 |
| Registry keys | §3.2 |
| VMStateV1 | §11.5 |
| StateDigest | §11.10.2 |
| Canonical tar | §14.3 |

## Field Parameters

- **Field**: BLS12-381 scalar (Fr)
- **Modulus**: 52435875175126190479447740508185965837690552500527637822603658699938581184513
- **Bits**: 255

## Poseidon Configuration

- **Width (t)**: 3
- **Full rounds**: 8
- **Partial rounds**: 60
- **S-box exponent**: 5
- **Total rounds**: 68

## Error Codes

### Overview

| Range | Category |
|-------|----------|
| E1xx | JSON/Input errors |
| E2xx | Registry errors |
| E3xx | Field encoding errors |
| E4xx | State validation errors |
| E5xx | Chain verification errors |
| E6xx | Hash/commitment errors |
| E7xx | Tar/bundle errors |

Run `oracle explain E404` for detailed error information.

### Complete Error Reference

#### JSON/Input Errors (E100-E199)

| Code | Name | Description |
|------|------|-------------|
| E100 | InvalidJSON | Input is not valid JSON syntax |
| E101 | DuplicateKey | Object contains duplicate key |
| E102 | InvalidBase64 | Invalid base64 encoding |
| E103 | InvalidHex | Invalid hexadecimal encoding |
| E104 | WrongLength | Value has incorrect byte length |
| E105 | InvalidUTF8 | Invalid UTF-8 encoding |
| E106 | UnexpectedType | JSON value is wrong type (e.g., expected object, got array) |
| E107 | ExponentNotation | Number uses scientific notation (not allowed) |
| E108 | FractionalNumber | Number has fractional part (integers only) |
| E109 | IntegerOutOfRange | Integer outside ±2^53-1 range |
| E110 | InputTooLarge | Input exceeds size limit |
| E111 | NestingTooDeep | JSON nesting exceeds depth limit |
| E112 | StringTooLong | String exceeds length limit |
| E113 | TooManyFields | Object has too many fields |
| E114 | ArrayTooLong | Array exceeds length limit |
| E115 | NonASCIICharacter | Character codepoint > 127 (ASCII-only profile) |

#### Registry Errors (E200-E299)

| Code | Name | Description |
|------|------|-------------|
| E200 | UnknownRegistryKey | Key not in allowed set |
| E201 | ExternalHandlePresent | External handle (VK_HASH, etc.) in registry.json |
| E202 | MissingRequiredKey | Required key absent from registry |
| E203 | TBDValuePresent | Key has placeholder "TBD" value |
| E204 | InvalidRegistryHash | Registry hash does not match computed value |
| E205 | NonCanonicalJSON | Registry JSON not in JCS canonical form |
| E206 | InvalidKeyFormat | Key doesn't match `^JOLT_[A-Z0-9_]+_V[0-9]+$` |

#### Field Errors (E300-E399)

| Code | Name | Description |
|------|------|-------------|
| E300 | NonCanonicalFr | Field element not in canonical form (≥ modulus) |
| E301 | Fr2LoBoundsViolation | Low 31 bytes of Fr2 exceed bounds |
| E302 | Fr2HiBoundsViolation | High byte of Fr2 exceeds bounds |
| E303 | InvalidFrEncoding | General field encoding error |

#### State Errors (E400-E499)

| Code | Name | Description |
|------|------|-------------|
| E400 | BindingMismatch | Prover binding doesn't match computed value |
| E401 | OrderingViolation | Fields in wrong absorption order |
| E402 | OutOfRange | Value outside valid range |
| E403 | ReservedNonZero | Reserved field is non-zero |
| E404 | InvalidHalted | Halted flag not in {0, 1} |
| E405 | TerminationInvariant | Termination invariant violated |
| E406 | InvalidTagFormat | Transcript tag format invalid |
| E407 | RegisterX0NonZero | Register x0 is not zero |

#### Chain Errors (E500-E599)

| Code | Name | Description |
|------|------|-------------|
| E500 | ChainBreak | end_digest[i] ≠ start_digest[i+1] |
| E501 | DigestMismatch | Computed digest doesn't match claimed digest |
| E502 | InvalidChunkIndex | Chunk index not sequential |
| E503 | EmptyChain | Chain has no chunks |

#### Hash Errors (E600-E699)

| Code | Name | Description |
|------|------|-------------|
| E600 | HashMismatch | Computed hash doesn't match expected |
| E601 | CommitmentMismatch | Commitment verification failed |
| E602 | TranscriptMismatch | Transcript state doesn't match |

#### Tar Errors (E700-E799)

| Code | Name | Description |
|------|------|-------------|
| E700 | NonCanonicalTar | Tar archive not in canonical form |
| E701 | InvalidTarHeader | Malformed tar header |
| E702 | UnsortedMembers | Members not in bytewise lexicographic order |
| E703 | NonZeroMtime | Member has non-zero mtime |
| E704 | InvalidPath | Path contains `..`, absolute path, or special chars |
| E705 | DuplicateMember | Duplicate path in archive |
| E706 | InvalidMemberType | Unsupported member type (not regular file) |
| E707 | PAXExtensionPresent | PAX extended header present (not allowed) |
| E708 | MissingRegistryJson | Bundle lacks registry.json |

## License

See LICENSE file.
