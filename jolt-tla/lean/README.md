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

Expected output: `148 passed, 0 failed`

## Usage

### Interactive REPL

```bash
lake exe oracle
```

Or use the built executable directly:

```bash
.lake/build/bin/oracle.exe
```

### Commands

| Command | Description |
|---------|-------------|
| `status` | Show oracle health dashboard |
| `digest <file>` | Compute state digest |
| `verify chain <file>` | Verify continuation chain |
| `verify vectors <file>` | Run conformance test vectors |
| `diff <a> <b>` | Compare two state files |
| `explain <code>` | Explain error code |
| `generate <type> <file>` | Generate test vector |

### REPL Commands

| Command | Description |
|---------|-------------|
| `:help` | Show help |
| `:load <file> [as <var>]` | Load file into variable |
| `:set <key> <value>` | Set variable |
| `:show <var>` | Display variable |
| `:source <file>` | Run script |
| `:quit` | Exit REPL |

### Batch Mode

```bash
lake exe oracle repl --batch script.oracle
```

Options:
- `--strict` - Stop on first error (default)
- `--continue` - Continue after errors
- `--quiet` - Suppress command echo

## Architecture

```
jolt_oracle/
├── Jolt/                    # Core library
│   ├── Field/Fr.lean        # BLS12-381 scalar field
│   ├── Encoding/            # Bytes32, Fr2 encoding
│   ├── Poseidon/            # Hash function
│   ├── Transcript/          # Domain separation
│   ├── State/               # VMState, Digest
│   ├── Registry/            # Config validation
│   └── Bundle/              # Tar handling
├── CLI/                     # Command-line interface
│   ├── Commands/            # Subcommands
│   └── REPL/                # Interactive shell
└── Tests/                   # Test suites
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

## License

See LICENSE file.
