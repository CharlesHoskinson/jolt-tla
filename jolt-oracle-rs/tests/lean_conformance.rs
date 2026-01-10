//! Lean conformance tests using live subprocess invocation.
//!
//! These tests run the Lean oracle as a subprocess and compare
//! its output against the Rust implementation.
//!
//! # Requirements
//!
//! Set LEAN_ORACLE_PATH environment variable to the jolt_oracle directory
//! where the Lean oracle has been built with `lake build`.
//!
//! # CI Integration
//!
//! The rust.yml workflow Job K builds the Lean oracle and runs these tests
//! with LEAN_ORACLE_PATH set automatically.

use jolt_oracle::conformance::{DiffTestHarness, OracleOutput};
use jolt_oracle::state::{Bytes32, VMStateV1};
use std::env;

/// Get the Lean oracle path from environment, or None if not set.
fn lean_oracle_path() -> Option<String> {
    env::var("LEAN_ORACLE_PATH").ok()
}

/// Skip test if Lean oracle is not available.
macro_rules! skip_if_no_lean {
    () => {
        if lean_oracle_path().is_none() {
            eprintln!("LEAN_ORACLE_PATH not set, skipping Lean conformance tests");
            return;
        }
    };
}

/// Golden test vectors derived from the Lean specification.
struct GoldenVector {
    name: &'static str,
    program_hash: &'static str,
    state: VMStateV1,
    expected_digest: &'static str,
}

fn golden_vectors() -> Vec<GoldenVector> {
    vec![
        GoldenVector {
            name: "minimal_state_zeros",
            program_hash: "0000000000000000000000000000000000000000000000000000000000000000",
            state: VMStateV1::default(),
            expected_digest:
                "24421670062301725635551677633693836338234896090794496795972501815695727753187",
        },
        GoldenVector {
            name: "typical_state",
            program_hash: "abcd1234567890abcd1234567890abcd1234567890abcd1234567890abcd1234",
            state: VMStateV1 {
                pc: 4096,
                regs: [
                    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
                    22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
                ],
                step_counter: 1000,
                rw_mem_root: Bytes32::from_hex(
                    "1111111111111111111111111111111111111111111111111111111111111111",
                )
                .unwrap(),
                io_root: Bytes32::from_hex(
                    "2222222222222222222222222222222222222222222222222222222222222222",
                )
                .unwrap(),
                halted: 0,
                exit_code: 0,
                config_tags: vec![],
            },
            expected_digest:
                "30919686901236335602438576816898388225550310633849398790605613577781839025832",
        },
        GoldenVector {
            name: "halted_state",
            program_hash: "deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef",
            state: VMStateV1 {
                pc: 8192,
                regs: [
                    0, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000, 1100, 1200, 1300, 1400,
                    1500, 1600, 1700, 1800, 1900, 2000, 2100, 2200, 2300, 2400, 2500, 2600, 2700,
                    2800, 2900, 3000, 3100,
                ],
                step_counter: 50000,
                rw_mem_root: Bytes32::from_hex(
                    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                )
                .unwrap(),
                io_root: Bytes32::from_hex(
                    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
                )
                .unwrap(),
                halted: 1,
                exit_code: 42,
                config_tags: vec![],
            },
            expected_digest:
                "40400183813884747956300889570234739091911790924111649960538043847858548402419",
        },
        GoldenVector {
            name: "state_with_config_tags_empty",
            program_hash: "cafebabecafebabecafebabecafebabecafebabecafebabecafebabecafebabe",
            state: VMStateV1 {
                pc: 4096,
                regs: [0; 32],
                step_counter: 100,
                rw_mem_root: Bytes32::zero(),
                io_root: Bytes32::zero(),
                halted: 0,
                exit_code: 0,
                config_tags: vec![],
            },
            expected_digest:
                "51269420250097274214666708236162143841421999722140888943312460699788950625363",
        },
    ]
}

/// Test that Lean oracle is available and produces expected output.
#[test]
fn test_lean_oracle_available() {
    skip_if_no_lean!();

    let lean_path = lean_oracle_path().unwrap();
    println!("Using Lean oracle at: {}", lean_path);

    let harness = DiffTestHarness::new(Some(&lean_path));
    assert!(
        harness.has_lean(),
        "Lean oracle should be available at {}",
        lean_path
    );
}

/// Test that Rust and Lean produce identical digests for golden vectors.
#[test]
fn test_lean_vs_rust_golden_vectors() {
    skip_if_no_lean!();

    let lean_path = lean_oracle_path().unwrap();
    let harness = DiffTestHarness::new(Some(&lean_path));

    if !harness.has_lean() {
        panic!(
            "Lean oracle not available at {}, but LEAN_ORACLE_PATH was set",
            lean_path
        );
    }

    for vector in golden_vectors() {
        println!("Testing: {}", vector.name);

        let program_hash = Bytes32::from_hex(vector.program_hash)
            .unwrap_or_else(|_| panic!("Invalid program_hash for {}", vector.name));

        let result = harness.compare_digest(vector.name, &program_hash, &vector.state);
        assert!(
            result.is_ok(),
            "Test {} failed with error: {:?}",
            vector.name,
            result.err()
        );

        let diff_result = result.unwrap();
        assert!(
            diff_result.is_match(),
            "Test {} had Rust/Lean mismatch: {:?}",
            vector.name,
            diff_result
        );
    }
}

/// Test batch comparison of all golden vectors.
#[test]
fn test_lean_batch_comparison() {
    skip_if_no_lean!();

    let lean_path = lean_oracle_path().unwrap();
    let harness = DiffTestHarness::new(Some(&lean_path));

    if !harness.has_lean() {
        panic!("Lean oracle not available");
    }

    let vectors = golden_vectors();
    let program_hashes: Vec<Bytes32> = vectors
        .iter()
        .map(|v| Bytes32::from_hex(v.program_hash).unwrap())
        .collect();

    let tests: Vec<(&str, &Bytes32, &VMStateV1)> = vectors
        .iter()
        .zip(program_hashes.iter())
        .map(|(v, ph)| (v.name, ph, &v.state))
        .collect();

    let results = harness.run_batch(tests.into_iter());

    println!("Batch results: {}", results.summary());

    assert_eq!(
        results.failed, 0,
        "Expected 0 failures, got {}: {:?}",
        results.failed, results.failures
    );
    assert_eq!(
        results.errors, 0,
        "Expected 0 errors, got {}: {:?}",
        results.errors, results.error_details
    );
    assert_eq!(
        results.passed, 4,
        "Expected 4 passed, got {}",
        results.passed
    );
}

/// Test error case: invalid x0 register.
#[test]
fn test_lean_error_invalid_x0() {
    skip_if_no_lean!();

    let lean_path = lean_oracle_path().unwrap();
    let harness = DiffTestHarness::new(Some(&lean_path));

    if !harness.has_lean() {
        panic!("Lean oracle not available");
    }

    let mut invalid_state = VMStateV1::default();
    invalid_state.regs[0] = 1; // x0 must be 0

    let result = harness.compare_digest("invalid_x0", &Bytes32::zero(), &invalid_state);
    assert!(result.is_ok());

    let diff_result = result.unwrap();

    // Both Rust and Lean should return an error for invalid x0
    assert!(
        diff_result.is_match(),
        "Rust and Lean should agree on x0 validation error: {:?}",
        diff_result
    );
}

/// Test error case: invalid halted flag.
#[test]
fn test_lean_error_invalid_halted() {
    skip_if_no_lean!();

    let lean_path = lean_oracle_path().unwrap();
    let harness = DiffTestHarness::new(Some(&lean_path));

    if !harness.has_lean() {
        panic!("Lean oracle not available");
    }

    let mut invalid_state = VMStateV1::default();
    invalid_state.halted = 2; // halted must be 0 or 1

    let result = harness.compare_digest("invalid_halted", &Bytes32::zero(), &invalid_state);
    assert!(result.is_ok());

    let diff_result = result.unwrap();

    // Both Rust and Lean should return an error for invalid halted
    assert!(
        diff_result.is_match(),
        "Rust and Lean should agree on halted validation error: {:?}",
        diff_result
    );
}
