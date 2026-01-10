//! Conformance tests using the differential test harness.
//!
//! These tests verify that the Rust implementation produces identical output
//! to the Lean oracle for all golden test vectors.

use jolt_oracle::conformance::{DiffTestHarness, OracleOutput};
use jolt_oracle::state::{Bytes32, ConfigTag, VMStateV1};

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

#[test]
fn test_rust_only_golden_vectors() {
    let harness = DiffTestHarness::rust_only();

    for vector in golden_vectors() {
        let program_hash = Bytes32::from_hex(vector.program_hash)
            .unwrap_or_else(|_| panic!("Invalid program_hash for {}", vector.name));

        let result = harness.run_rust_digest(&program_hash, &vector.state);
        assert!(
            result.is_ok(),
            "Test {} failed with error: {:?}",
            vector.name,
            result.err()
        );

        let output = result.unwrap();
        match output {
            OracleOutput::Ok(digest) => {
                assert_eq!(
                    digest, vector.expected_digest,
                    "Digest mismatch for test {}: got {}, expected {}",
                    vector.name, digest, vector.expected_digest
                );
            }
            OracleOutput::Err(e) => {
                panic!("Test {} returned error: {}", vector.name, e);
            }
        }
    }
}

#[test]
fn test_rust_only_batch_golden_vectors() {
    let harness = DiffTestHarness::rust_only();

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

    // When Lean is not available, all tests are skipped
    assert_eq!(results.skipped, 4, "Expected 4 skipped tests without Lean");
    assert_eq!(results.failed, 0, "No tests should fail");
    assert_eq!(results.errors, 0, "No tests should error");
}

#[test]
fn test_invalid_state_error_codes() {
    let harness = DiffTestHarness::rust_only();

    // Test E407: Register x0 non-zero
    let mut invalid_x0_state = VMStateV1::default();
    invalid_x0_state.regs[0] = 1;

    let result = harness.run_rust_digest(&Bytes32::zero(), &invalid_x0_state);
    assert!(result.is_ok());
    let output = result.unwrap();
    assert!(output.is_err(), "Expected error for x0 != 0");
    assert!(
        output.as_string().contains("E407"),
        "Expected E407 error code, got: {}",
        output.as_string()
    );

    // Test E404: Invalid halted flag
    let mut invalid_halted_state = VMStateV1::default();
    invalid_halted_state.halted = 2;

    let result = harness.run_rust_digest(&Bytes32::zero(), &invalid_halted_state);
    assert!(result.is_ok());
    let output = result.unwrap();
    assert!(output.is_err(), "Expected error for halted = 2");
    assert!(
        output.as_string().contains("E404"),
        "Expected E404 error code, got: {}",
        output.as_string()
    );
}

#[test]
fn test_config_tags_with_harness() {
    let harness = DiffTestHarness::rust_only();

    let state = VMStateV1 {
        pc: 0,
        regs: [0; 32],
        step_counter: 0,
        rw_mem_root: Bytes32::zero(),
        io_root: Bytes32::zero(),
        halted: 0,
        exit_code: 0,
        config_tags: vec![
            ConfigTag::new(b"aaa".to_vec(), b"value1".to_vec()),
            ConfigTag::new(b"bbb".to_vec(), b"value2".to_vec()),
        ],
    };

    let result = harness.run_rust_digest(&Bytes32::zero(), &state);
    assert!(
        result.is_ok(),
        "Config tags test failed: {:?}",
        result.err()
    );

    let output = result.unwrap();
    assert!(
        output.is_ok(),
        "Expected successful digest with config tags"
    );
}

#[test]
fn test_diff_result_methods() {
    use jolt_oracle::DiffResult;

    // Test Match variant
    let match_result = DiffResult::Match {
        value: "12345".to_string(),
    };
    assert!(match_result.is_match());
    assert!(!match_result.is_mismatch());
}

#[test]
fn test_harness_has_lean_detection() {
    let rust_only = DiffTestHarness::rust_only();
    assert!(
        !rust_only.has_lean(),
        "rust_only harness should not have Lean"
    );

    // This would require Lean to be installed and built
    // let with_lean = DiffTestHarness::new(Some("path/to/jolt_oracle"));
    // The has_lean() method properly detects Lean availability
}
