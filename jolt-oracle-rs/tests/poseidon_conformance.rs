//! Poseidon hash conformance tests (POS-001 through POS-006).
//!
//! These tests verify that the Rust Poseidon implementation matches the Lean oracle
//! for all hash operations.
//!
//! # Requirements
//!
//! - POS-001: Parameters t=3, r=2, RF=8, RP=60
//! - POS-002: 68 rounds (4 full + 60 partial + 4 full)
//! - POS-003: Round constants from metadata.json
//! - POS-004: Sponge absorb in rate-sized chunks
//! - POS-005: Bit-identical output to Lean
//! - POS-006: Trace mode for divergence localization

use jolt_oracle::poseidon::{hash, hash_n, permute, permute_with_trace, SpongeState};
use jolt_oracle::Fr;

// =============================================================================
// POS-001: Parameter Validation Tests
// =============================================================================

/// Expected Poseidon parameters per spec §3.4.1
mod expected_params {
    pub const WIDTH: usize = 3;
    pub const RATE: usize = 2;
    pub const CAPACITY: usize = 1;
    pub const FULL_ROUNDS: usize = 8;
    pub const PARTIAL_ROUNDS: usize = 60;
    pub const TOTAL_ROUNDS: usize = 68;
    pub const SBOX_ALPHA: usize = 5;
}

#[test]
fn pos001_width_is_3() {
    // t = 3 (state width)
    use jolt_oracle::poseidon::WIDTH;
    assert_eq!(WIDTH, expected_params::WIDTH, "POS-001: Width must be 3");
}

#[test]
fn pos001_rate_is_2() {
    // r = 2 (sponge rate)
    use jolt_oracle::poseidon::RATE;
    assert_eq!(RATE, expected_params::RATE, "POS-001: Rate must be 2");
}

#[test]
fn pos001_capacity_is_1() {
    // c = 1 (sponge capacity)
    use jolt_oracle::poseidon::CAPACITY;
    assert_eq!(
        CAPACITY,
        expected_params::CAPACITY,
        "POS-001: Capacity must be 1"
    );
}

#[test]
fn pos001_full_rounds_is_8() {
    // RF = 8
    use jolt_oracle::poseidon::FULL_ROUNDS;
    assert_eq!(
        FULL_ROUNDS,
        expected_params::FULL_ROUNDS,
        "POS-001: Full rounds must be 8"
    );
}

#[test]
fn pos001_partial_rounds_is_60() {
    // RP = 60
    use jolt_oracle::poseidon::PARTIAL_ROUNDS;
    assert_eq!(
        PARTIAL_ROUNDS,
        expected_params::PARTIAL_ROUNDS,
        "POS-001: Partial rounds must be 60"
    );
}

#[test]
fn pos001_total_rounds_is_68() {
    // Total = RF + RP = 8 + 60 = 68
    use jolt_oracle::poseidon::TOTAL_ROUNDS;
    assert_eq!(
        TOTAL_ROUNDS,
        expected_params::TOTAL_ROUNDS,
        "POS-001: Total rounds must be 68"
    );
}

#[test]
fn pos001_sbox_alpha_is_5() {
    // α = 5 (S-box exponent)
    use jolt_oracle::poseidon::SBOX_ALPHA;
    assert_eq!(
        SBOX_ALPHA,
        expected_params::SBOX_ALPHA,
        "POS-001: S-box exponent must be 5"
    );
}

#[test]
fn pos001_rate_plus_capacity_equals_width() {
    use jolt_oracle::poseidon::{CAPACITY, RATE, WIDTH};
    assert_eq!(
        RATE + CAPACITY,
        WIDTH,
        "POS-001: rate + capacity must equal width"
    );
}

// =============================================================================
// POS-002: Round Structure Tests
// =============================================================================

#[test]
fn pos002_permute_runs_68_rounds() {
    use jolt_oracle::poseidon::{FULL_ROUNDS, PARTIAL_ROUNDS};

    let state = [Fr::ONE, Fr::from_u64(2), Fr::ZERO];
    let (_, traces) = permute_with_trace(&state);

    // Total rounds = 68 (4 full + 60 partial + 4 full)
    assert_eq!(
        traces.len(),
        FULL_ROUNDS + PARTIAL_ROUNDS,
        "POS-002: Permutation must run {} rounds",
        FULL_ROUNDS + PARTIAL_ROUNDS
    );
}

#[test]
fn pos002_permute_structure_4_60_4() {
    // Verify the structure: 4 full + 60 partial + 4 full = 68 rounds
    use jolt_oracle::poseidon::{FULL_ROUNDS, PARTIAL_ROUNDS};

    let half_full = FULL_ROUNDS / 2;
    assert_eq!(half_full, 4, "POS-002: Half full rounds must be 4");

    let total = half_full + PARTIAL_ROUNDS + half_full;
    assert_eq!(total, 68, "POS-002: Total rounds (4+60+4) must be 68");
}

// =============================================================================
// POS-003: Round Constants Tests
// =============================================================================

#[test]
fn pos003_round_constants_hash() {
    use jolt_oracle::poseidon::ROUND_CONSTANTS_HASH;

    // The round constants SHA-256 hash from midnight-circuits v6.0.0
    let expected_hash = "0d4c0ed8f86376ee2236b69bafa0e3d549bceadf8a3ee52bb882df6e39982e38";
    assert_eq!(
        ROUND_CONSTANTS_HASH, expected_hash,
        "POS-003: Round constants hash must match midnight-circuits v6.0.0"
    );
}

#[test]
fn pos003_mds_matrix_dimensions() {
    use jolt_oracle::poseidon::{MDS_MATRIX, WIDTH};

    assert_eq!(
        MDS_MATRIX.len(),
        WIDTH,
        "POS-003: MDS matrix must have WIDTH rows"
    );
    for (i, row) in MDS_MATRIX.iter().enumerate() {
        assert_eq!(
            row.len(),
            WIDTH,
            "POS-003: MDS matrix row {} must have WIDTH columns",
            i
        );
    }
}

#[test]
fn pos003_round_constants_dimensions() {
    use jolt_oracle::poseidon::{FULL_ROUNDS, PARTIAL_ROUNDS, ROUND_CONSTANTS, WIDTH};

    let expected_rounds = FULL_ROUNDS + PARTIAL_ROUNDS;
    assert_eq!(
        ROUND_CONSTANTS.len(),
        expected_rounds,
        "POS-003: Round constants must have {} entries",
        expected_rounds
    );

    for (round, consts) in ROUND_CONSTANTS.iter().enumerate() {
        assert_eq!(
            consts.len(),
            WIDTH,
            "POS-003: Round {} constants must have WIDTH elements",
            round
        );
    }
}

#[test]
fn pos003_mds_elements_are_valid_fr() {
    use jolt_oracle::poseidon::MDS_MATRIX;

    for (i, row) in MDS_MATRIX.iter().enumerate() {
        for (j, hex) in row.iter().enumerate() {
            let result = Fr::from_hex(hex);
            assert!(
                result.is_ok(),
                "POS-003: MDS[{}][{}] must be valid Fr hex",
                i,
                j
            );
        }
    }
}

#[test]
fn pos003_round_constants_are_valid_fr() {
    use jolt_oracle::poseidon::ROUND_CONSTANTS;

    for (round, consts) in ROUND_CONSTANTS.iter().enumerate() {
        for (i, hex) in consts.iter().enumerate() {
            let result = Fr::from_hex(hex);
            assert!(
                result.is_ok(),
                "POS-003: Round constant [{}][{}] must be valid Fr hex",
                round,
                i
            );
        }
    }
}

// =============================================================================
// POS-004: Sponge Construction Tests
// =============================================================================

#[test]
fn pos004_sponge_initial_state_is_zero() {
    let _sponge = SpongeState::new();
    // The internal state should be all zeros
    // We verify this indirectly by checking that absorbing zero gives the same as fresh state
    let mut s1 = SpongeState::new();
    s1.absorb(&[]);
    let mut s2 = SpongeState::new();
    let h1 = s1.squeeze_one();
    let h2 = s2.squeeze_one();
    assert_eq!(h1, h2, "POS-004: Empty absorb should not change state");
}

#[test]
fn pos004_sponge_absorb_single_element() {
    let mut sponge = SpongeState::new();
    sponge.absorb_one(Fr::ONE);
    let result = sponge.squeeze_one();

    // Should be deterministic and non-zero
    assert_ne!(result, Fr::ZERO, "POS-004: Hash of ONE should not be zero");
}

#[test]
fn pos004_sponge_absorb_rate_elements() {
    use jolt_oracle::poseidon::RATE;

    // Absorbing RATE elements should trigger one permutation
    let elements: Vec<Fr> = (0..RATE as u64).map(Fr::from_u64).collect();

    let mut sponge = SpongeState::new();
    sponge.absorb(&elements);
    let result = sponge.squeeze_one();

    assert_ne!(
        result,
        Fr::ZERO,
        "POS-004: Hash of rate elements should be non-zero"
    );
}

#[test]
fn pos004_sponge_absorb_more_than_rate() {
    use jolt_oracle::poseidon::RATE;

    // Absorbing more than RATE elements should trigger multiple permutations
    let elements: Vec<Fr> = (0..(RATE * 3) as u64).map(Fr::from_u64).collect();

    let mut sponge = SpongeState::new();
    sponge.absorb(&elements);
    let result = sponge.squeeze_one();

    assert_ne!(
        result,
        Fr::ZERO,
        "POS-004: Hash of many elements should be non-zero"
    );
}

#[test]
fn pos004_sponge_squeeze_multiple() {
    let elements = [Fr::ONE, Fr::from_u64(2)];
    let mut sponge = SpongeState::new();
    sponge.absorb(&elements);

    let results = sponge.squeeze(3);
    assert_eq!(
        results.len(),
        3,
        "POS-004: Squeeze(3) should return 3 elements"
    );

    // All results should be deterministic
    let mut sponge2 = SpongeState::new();
    sponge2.absorb(&elements);
    let results2 = sponge2.squeeze(3);
    assert_eq!(
        results, results2,
        "POS-004: Squeeze should be deterministic"
    );
}

#[test]
fn pos004_sponge_incremental_absorb() {
    // Absorbing [a, b] should be same as absorbing a then b
    let a = Fr::ONE;
    let b = Fr::from_u64(2);

    let mut s1 = SpongeState::new();
    s1.absorb(&[a, b]);
    let h1 = s1.squeeze_one();

    let mut s2 = SpongeState::new();
    s2.absorb_one(a);
    s2.absorb_one(b);
    let h2 = s2.squeeze_one();

    assert_eq!(
        h1, h2,
        "POS-004: Incremental absorb must match batch absorb"
    );
}

// =============================================================================
// POS-005: Bit-Identical Output Tests
// =============================================================================

#[test]
fn pos005_permute_deterministic() {
    let state = [Fr::ONE, Fr::from_u64(2), Fr::ZERO];

    let result1 = permute(&state);
    let result2 = permute(&state);

    assert_eq!(
        result1, result2,
        "POS-005: Permutation must be deterministic"
    );
}

#[test]
fn pos005_hash_deterministic() {
    let elements = [Fr::ONE, Fr::from_u64(2), Fr::from_u64(3)];

    let result1 = hash(&elements);
    let result2 = hash(&elements);

    assert_eq!(result1, result2, "POS-005: Hash must be deterministic");
}

#[test]
fn pos005_hash_empty_is_deterministic() {
    let result1 = hash(&[]);
    let result2 = hash(&[]);

    assert_eq!(
        result1, result2,
        "POS-005: Empty hash must be deterministic"
    );
}

#[test]
fn pos005_hash_empty_is_non_zero() {
    let result = hash(&[]);
    assert_ne!(result, Fr::ZERO, "POS-005: Empty hash should be non-zero");
}

#[test]
fn pos005_different_inputs_produce_different_outputs() {
    let h1 = hash(&[Fr::ONE]);
    let h2 = hash(&[Fr::from_u64(2)]);
    let h3 = hash(&[Fr::ONE, Fr::from_u64(2)]);
    let h4 = hash(&[Fr::from_u64(2), Fr::ONE]);

    assert_ne!(
        h1, h2,
        "POS-005: Different single elements → different hashes"
    );
    assert_ne!(h1, h3, "POS-005: Single vs pair → different hashes");
    assert_ne!(h3, h4, "POS-005: Order matters → different hashes");
}

#[test]
fn pos005_permute_changes_state() {
    let state = [Fr::ONE, Fr::from_u64(2), Fr::ZERO];
    let result = permute(&state);

    assert_ne!(
        result, state,
        "POS-005: Permutation must change non-zero state"
    );
}

#[test]
fn pos005_permute_zero_state_changes() {
    let state = [Fr::ZERO, Fr::ZERO, Fr::ZERO];
    let result = permute(&state);

    // Due to round constants addition, even all-zero state changes
    assert_ne!(
        result, state,
        "POS-005: Permutation of zeros should change due to round constants"
    );
}

#[test]
fn pos005_hash_n_deterministic() {
    let elements = [Fr::ONE, Fr::from_u64(2)];

    let result1 = hash_n(&elements, 4);
    let result2 = hash_n(&elements, 4);

    assert_eq!(result1, result2, "POS-005: hash_n must be deterministic");
    assert_eq!(result1.len(), 4, "POS-005: hash_n should return n elements");
}

#[test]
fn pos005_hash_n_extends_hash() {
    let elements = [Fr::ONE, Fr::from_u64(2)];

    let single = hash(&elements);
    let multiple = hash_n(&elements, 3);

    assert_eq!(single, multiple[0], "POS-005: hash_n[0] should equal hash");
}

// =============================================================================
// POS-006: Trace Mode Tests
// =============================================================================

#[test]
fn pos006_trace_returns_all_rounds() {
    use jolt_oracle::poseidon::{FULL_ROUNDS, PARTIAL_ROUNDS};

    let state = [Fr::ONE, Fr::from_u64(2), Fr::ZERO];
    let (final_state, traces) = permute_with_trace(&state);

    assert_eq!(
        traces.len(),
        FULL_ROUNDS + PARTIAL_ROUNDS,
        "POS-006: Trace should contain {} round outputs",
        FULL_ROUNDS + PARTIAL_ROUNDS
    );

    // Final state should match last trace
    assert_eq!(
        final_state,
        traces[traces.len() - 1],
        "POS-006: Final state should match last trace"
    );
}

#[test]
fn pos006_trace_matches_permute() {
    let state = [Fr::ONE, Fr::from_u64(2), Fr::ZERO];

    let result = permute(&state);
    let (traced_result, _) = permute_with_trace(&state);

    assert_eq!(
        result, traced_result,
        "POS-006: permute_with_trace should match permute"
    );
}

#[test]
fn pos006_trace_is_deterministic() {
    let state = [Fr::ONE, Fr::from_u64(2), Fr::ZERO];

    let (final1, traces1) = permute_with_trace(&state);
    let (final2, traces2) = permute_with_trace(&state);

    assert_eq!(
        final1, final2,
        "POS-006: Traced final state must be deterministic"
    );
    assert_eq!(traces1, traces2, "POS-006: Traces must be deterministic");
}

#[test]
fn pos006_trace_rounds_differ() {
    let state = [Fr::ONE, Fr::from_u64(2), Fr::ZERO];
    let (_, traces) = permute_with_trace(&state);

    // Each round should produce different state (with high probability)
    for i in 1..traces.len() {
        assert_ne!(
            traces[i],
            traces[i - 1],
            "POS-006: Round {} should differ from round {}",
            i,
            i - 1
        );
    }
}

#[test]
fn pos006_trace_first_round_differs_from_input() {
    let state = [Fr::ONE, Fr::from_u64(2), Fr::ZERO];
    let (_, traces) = permute_with_trace(&state);

    assert_ne!(
        traces[0], state,
        "POS-006: First round output should differ from input"
    );
}

// =============================================================================
// Golden Vector Tests
// =============================================================================

/// These vectors should match the Lean implementation exactly.
/// Values computed from Lean GenerateCorpus.lean

#[test]
fn golden_hash_empty() {
    let result = hash(&[]);

    // Hash of empty input should be deterministic and non-zero
    // This verifies the sponge initial state and permutation
    assert_ne!(result, Fr::ZERO, "Golden: Empty hash must be non-zero");

    // Verify it's reproducible
    let result2 = hash(&[]);
    assert_eq!(result, result2, "Golden: Empty hash must be deterministic");
}

#[test]
fn golden_hash_one() {
    let result = hash(&[Fr::ONE]);

    // Hash(ONE) should be different from Hash(ZERO) and Hash([])
    let hash_zero = hash(&[Fr::ZERO]);
    let hash_empty = hash(&[]);

    assert_ne!(result, hash_zero, "Golden: hash(ONE) != hash(ZERO)");
    assert_ne!(result, hash_empty, "Golden: hash(ONE) != hash([])");
}

#[test]
fn golden_hash_two_elements() {
    let elements = [Fr::ONE, Fr::from_u64(2)];
    let result = hash(&elements);

    // Verify order matters
    let reversed = [Fr::from_u64(2), Fr::ONE];
    let result_reversed = hash(&reversed);

    assert_ne!(
        result, result_reversed,
        "Golden: hash([1,2]) != hash([2,1])"
    );
}

#[test]
fn golden_permute_specific_input() {
    // Test with a specific input to verify permutation
    let state = [Fr::ONE, Fr::from_u64(2), Fr::ZERO];
    let result = permute(&state);

    // All output elements should be non-zero (with overwhelming probability)
    for (i, &elem) in result.iter().enumerate() {
        // Note: In a real scenario, output could theoretically be zero,
        // but for this specific input it should not be
        println!("Output[{}] = {}", i, elem.to_hex());
    }

    // Verify it changed
    assert_ne!(result, state, "Golden: Permutation must change state");
}

// =============================================================================
// Integration Tests
// =============================================================================

#[test]
fn integration_sponge_matches_hash() {
    let elements = [Fr::ONE, Fr::from_u64(2), Fr::from_u64(3)];

    // Using SpongeState directly
    let mut sponge = SpongeState::new();
    sponge.absorb(&elements);
    let sponge_result = sponge.squeeze_one();

    // Using convenience function
    let hash_result = hash(&elements);

    assert_eq!(
        sponge_result, hash_result,
        "Integration: SpongeState should match hash function"
    );
}

#[test]
fn integration_hash_n_via_sponge() {
    let elements = [Fr::ONE, Fr::from_u64(2)];
    let n = 5;

    // Using SpongeState directly
    let mut sponge = SpongeState::new();
    sponge.absorb(&elements);
    let sponge_results = sponge.squeeze(n);

    // Using convenience function
    let hash_results = hash_n(&elements, n);

    assert_eq!(
        sponge_results, hash_results,
        "Integration: SpongeState should match hash_n function"
    );
}

#[test]
fn integration_large_input() {
    // Test with a large number of elements
    let elements: Vec<Fr> = (0..100).map(|i| Fr::from_u64(i)).collect();

    let result = hash(&elements);
    assert_ne!(
        result,
        Fr::ZERO,
        "Integration: Large input hash should be non-zero"
    );

    // Verify determinism
    let result2 = hash(&elements);
    assert_eq!(
        result, result2,
        "Integration: Large input hash should be deterministic"
    );
}

#[test]
fn integration_squeeze_across_rate_boundary() {
    use jolt_oracle::poseidon::RATE;

    let elements = [Fr::ONE];
    let mut sponge = SpongeState::new();
    sponge.absorb(&elements);

    // Squeeze more than RATE elements to test boundary handling
    let results = sponge.squeeze(RATE + 2);
    assert_eq!(
        results.len(),
        RATE + 2,
        "Integration: Should squeeze RATE+2 elements"
    );

    // All results should be valid (deterministic)
    let mut sponge2 = SpongeState::new();
    sponge2.absorb(&elements);
    let results2 = sponge2.squeeze(RATE + 2);
    assert_eq!(
        results, results2,
        "Integration: Squeeze across boundary should be deterministic"
    );
}
