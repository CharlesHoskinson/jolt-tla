//! Poseidon permutation implementation.
//!
//! The permutation applies 68 rounds total:
//! - 4 full rounds (all elements get S-box)
//! - 60 partial rounds (only first element gets S-box)
//! - 4 full rounds
//!
//! Each round consists of:
//! 1. S-box (x^5)
//! 2. MDS matrix multiplication
//! 3. Round constant addition

use super::{FULL_ROUNDS, MDS_MATRIX, PARTIAL_ROUNDS, ROUND_CONSTANTS, WIDTH};
use crate::field::Fr;

/// Lazy-initialized parsed constants.
struct ParsedConstants {
    mds: [[Fr; WIDTH]; WIDTH],
    round_constants: Vec<[Fr; WIDTH]>,
}

impl ParsedConstants {
    fn new() -> Self {
        // Parse MDS matrix from hex strings
        let mut mds = [[Fr::ZERO; WIDTH]; WIDTH];
        for i in 0..WIDTH {
            for j in 0..WIDTH {
                mds[i][j] = Fr::from_hex(MDS_MATRIX[i][j])
                    .unwrap_or(Fr::ZERO);
            }
        }

        // Parse round constants from hex strings
        let mut round_constants = Vec::with_capacity(FULL_ROUNDS + PARTIAL_ROUNDS);
        for round in 0..(FULL_ROUNDS + PARTIAL_ROUNDS) {
            let mut constants = [Fr::ZERO; WIDTH];
            for i in 0..WIDTH {
                constants[i] = Fr::from_hex(ROUND_CONSTANTS[round][i])
                    .unwrap_or(Fr::ZERO);
            }
            round_constants.push(constants);
        }

        Self { mds, round_constants }
    }
}

/// Get parsed constants (lazily initialized).
fn get_constants() -> &'static ParsedConstants {
    use std::sync::OnceLock;
    static CONSTANTS: OnceLock<ParsedConstants> = OnceLock::new();
    CONSTANTS.get_or_init(ParsedConstants::new)
}

/// Apply the S-box (x^5) to a field element.
#[inline]
fn sbox(x: Fr) -> Fr {
    x.pow5()
}

/// Apply MDS matrix multiplication: state' = MDS * state
fn apply_mds(state: &[Fr; WIDTH]) -> [Fr; WIDTH] {
    let constants = get_constants();
    let mut result = [Fr::ZERO; WIDTH];

    for i in 0..WIDTH {
        let mut sum = Fr::ZERO;
        for j in 0..WIDTH {
            sum = sum + constants.mds[i][j] * state[j];
        }
        result[i] = sum;
    }

    result
}

/// Add round constants to state.
fn add_round_constants(state: &mut [Fr; WIDTH], round: usize) {
    let constants = get_constants();
    for i in 0..WIDTH {
        state[i] = state[i] + constants.round_constants[round][i];
    }
}

/// Full round: S-box on all elements, then MDS, then add constants.
fn full_round(state: &mut [Fr; WIDTH], round: usize) {
    // S-box on all elements
    for i in 0..WIDTH {
        state[i] = sbox(state[i]);
    }

    // MDS matrix multiplication
    *state = apply_mds(state);

    // Add round constants
    add_round_constants(state, round);
}

/// Partial round: S-box on first element only, then MDS, then add constants.
fn partial_round(state: &mut [Fr; WIDTH], round: usize) {
    // S-box on first element only
    state[0] = sbox(state[0]);

    // MDS matrix multiplication
    *state = apply_mds(state);

    // Add round constants
    add_round_constants(state, round);
}

/// Complete Poseidon permutation.
///
/// Runs:
/// 1. First half of full rounds (RF/2 = 4)
/// 2. All partial rounds (RP = 60)
/// 3. Second half of full rounds (RF/2 = 4)
pub fn permute(state: &[Fr; WIDTH]) -> [Fr; WIDTH] {
    let mut st = *state;
    let half_full = FULL_ROUNDS / 2;
    let mut round = 0;

    // First half of full rounds
    for _ in 0..half_full {
        full_round(&mut st, round);
        round += 1;
    }

    // Partial rounds
    for _ in 0..PARTIAL_ROUNDS {
        partial_round(&mut st, round);
        round += 1;
    }

    // Second half of full rounds
    for _ in 0..half_full {
        full_round(&mut st, round);
        round += 1;
    }

    st
}

/// Poseidon permutation with trace output for debugging (POS-006).
///
/// Returns (final_state, round_traces) where each trace entry contains
/// the state after that round.
pub fn permute_with_trace(state: &[Fr; WIDTH]) -> ([Fr; WIDTH], Vec<[Fr; WIDTH]>) {
    let mut st = *state;
    let half_full = FULL_ROUNDS / 2;
    let mut round = 0;
    let mut traces = Vec::with_capacity(FULL_ROUNDS + PARTIAL_ROUNDS);

    // First half of full rounds
    for _ in 0..half_full {
        full_round(&mut st, round);
        traces.push(st);
        round += 1;
    }

    // Partial rounds
    for _ in 0..PARTIAL_ROUNDS {
        partial_round(&mut st, round);
        traces.push(st);
        round += 1;
    }

    // Second half of full rounds
    for _ in 0..half_full {
        full_round(&mut st, round);
        traces.push(st);
        round += 1;
    }

    (st, traces)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_permute_deterministic() {
        let state = [Fr::ONE, Fr::from_u64(2), Fr::ZERO];
        let result1 = permute(&state);
        let result2 = permute(&state);
        assert_eq!(result1, result2);
    }

    #[test]
    fn test_permute_with_trace_length() {
        let state = [Fr::ONE, Fr::from_u64(2), Fr::ZERO];
        let (_, traces) = permute_with_trace(&state);
        assert_eq!(traces.len(), FULL_ROUNDS + PARTIAL_ROUNDS);
    }
}
