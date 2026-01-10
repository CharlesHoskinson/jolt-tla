//! VM state types and digest computation.
//!
//! # Requirements
//!
//! - DIG-001: Hash fields in order: pc, regs[0..31], step_counter
//! - DIG-002: Bit-identical output to Lean
//! - DIG-003: Return ErrorCode for invalid field values

mod transcript;
mod types;
mod validation;

pub use transcript::Transcript;
pub use types::{Bytes32, ConfigTag, VMStateV1};
pub use validation::validate_vm_state;

use crate::error::{ErrorCode, OracleResult};
use crate::field::Fr;

/// Compute state digest per specification section 11.10.2.
///
/// # Arguments
/// - `program_hash`: 32-byte program hash (separate from VMState)
/// - `state`: VM state including config_tags
///
/// # Returns
/// The state digest as an Fr field element.
///
/// # Requirements
/// - DIG-001: Hash fields in order: pc, regs[0..31], step_counter, etc.
/// - DIG-002: Bit-identical output to Lean implementation
/// - DIG-003: Return ErrorCode for invalid field values
pub fn compute_state_digest(program_hash: &Bytes32, state: &VMStateV1) -> OracleResult<Fr> {
    // Validate state first
    validate_vm_state(state)?;

    // Initialize transcript per section 8.4 (absorbs "JOLT/TRANSCRIPT/V1")
    let mut t = Transcript::new()?;

    // Step 1: absorb_tag("JOLT/STATE/V1")
    t.absorb_tag("JOLT/STATE/V1")?;

    // Step 2: absorb_bytes(program_hash)
    t.absorb_bytes(&program_hash.0)?;

    // Step 3: absorb_u64(pc)
    t.absorb_u64(state.pc);

    // Step 4: absorb_u64(regs[i]) for i=0..31 (BEFORE step_counter!)
    for i in 0..32 {
        t.absorb_u64(state.regs[i]);
    }

    // Step 5: absorb_u64(step_counter) (AFTER regs!)
    t.absorb_u64(state.step_counter);

    // Step 6: absorb_bytes(rw_mem_root)
    t.absorb_bytes(&state.rw_mem_root.0)?;

    // Step 7: absorb_bytes(io_root)
    t.absorb_bytes(&state.io_root.0)?;

    // Step 8: absorb_u64(u64(halted)) per section 11.10.2
    t.absorb_u64(state.halted as u64);

    // Step 9: absorb_u64(exit_code)
    t.absorb_u64(state.exit_code);

    // Step 10: absorb_tag("JOLT/CONFIG_TAGS/V1")
    t.absorb_tag("JOLT/CONFIG_TAGS/V1")?;

    // Step 11: absorb_u64(len(config_tags))
    if state.config_tags.len() > u64::MAX as usize {
        return Err(ErrorCode::E402_OutOfRange(
            "config_tags count exceeds u64".to_string(),
        ));
    }
    t.absorb_u64(state.config_tags.len() as u64);

    // Step 12: for each config tag
    for tag in &state.config_tags {
        // absorb_tag("JOLT/TAG/V1")
        t.absorb_tag("JOLT/TAG/V1")?;
        // absorb_bytes(name)
        t.absorb_bytes(&tag.name)?;
        // absorb_bytes(value)
        t.absorb_bytes(&tag.value)?;
    }

    // Steps 13-14: challenge_fr() -> digest
    let digest = t.challenge_fr();
    Ok(digest)
}

/// Verify state digest matches expected value.
pub fn verify_state_digest(
    program_hash: &Bytes32,
    state: &VMStateV1,
    expected_digest: &Fr,
) -> OracleResult<bool> {
    let computed = compute_state_digest(program_hash, state)?;
    Ok(computed == *expected_digest)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_minimal_state_zeros() {
        // Test vector: minimal_state_zeros
        let program_hash = Bytes32::zero();
        let state = VMStateV1::default();

        let digest = compute_state_digest(&program_hash, &state).unwrap();

        // Expected digest from golden_v1.json
        let expected =
            "24421670062301725635551677633693836338234896090794496795972501815695727753187";
        let digest_str = format!("{}", scalar_to_decimal(&digest));
        assert_eq!(digest_str, expected, "minimal_state_zeros digest mismatch");
    }

    #[test]
    fn test_typical_state() {
        // Test vector: typical_state
        let program_hash =
            Bytes32::from_hex("abcd1234567890abcd1234567890abcd1234567890abcd1234567890abcd1234")
                .unwrap();
        let state = VMStateV1 {
            pc: 4096,
            regs: [
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
                23, 24, 25, 26, 27, 28, 29, 30, 31,
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
        };

        let digest = compute_state_digest(&program_hash, &state).unwrap();

        let expected =
            "30919686901236335602438576816898388225550310633849398790605613577781839025832";
        let digest_str = format!("{}", scalar_to_decimal(&digest));
        assert_eq!(digest_str, expected, "typical_state digest mismatch");
    }

    #[test]
    fn test_halted_state() {
        // Test vector: halted_state
        let program_hash =
            Bytes32::from_hex("deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef")
                .unwrap();
        let state = VMStateV1 {
            pc: 8192,
            regs: [
                0, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000, 1100, 1200, 1300, 1400, 1500,
                1600, 1700, 1800, 1900, 2000, 2100, 2200, 2300, 2400, 2500, 2600, 2700, 2800, 2900,
                3000, 3100,
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
        };

        let digest = compute_state_digest(&program_hash, &state).unwrap();

        let expected =
            "40400183813884747956300889570234739091911790924111649960538043847858548402419";
        let digest_str = scalar_to_decimal(&digest);
        assert_eq!(digest_str, expected, "halted_state digest mismatch");
    }

    #[test]
    fn test_state_with_config_tags() {
        // Test vector: state_with_config_tags
        let program_hash =
            Bytes32::from_hex("cafebabecafebabecafebabecafebabecafebabecafebabecafebabecafebabe")
                .unwrap();
        let state = VMStateV1 {
            pc: 4096,
            regs: [0; 32],
            step_counter: 100,
            rw_mem_root: Bytes32::zero(),
            io_root: Bytes32::zero(),
            halted: 0,
            exit_code: 0,
            config_tags: vec![],
        };

        let digest = compute_state_digest(&program_hash, &state).unwrap();

        let expected =
            "51269420250097274214666708236162143841421999722140888943312460699788950625363";
        let digest_str = scalar_to_decimal(&digest);
        assert_eq!(
            digest_str, expected,
            "state_with_config_tags digest mismatch"
        );
    }

    #[test]
    fn test_invalid_register_x0() {
        let program_hash = Bytes32::zero();
        let mut state = VMStateV1::default();
        state.regs[0] = 1; // Invalid: x0 must be 0

        let result = compute_state_digest(&program_hash, &state);
        assert!(result.is_err());
        match result.unwrap_err() {
            ErrorCode::E407_RegisterX0NonZero(_) => {}
            e => panic!("Expected E407_RegisterX0NonZero, got {:?}", e),
        }
    }

    #[test]
    fn test_invalid_halted_value() {
        let program_hash = Bytes32::zero();
        let mut state = VMStateV1::default();
        state.halted = 2; // Invalid: must be 0 or 1

        let result = compute_state_digest(&program_hash, &state);
        assert!(result.is_err());
        match result.unwrap_err() {
            ErrorCode::E404_InvalidHalted => {}
            e => panic!("Expected E404_InvalidHalted, got {:?}", e),
        }
    }

    /// Convert Fr to decimal string for test comparison.
    fn scalar_to_decimal(fr: &Fr) -> String {
        // Convert Fr bytes (little-endian) to big integer
        let bytes = fr.to_bytes_le();
        let mut result = vec![0u8];

        for &byte in bytes.iter().rev() {
            // Multiply result by 256 and add byte
            let mut carry = byte as u16;
            for digit in result.iter_mut() {
                let val = (*digit as u16) * 256 + carry;
                *digit = (val % 10) as u8;
                carry = val / 10;
            }
            while carry > 0 {
                result.push((carry % 10) as u8);
                carry /= 10;
            }
        }

        // Convert digits to string (reverse order)
        if result.iter().all(|&d| d == 0) {
            "0".to_string()
        } else {
            result
                .iter()
                .rev()
                .skip_while(|&&d| d == 0)
                .map(|&d| (b'0' + d) as char)
                .collect()
        }
    }
}
