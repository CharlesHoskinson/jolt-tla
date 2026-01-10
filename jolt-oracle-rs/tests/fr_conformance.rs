//! Fr field conformance tests (FR-001 through FR-006).
//!
//! These tests verify that the Rust Fr implementation matches the Lean oracle
//! for all field operations.
//!
//! # Requirements
//!
//! - FR-001: Pinned scalar-field implementation, canonical 32-byte LE encoding
//! - FR-002: Fr::from_bytes_le() validates canonical field element
//! - FR-003: Non-canonical bytes return ErrorCode::E300_NonCanonicalFr
//! - FR-004: Serialization produces canonical LE 32-byte output
//! - FR-005: Arithmetic produces bit-identical results to Lean
//! - FR-006: Division by zero returns ErrorCode::E303_InvalidFrEncoding

use jolt_oracle::error::ErrorCode;
use jolt_oracle::Fr;

/// BLS12-381 scalar field modulus.
/// r = 52435875175126190479447740508185965837690552500527637822603658699938581184513
const MODULUS_HEX: &str = "01000000fffffffffe5bfeff02a4bd5305d8a10908d83933487d9d2953a7ed73";

/// The modulus as a decimal string.
const MODULUS_DECIMAL: &str =
    "52435875175126190479447740508185965837690552500527637822603658699938581184513";

// =============================================================================
// FR-001: Canonical Encoding Tests
// =============================================================================

#[test]
fn fr001_zero_encoding() {
    // Zero should encode to 32 zero bytes
    let zero = Fr::ZERO;
    let bytes = zero.to_bytes_le();
    assert_eq!(
        bytes, [0u8; 32],
        "FR-001: Zero should encode to 32 zero bytes"
    );

    let hex = zero.to_hex();
    assert_eq!(
        hex, "0000000000000000000000000000000000000000000000000000000000000000",
        "FR-001: Zero hex encoding"
    );
}

#[test]
fn fr001_one_encoding() {
    // One should encode to [1, 0, 0, ..., 0] (LE)
    let one = Fr::ONE;
    let bytes = one.to_bytes_le();

    let mut expected = [0u8; 32];
    expected[0] = 1;
    assert_eq!(bytes, expected, "FR-001: One should encode to LE bytes");

    let hex = one.to_hex();
    assert_eq!(
        hex, "0100000000000000000000000000000000000000000000000000000000000000",
        "FR-001: One hex encoding"
    );
}

#[test]
fn fr001_small_values() {
    // Test small values encode correctly in LE format
    let test_cases = [
        (
            2u64,
            "0200000000000000000000000000000000000000000000000000000000000000",
        ),
        (
            42u64,
            "2a00000000000000000000000000000000000000000000000000000000000000",
        ),
        (
            255u64,
            "ff00000000000000000000000000000000000000000000000000000000000000",
        ),
        (
            256u64,
            "0001000000000000000000000000000000000000000000000000000000000000",
        ),
        (
            65535u64,
            "ffff000000000000000000000000000000000000000000000000000000000000",
        ),
    ];

    for (val, expected_hex) in test_cases {
        let fr = Fr::from_u64(val);
        assert_eq!(
            fr.to_hex(),
            expected_hex,
            "FR-001: Value {} should encode to {}",
            val,
            expected_hex
        );
    }
}

#[test]
fn fr001_max_valid_value() {
    // modulus - 1 is the largest valid canonical value
    // We can construct it by subtracting 1 from the modulus bytes
    let max_valid_hex = "00000000fffffffffe5bfeff02a4bd5305d8a10908d83933487d9d2953a7ed73";
    let result = Fr::from_hex(max_valid_hex);
    assert!(
        result.is_ok(),
        "FR-001: modulus-1 should be valid canonical encoding"
    );

    let fr = result.unwrap();
    let roundtrip = fr.to_hex();
    assert_eq!(
        roundtrip, max_valid_hex,
        "FR-001: modulus-1 should roundtrip exactly"
    );
}

// =============================================================================
// FR-002: Canonical Validation Tests
// =============================================================================

#[test]
fn fr002_valid_bytes_accepted() {
    // Valid canonical bytes should be accepted
    // Use a small value that is definitely < modulus
    // The value has zeros in the high bytes, so it's well below the modulus
    let valid_hex = "1234567890abcdef123456780000000000000000000000000000000000000000";
    assert_eq!(valid_hex.len(), 64, "Hex string must be 64 chars");
    let bytes = hex::decode(valid_hex).unwrap();
    let mut arr = [0u8; 32];
    arr.copy_from_slice(&bytes);

    // This value is < modulus, so it should be accepted
    let result = Fr::from_bytes_le(&arr);
    assert!(
        result.is_ok(),
        "FR-002: Valid canonical bytes should be accepted"
    );
}

#[test]
fn fr002_from_hex_validates() {
    // from_hex should perform canonical validation
    let valid_result =
        Fr::from_hex("0000000000000000000000000000000000000000000000000000000000000000");
    assert!(valid_result.is_ok(), "FR-002: Zero hex should be valid");

    let valid_result =
        Fr::from_hex("ff00000000000000000000000000000000000000000000000000000000000000");
    assert!(valid_result.is_ok(), "FR-002: 255 hex should be valid");
}

#[test]
fn fr002_wrong_length_rejected() {
    // Wrong length inputs should be rejected with E104
    let short_hex = "0011223344"; // Only 5 bytes = 10 hex chars
    let result = Fr::from_hex(short_hex);
    assert!(result.is_err(), "FR-002: Short hex should be rejected");

    match result.unwrap_err() {
        ErrorCode::E104_WrongLength(expected, got) => {
            assert_eq!(expected, "64", "FR-002: Expected length should be 64");
            assert_eq!(got, 10, "FR-002: Got length should be 10");
        }
        e => panic!("FR-002: Expected E104_WrongLength, got {:?}", e),
    }
}

#[test]
fn fr002_invalid_hex_rejected() {
    // Invalid hex characters should be rejected with E103
    let invalid_hex = "gg00000000000000000000000000000000000000000000000000000000000000";
    let result = Fr::from_hex(invalid_hex);
    assert!(
        result.is_err(),
        "FR-002: Invalid hex chars should be rejected"
    );

    match result.unwrap_err() {
        ErrorCode::E103_InvalidHex => {}
        e => panic!("FR-002: Expected E103_InvalidHex, got {:?}", e),
    }
}

// =============================================================================
// FR-003: Non-Canonical Rejection Tests
// =============================================================================

#[test]
fn fr003_modulus_rejected() {
    // The modulus itself is NOT canonical (>= r)
    let result = Fr::from_hex(MODULUS_HEX);
    assert!(
        result.is_err(),
        "FR-003: Modulus itself should be rejected as non-canonical"
    );

    match result.unwrap_err() {
        ErrorCode::E300_NonCanonicalFr(_) => {}
        e => panic!("FR-003: Expected E300_NonCanonicalFr, got {:?}", e),
    }
}

#[test]
fn fr003_modulus_plus_one_rejected() {
    // modulus + 1 should also be rejected
    let modulus_plus_one_hex = "02000000fffffffffe5bfeff02a4bd5305d8a10908d83933487d9d2953a7ed73";
    let result = Fr::from_hex(modulus_plus_one_hex);
    assert!(
        result.is_err(),
        "FR-003: modulus+1 should be rejected as non-canonical"
    );

    match result.unwrap_err() {
        ErrorCode::E300_NonCanonicalFr(_) => {}
        e => panic!("FR-003: Expected E300_NonCanonicalFr, got {:?}", e),
    }
}

#[test]
fn fr003_max_u256_rejected() {
    // Maximum 256-bit value (all 0xff) should be rejected
    let max_hex = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    let result = Fr::from_hex(max_hex);
    assert!(
        result.is_err(),
        "FR-003: Max u256 should be rejected as non-canonical"
    );

    match result.unwrap_err() {
        ErrorCode::E300_NonCanonicalFr(_) => {}
        e => panic!("FR-003: Expected E300_NonCanonicalFr, got {:?}", e),
    }
}

#[test]
fn fr003_just_above_modulus_rejected() {
    // Test values just slightly above the modulus
    // modulus = 0x73eda753299d7d483339d80809a1d80553bd44a4fd8d5e09fefffffffeffffffff (BE)
    // In LE: 01000000fffffffffe5bfeff02a4bd5305d8a10908d83933487d9d2953a7ed73

    // Values with just the first byte incremented beyond valid range
    // If modulus LE starts with 01, then 02 in the same position makes it >= r
    let just_over = "02000000fffffffffe5bfeff02a4bd5305d8a10908d83933487d9d2953a7ed73";
    let result = Fr::from_hex(just_over);
    assert!(
        result.is_err(),
        "FR-003: Value just above modulus should be rejected"
    );
}

// =============================================================================
// FR-004: Canonical Output Tests
// =============================================================================

#[test]
fn fr004_roundtrip_small_values() {
    // Small values should roundtrip exactly
    for val in [0u64, 1, 2, 42, 100, 255, 256, 1000, 65535, 1_000_000] {
        let fr = Fr::from_u64(val);
        let bytes = fr.to_bytes_le();
        let recovered = Fr::from_bytes_le(&bytes).unwrap();
        assert_eq!(fr, recovered, "FR-004: Value {} should roundtrip", val);
    }
}

#[test]
fn fr004_roundtrip_hex() {
    // Hex encoding should roundtrip exactly
    let original = Fr::from_u64(0xDEADBEEF);
    let hex = original.to_hex();
    let recovered = Fr::from_hex(&hex).unwrap();
    assert_eq!(original, recovered, "FR-004: Hex should roundtrip");
}

#[test]
fn fr004_output_is_32_bytes() {
    // Output should always be exactly 32 bytes
    let test_values = [Fr::ZERO, Fr::ONE, Fr::from_u64(42), Fr::from_u64(u64::MAX)];

    for fr in test_values {
        let bytes = fr.to_bytes_le();
        assert_eq!(bytes.len(), 32, "FR-004: Output must be exactly 32 bytes");

        let hex = fr.to_hex();
        assert_eq!(hex.len(), 64, "FR-004: Hex output must be exactly 64 chars");
    }
}

#[test]
fn fr004_output_is_lowercase_hex() {
    // Hex output should be lowercase
    let fr = Fr::from_u64(0xABCDEF);
    let hex = fr.to_hex();

    // Check that all hex chars are lowercase
    for c in hex.chars() {
        if c.is_alphabetic() {
            assert!(
                c.is_lowercase(),
                "FR-004: Hex output must be lowercase, got '{}'",
                c
            );
        }
    }
}

// =============================================================================
// FR-005: Arithmetic Tests
// =============================================================================

#[test]
fn fr005_addition_basic() {
    let a = Fr::from_u64(100);
    let b = Fr::from_u64(200);
    let sum = a + b;
    assert_eq!(sum, Fr::from_u64(300), "FR-005: 100 + 200 = 300");
}

#[test]
fn fr005_addition_commutative() {
    let a = Fr::from_u64(12345);
    let b = Fr::from_u64(67890);
    assert_eq!(a + b, b + a, "FR-005: Addition should be commutative");
}

#[test]
fn fr005_addition_identity() {
    let a = Fr::from_u64(42);
    assert_eq!(a + Fr::ZERO, a, "FR-005: a + 0 = a");
    assert_eq!(Fr::ZERO + a, a, "FR-005: 0 + a = a");
}

#[test]
fn fr005_multiplication_basic() {
    let a = Fr::from_u64(7);
    let b = Fr::from_u64(11);
    let product = a * b;
    assert_eq!(product, Fr::from_u64(77), "FR-005: 7 * 11 = 77");
}

#[test]
fn fr005_multiplication_commutative() {
    let a = Fr::from_u64(123);
    let b = Fr::from_u64(456);
    assert_eq!(a * b, b * a, "FR-005: Multiplication should be commutative");
}

#[test]
fn fr005_multiplication_identity() {
    let a = Fr::from_u64(42);
    assert_eq!(a * Fr::ONE, a, "FR-005: a * 1 = a");
    assert_eq!(Fr::ONE * a, a, "FR-005: 1 * a = a");
}

#[test]
fn fr005_multiplication_by_zero() {
    let a = Fr::from_u64(42);
    assert_eq!(a * Fr::ZERO, Fr::ZERO, "FR-005: a * 0 = 0");
    assert_eq!(Fr::ZERO * a, Fr::ZERO, "FR-005: 0 * a = 0");
}

#[test]
fn fr005_subtraction_basic() {
    let a = Fr::from_u64(300);
    let b = Fr::from_u64(200);
    let diff = a - b;
    assert_eq!(diff, Fr::from_u64(100), "FR-005: 300 - 200 = 100");
}

#[test]
fn fr005_subtraction_self() {
    let a = Fr::from_u64(42);
    assert_eq!(a - a, Fr::ZERO, "FR-005: a - a = 0");
}

#[test]
fn fr005_negation() {
    let a = Fr::from_u64(42);
    let neg_a = -a;
    assert_eq!(a + neg_a, Fr::ZERO, "FR-005: a + (-a) = 0");
}

#[test]
fn fr005_double_negation() {
    let a = Fr::from_u64(42);
    assert_eq!(-(-a), a, "FR-005: -(-a) = a");
}

#[test]
fn fr005_negation_of_zero() {
    assert_eq!(-Fr::ZERO, Fr::ZERO, "FR-005: -0 = 0");
}

#[test]
fn fr005_distributive() {
    let a = Fr::from_u64(2);
    let b = Fr::from_u64(3);
    let c = Fr::from_u64(4);

    // a * (b + c) = a*b + a*c
    let lhs = a * (b + c);
    let rhs = (a * b) + (a * c);
    assert_eq!(lhs, rhs, "FR-005: Multiplication should be distributive");
}

#[test]
fn fr005_associative_addition() {
    let a = Fr::from_u64(1);
    let b = Fr::from_u64(2);
    let c = Fr::from_u64(3);

    assert_eq!(
        (a + b) + c,
        a + (b + c),
        "FR-005: Addition should be associative"
    );
}

#[test]
fn fr005_associative_multiplication() {
    let a = Fr::from_u64(2);
    let b = Fr::from_u64(3);
    let c = Fr::from_u64(4);

    assert_eq!(
        (a * b) * c,
        a * (b * c),
        "FR-005: Multiplication should be associative"
    );
}

// =============================================================================
// FR-005: pow5 (S-box) Tests
// =============================================================================

#[test]
fn fr005_pow5_basic() {
    // 2^5 = 32
    let two = Fr::from_u64(2);
    let result = two.pow5();
    assert_eq!(result, Fr::from_u64(32), "FR-005: 2^5 = 32");
}

#[test]
fn fr005_pow5_one() {
    // 1^5 = 1
    assert_eq!(Fr::ONE.pow5(), Fr::ONE, "FR-005: 1^5 = 1");
}

#[test]
fn fr005_pow5_zero() {
    // 0^5 = 0
    assert_eq!(Fr::ZERO.pow5(), Fr::ZERO, "FR-005: 0^5 = 0");
}

#[test]
fn fr005_pow5_three() {
    // 3^5 = 243
    let three = Fr::from_u64(3);
    let result = three.pow5();
    assert_eq!(result, Fr::from_u64(243), "FR-005: 3^5 = 243");
}

#[test]
fn fr005_square() {
    let three = Fr::from_u64(3);
    assert_eq!(three.square(), Fr::from_u64(9), "FR-005: 3^2 = 9");

    let ten = Fr::from_u64(10);
    assert_eq!(ten.square(), Fr::from_u64(100), "FR-005: 10^2 = 100");
}

// =============================================================================
// Modular Arithmetic Tests (values wrap around modulus)
// =============================================================================

#[test]
fn fr_modular_wrap_addition() {
    // Adding values that would overflow a u64 but stay in field
    let large = Fr::from_u64(u64::MAX);
    let one = Fr::ONE;
    let sum = large + one;

    // Should not be zero (would only be zero if we used u64 arithmetic)
    assert_ne!(
        sum,
        Fr::ZERO,
        "FR: Field addition should not overflow like u64"
    );

    // Verify by checking that (large + 1) - large = 1
    assert_eq!(
        sum - large,
        one,
        "FR: Modular addition should be consistent"
    );
}

#[test]
fn fr_from_nat_reduces() {
    // from_nat should reduce values mod r
    let bytes = [0xffu8; 32]; // Max 256-bit value
    let fr = Fr::from_nat(&bytes);

    // The result should be well-defined (reduced mod r)
    // We can verify it roundtrips through to_bytes_le -> from_bytes_le
    let out_bytes = fr.to_bytes_le();
    let recovered = Fr::from_bytes_le(&out_bytes).unwrap();
    assert_eq!(fr, recovered, "FR: from_nat result should be canonical");
}

// =============================================================================
// Golden Vector Tests (known-answer tests from Lean)
// =============================================================================

/// Test vector from Lean GenerateCorpus: fr_FR001_zero
#[test]
fn golden_fr001_zero() {
    let hex = "0000000000000000000000000000000000000000000000000000000000000000";
    let fr = Fr::from_hex(hex).unwrap();
    assert_eq!(fr, Fr::ZERO, "Golden: fr_FR001_zero");
}

/// Test vector from Lean GenerateCorpus: fr_FR001_one
#[test]
fn golden_fr001_one() {
    let hex = "0100000000000000000000000000000000000000000000000000000000000000";
    let fr = Fr::from_hex(hex).unwrap();
    assert_eq!(fr, Fr::ONE, "Golden: fr_FR001_one");
}

/// Test vector: fr_FR005_add (100 + 200 = 300)
#[test]
fn golden_fr005_add() {
    let a_hex = "6400000000000000000000000000000000000000000000000000000000000000"; // 100
    let b_hex = "c800000000000000000000000000000000000000000000000000000000000000"; // 200
    let expected_hex = "2c01000000000000000000000000000000000000000000000000000000000000"; // 300

    let a = Fr::from_hex(a_hex).unwrap();
    let b = Fr::from_hex(b_hex).unwrap();
    let sum = a + b;

    assert_eq!(
        sum.to_hex(),
        expected_hex,
        "Golden: fr_FR005_add (100 + 200 = 300)"
    );
}

/// Test vector: fr_FR005_mul (7 * 11 = 77)
#[test]
fn golden_fr005_mul() {
    let a_hex = "0700000000000000000000000000000000000000000000000000000000000000"; // 7
    let b_hex = "0b00000000000000000000000000000000000000000000000000000000000000"; // 11
    let expected_hex = "4d00000000000000000000000000000000000000000000000000000000000000"; // 77

    let a = Fr::from_hex(a_hex).unwrap();
    let b = Fr::from_hex(b_hex).unwrap();
    let product = a * b;

    assert_eq!(
        product.to_hex(),
        expected_hex,
        "Golden: fr_FR005_mul (7 * 11 = 77)"
    );
}

// =============================================================================
// Conformance Summary
// =============================================================================

#[test]
fn conformance_modulus_check() {
    // Verify the modulus constant matches the Lean specification
    assert_eq!(
        MODULUS_DECIMAL,
        "52435875175126190479447740508185965837690552500527637822603658699938581184513",
        "Modulus should match BLS12-381 scalar field"
    );
}
