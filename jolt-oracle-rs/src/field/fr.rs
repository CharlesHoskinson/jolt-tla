//! BLS12-381 scalar field element (Fr).
//!
//! Wraps `bls12_381::Scalar` with validation on construction to ensure
//! canonical representation.

use crate::error::{ErrorCode, OracleResult};
use bls12_381::Scalar;
use ff::Field;
use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};

/// A BLS12-381 scalar field element.
///
/// This is a newtype wrapper around `bls12_381::Scalar` that enforces
/// canonical encoding on construction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fr(Scalar);

impl Fr {
    /// The additive identity (zero).
    pub const ZERO: Fr = Fr(Scalar::ZERO);

    /// The multiplicative identity (one).
    pub const ONE: Fr = Fr(Scalar::ONE);

    /// Create an Fr from a u64 value.
    pub fn from_u64(val: u64) -> Fr {
        Fr(Scalar::from(val))
    }

    /// Create an Fr from a u64 value (const-compatible version).
    ///
    /// This uses from_raw which works in const contexts.
    pub const fn from_u64_const(val: u64) -> Fr {
        Fr(Scalar::from_raw([val, 0, 0, 0]))
    }

    /// Create an Fr from raw bytes (little-endian).
    ///
    /// Returns an error if the bytes do not represent a canonical field element
    /// (i.e., the value is >= the field modulus).
    ///
    /// # Requirements
    /// - FR-002: Validates canonical field element
    /// - FR-003: Returns E300_NonCanonicalFr for non-canonical bytes
    pub fn from_bytes_le(bytes: &[u8; 32]) -> OracleResult<Fr> {
        let scalar = Scalar::from_bytes(bytes);
        if scalar.is_some().into() {
            Ok(Fr(scalar.unwrap()))
        } else {
            Err(ErrorCode::E300_NonCanonicalFr(hex::encode(bytes)))
        }
    }

    /// Create an Fr from a hex string (64 lowercase hex chars, LE encoding).
    ///
    /// # Requirements
    /// - FR-002: Validates canonical field element
    pub fn from_hex(hex_str: &str) -> OracleResult<Fr> {
        if hex_str.len() != 64 {
            return Err(ErrorCode::E104_WrongLength(
                "64".to_string(),
                hex_str.len() as u64,
            ));
        }

        let bytes = hex::decode(hex_str).map_err(|_| ErrorCode::E103_InvalidHex)?;

        let mut arr = [0u8; 32];
        arr.copy_from_slice(&bytes);
        Self::from_bytes_le(&arr)
    }

    /// Convert to canonical 32-byte little-endian representation.
    ///
    /// # Requirements
    /// - FR-004: Produces canonical LE 32-byte output
    pub fn to_bytes_le(&self) -> [u8; 32] {
        self.0.to_bytes()
    }

    /// Convert to 64-character lowercase hex string.
    pub fn to_hex(&self) -> String {
        hex::encode(self.to_bytes_le())
    }

    /// Get the underlying scalar value.
    pub fn inner(&self) -> &Scalar {
        &self.0
    }

    /// Create an Fr from a natural number (arbitrary precision).
    ///
    /// The number is reduced modulo the field modulus.
    /// This is used for converting byte arrays (up to 31 bytes) to field elements.
    pub fn from_nat(bytes: &[u8]) -> Fr {
        // Convert bytes to u64 limbs (little-endian)
        // bls12_381::Scalar::from_raw takes [u64; 4] in little-endian limb order
        let mut val = [0u64; 4];
        for (i, chunk) in bytes.chunks(8).enumerate() {
            if i >= 4 {
                break;
            }
            let mut buf = [0u8; 8];
            buf[..chunk.len()].copy_from_slice(chunk);
            val[i] = u64::from_le_bytes(buf);
        }
        // from_raw performs modular reduction
        Fr(Scalar::from_raw(val))
    }

    /// Compute x^5 (used in Poseidon S-box).
    pub fn pow5(&self) -> Fr {
        let x2 = self.0 * self.0;
        let x4 = x2 * x2;
        Fr(x4 * self.0)
    }

    /// Square the field element.
    pub fn square(&self) -> Fr {
        Fr(self.0 * self.0)
    }

    /// Convert to decimal string representation.
    ///
    /// This produces the canonical decimal representation of the field element,
    /// which is used in the oracle CLI output.
    pub fn to_decimal(&self) -> String {
        // Convert from little-endian bytes to big-endian limbs for decimal conversion
        let bytes = self.to_bytes_le();

        // Convert to u64 limbs (little-endian order in memory)
        let limbs: [u64; 4] = [
            u64::from_le_bytes(bytes[0..8].try_into().unwrap_or([0u8; 8])),
            u64::from_le_bytes(bytes[8..16].try_into().unwrap_or([0u8; 8])),
            u64::from_le_bytes(bytes[16..24].try_into().unwrap_or([0u8; 8])),
            u64::from_le_bytes(bytes[24..32].try_into().unwrap_or([0u8; 8])),
        ];

        // Convert to decimal using repeated division
        // We work with 256-bit unsigned integers
        let mut result = String::new();
        let mut value = limbs;

        // Handle zero case
        if value == [0, 0, 0, 0] {
            return "0".to_string();
        }

        while value != [0, 0, 0, 0] {
            let remainder = div_by_10(&mut value);
            result.push((b'0' + remainder) as char);
        }

        result.chars().rev().collect()
    }
}

/// Divide a 256-bit number (as 4 u64 limbs, little-endian) by 10 in place.
/// Returns the remainder.
fn div_by_10(limbs: &mut [u64; 4]) -> u8 {
    let mut carry: u128 = 0;
    // Process from most significant to least significant
    for i in (0..4).rev() {
        let cur = carry * (1u128 << 64) + limbs[i] as u128;
        limbs[i] = (cur / 10) as u64;
        carry = cur % 10;
    }
    carry as u8
}

impl Default for Fr {
    fn default() -> Self {
        Self::ZERO
    }
}

impl From<u64> for Fr {
    fn from(val: u64) -> Self {
        Fr::from_u64(val)
    }
}

impl Add for Fr {
    type Output = Fr;
    fn add(self, rhs: Fr) -> Fr {
        Fr(self.0 + rhs.0)
    }
}

impl Sub for Fr {
    type Output = Fr;
    fn sub(self, rhs: Fr) -> Fr {
        Fr(self.0 - rhs.0)
    }
}

impl Mul for Fr {
    type Output = Fr;
    fn mul(self, rhs: Fr) -> Fr {
        Fr(self.0 * rhs.0)
    }
}

impl Neg for Fr {
    type Output = Fr;
    fn neg(self) -> Fr {
        Fr(-self.0)
    }
}

impl fmt::Display for Fr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_decimal())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zero_one() {
        assert_eq!(
            Fr::ZERO.to_hex(),
            "0000000000000000000000000000000000000000000000000000000000000000"
        );
        assert_eq!(
            Fr::ONE.to_hex(),
            "0100000000000000000000000000000000000000000000000000000000000000"
        );
    }

    #[test]
    fn test_from_u64() {
        let fr = Fr::from_u64(42);
        assert_eq!(
            fr.to_hex(),
            "2a00000000000000000000000000000000000000000000000000000000000000"
        );
    }

    #[test]
    fn test_roundtrip() {
        let original = Fr::from_u64(12345);
        let bytes = original.to_bytes_le();
        let recovered = Fr::from_bytes_le(&bytes).unwrap();
        assert_eq!(original, recovered);
    }

    #[test]
    fn test_arithmetic() {
        let a = Fr::from_u64(100);
        let b = Fr::from_u64(200);
        let sum = a + b;
        assert_eq!(sum, Fr::from_u64(300));

        let product = Fr::from_u64(7) * Fr::from_u64(11);
        assert_eq!(product, Fr::from_u64(77));
    }
}
