//! Transcript state wrapping Poseidon sponge with type-tagged absorption.
//!
//! Implements the transcript protocol per specification section 8.

use crate::error::{ErrorCode, OracleResult};
use crate::field::Fr;
use crate::poseidon::SpongeState;

/// Type tag for bytes absorption.
const TYPE_BYTES: Fr = Fr::from_u64_const(1);

/// Type tag for u64 absorption.
const TYPE_U64: Fr = Fr::from_u64_const(2);

/// Type tag for tag string absorption.
const TYPE_TAG: Fr = Fr::from_u64_const(3);

/// Transcript state wrapping Poseidon sponge.
pub struct Transcript {
    sponge: SpongeState,
}

impl Transcript {
    /// Initialize transcript per specification section 8.4 TranscriptV1.init().
    ///
    /// Per spec:
    /// 1. state[0..t-1] := 0
    /// 2. mode := ABSORB
    /// 3. pos := 0
    /// 4. absorb_tag("JOLT/TRANSCRIPT/V1")
    /// 5. return transcript
    pub fn new() -> OracleResult<Self> {
        let mut t = Transcript {
            sponge: SpongeState::new(),
        };
        t.absorb_tag("JOLT/TRANSCRIPT/V1")?;
        Ok(t)
    }

    /// Absorb a single field element (RAW, no type tag).
    fn absorb_fr(&mut self, x: Fr) {
        self.sponge.absorb_one(x);
    }

    /// Absorb a u64 with TYPE_U64 tag.
    pub fn absorb_u64(&mut self, x: u64) {
        self.absorb_fr(TYPE_U64);
        self.absorb_fr(Fr::from_u64(x));
    }

    /// Convert up to 31 bytes to Fr (little-endian).
    ///
    /// Rejects if more than 31 bytes (never truncate).
    fn fr_from_u248(bytes: &[u8]) -> OracleResult<Fr> {
        if bytes.len() > 31 {
            return Err(ErrorCode::E104_WrongLength(
                "31".to_string(),
                bytes.len() as u64,
            ));
        }
        Ok(Fr::from_nat(bytes))
    }

    /// Absorb bytes with TYPE_BYTES tag.
    ///
    /// Absorbs: TYPE_BYTES, then absorb_u64(len), then ceil(len/31) Fr elements.
    /// Per section 8.5.2: absorb_u64 includes TYPE_U64 before the length value.
    pub fn absorb_bytes(&mut self, bytes: &[u8]) -> OracleResult<()> {
        // Check length fits in u64
        if bytes.len() > u64::MAX as usize {
            return Err(ErrorCode::E402_OutOfRange(
                "bytes length exceeds u64".to_string(),
            ));
        }
        let len = bytes.len() as u64;

        // Absorb TYPE_BYTES, then absorb_u64(len) per section 8.5.2
        self.absorb_fr(TYPE_BYTES);
        self.absorb_u64(len); // section 8.5.2 step 3: absorb_u64(n)

        // Absorb in 31-byte chunks
        let mut pos = 0;
        while pos < bytes.len() {
            let chunk_end = std::cmp::min(pos + 31, bytes.len());
            let chunk = &bytes[pos..chunk_end];
            let fr = Self::fr_from_u248(chunk)?;
            self.absorb_fr(fr);
            pos = chunk_end;
        }

        Ok(())
    }

    /// Validate tag format per specification section 8.6.
    ///
    /// Tags must:
    /// - Be ASCII only (bytes 0x20-0x7E)
    /// - Use format "NAMESPACE/NAME/VERSION" (e.g., "JOLT/STATE/V1")
    fn validate_tag(tag: &str) -> OracleResult<()> {
        // Check ASCII range
        for (i, b) in tag.bytes().enumerate() {
            if !(0x20..=0x7E).contains(&b) {
                return Err(ErrorCode::E406_InvalidTagFormat(format!(
                    "non-ASCII byte 0x{:02x} at position {}",
                    b, i
                )));
            }
        }

        // Check format: should contain at least two slashes for NAMESPACE/NAME/VERSION
        let slash_count = tag.chars().filter(|&c| c == '/').count();
        if slash_count < 2 {
            return Err(ErrorCode::E406_InvalidTagFormat(
                "tag must have format NAMESPACE/NAME/VERSION".to_string(),
            ));
        }

        Ok(())
    }

    /// Absorb a transcript tag per specification section 8.6.
    ///
    /// Absorbs: TYPE_TAG, then absorb_u64(len), then ceil(len/31) raw Fr chunks.
    /// Per section 8.6: absorb_u64 includes TYPE_U64 before the length value.
    /// This is NOT the same as absorb_bytes (different type tag at start).
    pub fn absorb_tag(&mut self, tag: &str) -> OracleResult<()> {
        // Validate tag format
        Self::validate_tag(tag)?;

        let bytes = tag.as_bytes();

        // Check length fits in u64
        if bytes.len() > u64::MAX as usize {
            return Err(ErrorCode::E402_OutOfRange(
                "tag length exceeds u64".to_string(),
            ));
        }
        let len = bytes.len() as u64;

        // Absorb TYPE_TAG, then absorb_u64(len) per section 8.6
        self.absorb_fr(TYPE_TAG);
        self.absorb_u64(len); // section 8.6 step 4: absorb_u64(n)

        // Absorb tag bytes in 31-byte chunks (raw, no TYPE_BYTES)
        let mut pos = 0;
        while pos < bytes.len() {
            let chunk_end = std::cmp::min(pos + 31, bytes.len());
            let chunk = &bytes[pos..chunk_end];
            let fr = Self::fr_from_u248(chunk)?;
            self.absorb_fr(fr);
            pos = chunk_end;
        }

        Ok(())
    }

    /// Squeeze a field element challenge.
    ///
    /// Finalizes absorption and squeezes one Fr.
    pub fn challenge_fr(&mut self) -> Fr {
        self.sponge.squeeze_one()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_transcript_creation() {
        let t = Transcript::new();
        assert!(t.is_ok());
    }

    #[test]
    fn test_valid_tag() {
        assert!(Transcript::validate_tag("JOLT/STATE/V1").is_ok());
        assert!(Transcript::validate_tag("JOLT/TRANSCRIPT/V1").is_ok());
        assert!(Transcript::validate_tag("JOLT/CONFIG_TAGS/V1").is_ok());
    }

    #[test]
    fn test_invalid_tag_format() {
        // Missing slashes
        assert!(Transcript::validate_tag("JOLT").is_err());
        assert!(Transcript::validate_tag("JOLT/STATE").is_err());
    }

    #[test]
    fn test_transcript_deterministic() {
        let mut t1 = Transcript::new().unwrap();
        t1.absorb_u64(42);
        let r1 = t1.challenge_fr();

        let mut t2 = Transcript::new().unwrap();
        t2.absorb_u64(42);
        let r2 = t2.challenge_fr();

        assert_eq!(r1, r2);
    }

    #[test]
    fn test_transcript_different_inputs() {
        let mut t1 = Transcript::new().unwrap();
        t1.absorb_u64(1);
        let r1 = t1.challenge_fr();

        let mut t2 = Transcript::new().unwrap();
        t2.absorb_u64(2);
        let r2 = t2.challenge_fr();

        assert_ne!(r1, r2);
    }
}
