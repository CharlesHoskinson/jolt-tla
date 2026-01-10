//! State types: Bytes32, ConfigTag, VMStateV1.

use crate::error::{ErrorCode, OracleResult};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// A 32-byte array used for hashes and roots.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Bytes32(pub [u8; 32]);

impl Serialize for Bytes32 {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.to_hex())
    }
}

impl<'de> Deserialize<'de> for Bytes32 {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = String::deserialize(deserializer)?;
        Bytes32::from_hex(&s).map_err(serde::de::Error::custom)
    }
}

impl Bytes32 {
    /// Create a zero-filled Bytes32.
    pub fn zero() -> Self {
        Bytes32([0u8; 32])
    }

    /// Create from a hex string (64 hex chars, no 0x prefix expected but tolerated).
    pub fn from_hex(hex_str: &str) -> OracleResult<Self> {
        let hex_str = hex_str.strip_prefix("0x").unwrap_or(hex_str);

        if hex_str.len() != 64 {
            return Err(ErrorCode::E104_WrongLength(
                "64".to_string(),
                hex_str.len() as u64,
            ));
        }

        let bytes = hex::decode(hex_str).map_err(|_| ErrorCode::E103_InvalidHex)?;

        let mut arr = [0u8; 32];
        arr.copy_from_slice(&bytes);
        Ok(Bytes32(arr))
    }

    /// Convert to hex string.
    pub fn to_hex(&self) -> String {
        hex::encode(self.0)
    }

    /// Get the underlying bytes.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

impl Default for Bytes32 {
    fn default() -> Self {
        Self::zero()
    }
}

impl From<[u8; 32]> for Bytes32 {
    fn from(arr: [u8; 32]) -> Self {
        Bytes32(arr)
    }
}

/// A config tag entry (name bytes, value bytes).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConfigTag {
    /// Tag name as raw bytes (hex-encoded in JSON).
    #[serde(with = "hex_bytes")]
    pub name: Vec<u8>,
    /// Tag value as raw bytes (hex-encoded in JSON).
    #[serde(with = "hex_bytes")]
    pub value: Vec<u8>,
}

mod hex_bytes {
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn serialize<S: Serializer>(bytes: &Vec<u8>, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&hex::encode(bytes))
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<Vec<u8>, D::Error> {
        let s = String::deserialize(deserializer)?;
        hex::decode(&s).map_err(serde::de::Error::custom)
    }
}

impl ConfigTag {
    /// Create a new config tag.
    pub fn new(name: Vec<u8>, value: Vec<u8>) -> Self {
        ConfigTag { name, value }
    }
}

/// RISC-V VM state (version 1) per specification section 11.5.
///
/// Contains all state needed for state digest computation.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct VMStateV1 {
    /// Program counter.
    pub pc: u64,
    /// 32 general-purpose registers.
    pub regs: [u64; 32],
    /// Step counter.
    pub step_counter: u64,
    /// Read-write memory Merkle root.
    pub rw_mem_root: Bytes32,
    /// I/O Merkle root.
    pub io_root: Bytes32,
    /// Halted flag (0 = running, 1 = halted) per section 11.5.
    pub halted: u8,
    /// Exit code (valid only when halted, must be <= 255).
    pub exit_code: u64,
    /// Config tags (prover's claim, must match registry projection per section 3.8).
    pub config_tags: Vec<ConfigTag>,
}

impl VMStateV1 {
    /// Create initial state (all zeros).
    pub fn initial() -> Self {
        Self::default()
    }
}
