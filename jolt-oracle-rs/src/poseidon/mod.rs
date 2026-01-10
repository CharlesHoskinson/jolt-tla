//! Poseidon hash function (JOLT_POSEIDON_FR_V1).
//!
//! Implements the Poseidon permutation and sponge construction per spec §3.4.1.
//!
//! # Requirements
//!
//! - POS-001: Parameters t=3, r=2, RF=8, RP=60
//! - POS-002: 68 rounds (4 full + 60 partial + 4 full)
//! - POS-003: Round constants from metadata.json
//! - POS-004: Sponge absorb in rate-sized chunks
//! - POS-005: Bit-identical output to Lean
//! - POS-006: Trace mode for divergence localization

mod permute;
mod sponge;

pub use permute::{permute, permute_with_trace};
pub use sponge::{hash, hash_n, SpongeState};

// Include generated parameters
include!(concat!(env!("OUT_DIR"), "/params_generated.rs"));
