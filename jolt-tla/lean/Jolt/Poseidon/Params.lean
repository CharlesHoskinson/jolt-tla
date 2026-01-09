import Jolt.Field.Fr

/-!
# Poseidon Hash Parameters

Defines configuration parameters for Poseidon hash per §3.4.1.

## JOLT_POSEIDON_FR_V1 Parameters
* Field: BLS12-381 scalar field Fr
* State width: t = 3
* Sponge rate: r = 2
* Sponge capacity: c = 1
* Full rounds: RF = 8
* Partial rounds: RP = 60
* Security level: 128 bits

## References
* Jolt Spec §3.4.1, §8
* Poseidon Paper: https://eprint.iacr.org/2019/458.pdf
-/

namespace Jolt.Poseidon

/-- Poseidon variant type. -/
inductive Variant where
  | Poseidon   -- Original Poseidon
  | Poseidon2  -- Poseidon2 variant
  deriving Repr, DecidableEq, Inhabited

/-- JOLT_POSEIDON_FR_V1 state width (t = 3). -/
def POSEIDON_WIDTH : Nat := 3

/-- JOLT_POSEIDON_FR_V1 sponge rate (r = 2). -/
def POSEIDON_RATE : Nat := 2

/-- JOLT_POSEIDON_FR_V1 sponge capacity (c = 1). -/
def POSEIDON_CAPACITY : Nat := 1

/-- JOLT_POSEIDON_FR_V1 full rounds (RF = 8). -/
def POSEIDON_FULL_ROUNDS : Nat := 8

/-- JOLT_POSEIDON_FR_V1 partial rounds (RP = 60). -/
def POSEIDON_PARTIAL_ROUNDS : Nat := 60

/-- JOLT_POSEIDON_FR_V1 total rounds (RF + RP = 68). -/
def POSEIDON_TOTAL_ROUNDS : Nat := POSEIDON_FULL_ROUNDS + POSEIDON_PARTIAL_ROUNDS

/-- JOLT_POSEIDON_FR_V1 security level in bits. -/
def POSEIDON_SECURITY_BITS : Nat := 128

/-- JOLT_POSEIDON_FR_V1 S-box exponent (α = 5). -/
def POSEIDON_SBOX_ALPHA : Nat := 5

/-- Poseidon hash configuration.

Contains all parameters needed for the Poseidon permutation per §3.4.1. -/
structure Config where
  /-- Poseidon variant (Poseidon or Poseidon2) -/
  variant : Variant
  /-- S-box exponent (α, typically 5) -/
  sboxExponent : Nat
  /-- State width (t) -/
  width : Nat
  /-- Number of full rounds (RF) -/
  fullRounds : Nat
  /-- Number of partial rounds (RP) -/
  partialRounds : Nat
  /-- Round constants (width × (fullRounds + partialRounds)) -/
  roundConstants : Array Fr
  /-- MDS matrix (width × width) -/
  mdsMatrix : Array (Array Fr)
  deriving Repr

namespace Config

/-- Sponge rate (width - capacity, where capacity = 1). -/
def rate (c : Config) : Nat := c.width - 1

/-- Total number of rounds (RF + RP). -/
def totalRounds (c : Config) : Nat := c.fullRounds + c.partialRounds

/-- Get round constant at (round, index). -/
def getRoundConstant (c : Config) (round : Nat) (idx : Nat) : Fr :=
  c.roundConstants.getD (round * c.width + idx) Fr.zero

/-- Get MDS matrix entry at (row, col). -/
def getMDS (c : Config) (row col : Nat) : Fr :=
  (c.mdsMatrix.getD row #[]).getD col Fr.zero

/-- Check if config matches JOLT_POSEIDON_FR_V1 parameters. -/
def isJoltPoseidonV1 (c : Config) : Bool :=
  c.width == POSEIDON_WIDTH &&
  c.fullRounds == POSEIDON_FULL_ROUNDS &&
  c.partialRounds == POSEIDON_PARTIAL_ROUNDS

end Config

/-- Default Poseidon configuration for JOLT_POSEIDON_FR_V1.

Parameters per §3.4.1: t=3, RF=8, RP=60.
Round constants and MDS matrix must be loaded from registry. -/
def defaultConfig : Config where
  variant := .Poseidon
  sboxExponent := POSEIDON_SBOX_ALPHA
  width := POSEIDON_WIDTH
  fullRounds := POSEIDON_FULL_ROUNDS
  partialRounds := POSEIDON_PARTIAL_ROUNDS
  roundConstants := #[]  -- Must be populated from registry
  mdsMatrix := #[]       -- Must be populated from registry

/-- JOLT_POSEIDON_FR_V1: The canonical Poseidon configuration per §3.4.1.

This is the production configuration for Jolt. Round constants and MDS matrix
must be populated from Appendix A / registry before use. -/
def JOLT_POSEIDON_FR_V1 : Config where
  variant := .Poseidon
  sboxExponent := POSEIDON_SBOX_ALPHA
  width := POSEIDON_WIDTH
  fullRounds := POSEIDON_FULL_ROUNDS
  partialRounds := POSEIDON_PARTIAL_ROUNDS
  roundConstants := #[]  -- Populated from Appendix A
  mdsMatrix := #[]       -- Populated from Appendix A

/-- Validate that config has correct dimensions. -/
def validateConfig (c : Config) : Bool :=
  c.roundConstants.size == c.width * c.totalRounds &&
  c.mdsMatrix.size == c.width &&
  c.mdsMatrix.all (·.size == c.width)

/-- Validate that config matches JOLT_POSEIDON_FR_V1 parameters per §3.4.1. -/
def Config.validate (c : Config) : Bool :=
  c.variant == .Poseidon &&
  c.sboxExponent == POSEIDON_SBOX_ALPHA &&
  c.width == POSEIDON_WIDTH &&
  c.fullRounds == POSEIDON_FULL_ROUNDS &&
  c.partialRounds == POSEIDON_PARTIAL_ROUNDS &&
  validateConfig c

end Jolt.Poseidon
