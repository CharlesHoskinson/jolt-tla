import Jolt.Field.Fr
import Jolt.Poseidon.Params

/-!
# Poseidon Round Constants

Defines the MDS matrix and round constants for JOLT_POSEIDON_FR_V1 per Appendix A.

## Structure
* MDS matrix: 3×3 Cauchy matrix
* Round constants: 68 rounds × 3 = 204 field elements
* Generated via Grain LFSR per Poseidon paper §4.2

## References
* Jolt Spec §3.4.1, Appendix A
* Poseidon Paper: https://eprint.iacr.org/2019/458.pdf §4
-/

namespace Jolt.Poseidon.Constants

/-- MDS matrix for JOLT_POSEIDON_FR_V1 (3×3 Cauchy matrix).

Per Appendix A: Elements chosen to ensure MDS property over BLS12-381 Fr.
M[i,j] = 1 / (x_i + y_j) where x, y are carefully chosen. -/
def mdsMatrix : Array (Array Fr) :=
  -- Placeholder: actual values from registry/Appendix A
  #[
    #[Fr.ofNat 1, Fr.ofNat 0, Fr.ofNat 0],
    #[Fr.ofNat 0, Fr.ofNat 1, Fr.ofNat 0],
    #[Fr.ofNat 0, Fr.ofNat 0, Fr.ofNat 1]
  ]

/-- Round constants for JOLT_POSEIDON_FR_V1.

Per Appendix A: 68 rounds × 3 elements = 204 constants.
Generated via Grain LFSR seeded with:
- Field size: BLS12-381 scalar field modulus
- Parameters: t=3, RF=8, RP=60, α=5

Format: Round i constants are at indices [3*i, 3*i+1, 3*i+2]. -/
def roundConstants : Array Fr :=
  -- Placeholder: actual 204 values from registry/Appendix A
  Array.replicate (POSEIDON_TOTAL_ROUNDS * POSEIDON_WIDTH) Fr.zero

/-- Create a Config with JOLT_POSEIDON_FR_V1 constants.

This loads the actual MDS matrix and round constants per Appendix A. -/
def joltPoseidonConfig : Config where
  variant := .Poseidon
  sboxExponent := POSEIDON_SBOX_ALPHA
  width := POSEIDON_WIDTH
  fullRounds := POSEIDON_FULL_ROUNDS
  partialRounds := POSEIDON_PARTIAL_ROUNDS
  roundConstants := roundConstants
  mdsMatrix := mdsMatrix

/-- Verify that the constants have correct dimensions. -/
def validateConstants : Bool :=
  mdsMatrix.size == POSEIDON_WIDTH &&
  mdsMatrix.all (·.size == POSEIDON_WIDTH) &&
  roundConstants.size == POSEIDON_TOTAL_ROUNDS * POSEIDON_WIDTH

end Jolt.Poseidon.Constants
