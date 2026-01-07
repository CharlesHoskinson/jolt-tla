import Jolt.Field.Fr

namespace Jolt.Poseidon

/-- Poseidon hash configuration.

Contains all parameters needed for the Poseidon permutation. -/
structure Config where
  /-- State width (t) -/
  width : Nat
  /-- Number of full rounds -/
  fullRounds : Nat
  /-- Number of partial rounds -/
  partialRounds : Nat
  /-- Round constants (width × (fullRounds + partialRounds)) -/
  roundConstants : Array Fr
  /-- MDS matrix (width × width) -/
  mdsMatrix : Array (Array Fr)
  deriving Repr

namespace Config

/-- Sponge rate (width - 1, capacity = 1). -/
def rate (c : Config) : Nat := c.width - 1

/-- Total number of rounds. -/
def totalRounds (c : Config) : Nat := c.fullRounds + c.partialRounds

/-- Get round constant at (round, index). -/
def getRoundConstant (c : Config) (round : Nat) (idx : Nat) : Fr :=
  c.roundConstants.getD (round * c.width + idx) Fr.zero

/-- Get MDS matrix entry at (row, col). -/
def getMDS (c : Config) (row col : Nat) : Fr :=
  (c.mdsMatrix.getD row #[]).getD col Fr.zero

end Config

/-- Default Poseidon configuration for BLS12-381.

Standard parameters: t=3, RF=8, RP=56.
Round constants and MDS matrix must be loaded from registry. -/
def defaultConfig : Config where
  width := 3
  fullRounds := 8
  partialRounds := 56
  roundConstants := #[]  -- Must be populated from registry
  mdsMatrix := #[]       -- Must be populated from registry

/-- Validate that config has correct dimensions. -/
def validateConfig (c : Config) : Bool :=
  c.roundConstants.size == c.width * c.totalRounds &&
  c.mdsMatrix.size == c.width &&
  c.mdsMatrix.all (·.size == c.width)

end Jolt.Poseidon
