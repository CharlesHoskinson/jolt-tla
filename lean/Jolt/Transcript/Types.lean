import Jolt.Field.Fr
import Jolt.Poseidon.Sponge

namespace Jolt.Transcript

/-- Type tag for bytes absorption. -/
def TYPE_BYTES : Fr := Fr.ofNat 1

/-- Type tag for u64 absorption. -/
def TYPE_U64 : Fr := Fr.ofNat 2

/-- Type tag for tag string absorption. -/
def TYPE_TAG : Fr := Fr.ofNat 3

/-- Type tag for vector absorption. -/
def TYPE_VEC : Fr := Fr.ofNat 4

/-- Maximum u64 value (2^64). -/
def MAX_U64 : Nat := 18446744073709551616

/-- Transcript operation mode. -/
inductive Mode where
  | Absorbing
  | Squeezing
  deriving Repr, DecidableEq

/-- Transcript state wrapping Poseidon sponge. -/
structure State where
  /-- Underlying sponge state -/
  sponge : Poseidon.SpongeState
  /-- Current mode -/
  mode : Mode
  deriving Repr

namespace State

/-- Initialize transcript with Poseidon config. -/
def init (cfg : Poseidon.Config) : State where
  sponge := Poseidon.SpongeState.init cfg
  mode := .Absorbing

/-- Get the Poseidon configuration. -/
def config (s : State) : Poseidon.Config := s.sponge.config

end State

end Jolt.Transcript
