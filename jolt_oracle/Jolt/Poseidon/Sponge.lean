import Jolt.Poseidon.Permute

namespace Jolt.Poseidon

/-- Sponge operation mode. -/
inductive Mode where
  | Absorbing
  | Squeezing
  deriving Repr, DecidableEq

/-- Sponge state.

Contains the internal state array, current position, and mode. -/
structure SpongeState where
  /-- Internal state (width elements) -/
  state : Array Fr
  /-- Current position in rate portion -/
  pos : Nat
  /-- Current mode -/
  mode : Mode
  /-- Configuration -/
  config : Config
  deriving Repr

namespace SpongeState

/-- Create a new sponge state. -/
def init (cfg : Config) : SpongeState where
  state := Array.replicate cfg.width Fr.zero
  pos := 0
  mode := .Absorbing
  config := cfg

/-- Get the rate (absorbable elements per permutation). -/
def rate (s : SpongeState) : Nat := s.config.rate

/-- Absorb a single field element. -/
def absorbOne (s : SpongeState) (x : Fr) : SpongeState :=
  if s.mode != .Absorbing then s  -- Error: wrong mode
  else
    let newState := s.state.set! s.pos (s.state.getD s.pos Fr.zero + x)
    if s.pos + 1 >= s.rate then
      -- Rate full, permute
      let permuted := permute s.config newState
      { s with state := permuted, pos := 0 }
    else
      { s with state := newState, pos := s.pos + 1 }

/-- Absorb multiple field elements. -/
def absorb (s : SpongeState) (xs : Array Fr) : SpongeState := Id.run do
  let mut st := s
  for x in xs do
    st := st.absorbOne x
  return st

/-- Finalize absorption and prepare for squeezing.

Pads with 1 and permutes if needed. -/
def finalize (s : SpongeState) : SpongeState :=
  if s.mode != .Absorbing then s
  else
    -- Pad with 1
    let padded := s.state.set! s.pos (s.state.getD s.pos Fr.zero + Fr.one)
    -- Permute
    let permuted := permute s.config padded
    { s with state := permuted, pos := 0, mode := .Squeezing }

/-- Squeeze a single field element. -/
def squeezeOne (s : SpongeState) : (Fr × SpongeState) :=
  let s' := if s.mode == .Absorbing then s.finalize else s
  if s'.pos >= s'.rate then
    -- Need to permute for more output
    let permuted := permute s'.config s'.state
    let result := permuted.getD 0 Fr.zero
    (result, { s' with state := permuted, pos := 1 })
  else
    let result := s'.state.getD s'.pos Fr.zero
    (result, { s' with pos := s'.pos + 1 })

/-- Squeeze n field elements. -/
def squeeze (s : SpongeState) (n : Nat) : (Array Fr × SpongeState) := Id.run do
  let mut st := s
  let mut result : Array Fr := #[]
  for _ in [:n] do
    let (x, st') := st.squeezeOne
    result := result.push x
    st := st'
  return (result, st)

end SpongeState

/-- Hash an array of field elements to a single field element. -/
def hash (cfg : Config) (xs : Array Fr) : Fr :=
  let s := SpongeState.init cfg |>.absorb xs
  let (result, _) := s.squeezeOne
  result

/-- Hash an array of field elements to n field elements. -/
def hashN (cfg : Config) (xs : Array Fr) (n : Nat) : Array Fr :=
  let s := SpongeState.init cfg |>.absorb xs
  let (result, _) := s.squeeze n
  result

end Jolt.Poseidon
