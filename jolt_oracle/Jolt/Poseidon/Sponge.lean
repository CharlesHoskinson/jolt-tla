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

/-- Absorb a single field element per §8.4 absorb_fr.

1. if mode == SQUEEZE: permute(); mode = ABSORB; pos = 0
2. state[pos] += x; pos += 1
3. if pos == r: permute(); pos = 0 -/
def absorbOne (s : SpongeState) (x : Fr) : SpongeState :=
  -- Step 1: If squeezing, switch to absorb mode
  let s' := if s.mode == .Squeezing then
    let permuted := permute s.config s.state
    { s with state := permuted, mode := .Absorbing, pos := 0 }
  else s
  -- Step 2: state[pos] += x
  let newState := s'.state.set! s'.pos (s'.state.getD s'.pos Fr.zero + x)
  let newPos := s'.pos + 1
  -- Step 3: if pos == r: permute(); pos = 0
  if newPos >= s'.rate then
    let permuted := permute s'.config newState
    { s' with state := permuted, pos := 0 }
  else
    { s' with state := newState, pos := newPos }

/-- Absorb multiple field elements. -/
def absorb (s : SpongeState) (xs : Array Fr) : SpongeState := Id.run do
  let mut st := s
  for x in xs do
    st := st.absorbOne x
  return st

/-- Finalize absorption and switch to squeezing per §8.4.

Per spec: if mode == ABSORB: permute(); mode = SQUEEZE; pos = 0
NOTE: No padding is added - the spec does not specify padding. -/
def finalize (s : SpongeState) : SpongeState :=
  if s.mode != .Absorbing then s
  else
    let permuted := permute s.config s.state
    { s with state := permuted, pos := 0, mode := .Squeezing }

/-- Squeeze a single field element per §8.4 squeeze_fr.

1. if mode == ABSORB: permute(); mode = SQUEEZE; pos = 0
2. y = state[pos]; pos += 1
3. if pos == r: permute(); pos = 0
4. return y -/
def squeezeOne (s : SpongeState) : (Fr × SpongeState) :=
  -- Step 1: If absorbing, switch to squeeze mode
  let s' := if s.mode == .Absorbing then s.finalize else s
  -- Step 2: y = state[pos]
  let result := s'.state.getD s'.pos Fr.zero
  let newPos := s'.pos + 1
  -- Step 3: if pos == r: permute(); pos = 0
  if newPos >= s'.rate then
    let permuted := permute s'.config s'.state
    (result, { s' with state := permuted, pos := 0 })
  else
    (result, { s' with pos := newPos })

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
