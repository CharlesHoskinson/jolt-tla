import Jolt.Poseidon.Params

namespace Jolt.Poseidon

/-- Poseidon S-box: x^5 mod r. -/
def sbox (x : Fr) : Fr := Fr.pow5 x

/-- Apply MDS matrix to state.

state' = MDS × state -/
def applyMDS (cfg : Config) (state : Array Fr) : Array Fr := Id.run do
  let mut result := (List.replicate cfg.width Fr.zero).toArray
  for i in [:cfg.width] do
    let mut sum := Fr.zero
    for j in [:cfg.width] do
      sum := sum + cfg.getMDS i j * state.getD j Fr.zero
    result := result.set! i sum
  return result

/-- Add round constants to state. -/
def addRoundConstants (cfg : Config) (state : Array Fr) (round : Nat) : Array Fr := Id.run do
  let mut result := state
  for i in [:cfg.width] do
    result := result.set! i (result.getD i Fr.zero + cfg.getRoundConstant round i)
  return result

/-- Full round: S-box on all elements, then MDS, then add constants. -/
def fullRound (cfg : Config) (state : Array Fr) (round : Nat) : Array Fr :=
  let withSbox := state.map sbox
  let afterMDS := applyMDS cfg withSbox
  addRoundConstants cfg afterMDS round

/-- Partial round: S-box on first element only, then MDS, then add constants. -/
def partialRound (cfg : Config) (state : Array Fr) (round : Nat) : Array Fr :=
  let withSbox := state.set! 0 (sbox (state.getD 0 Fr.zero))
  let afterMDS := applyMDS cfg withSbox
  addRoundConstants cfg afterMDS round

/-- Complete Poseidon permutation.

Runs:
1. First half of full rounds (RF/2)
2. All partial rounds (RP)
3. Second half of full rounds (RF/2)
-/
def permute (cfg : Config) (state : Array Fr) : Array Fr := Id.run do
  if state.size != cfg.width then return state  -- Invalid input
  let halfFull := cfg.fullRounds / 2
  let mut st := state
  let mut round := 0

  -- First half of full rounds
  for _ in [:halfFull] do
    st := fullRound cfg st round
    round := round + 1

  -- Partial rounds
  for _ in [:cfg.partialRounds] do
    st := partialRound cfg st round
    round := round + 1

  -- Second half of full rounds
  for _ in [:halfFull] do
    st := fullRound cfg st round
    round := round + 1

  return st

/-- Poseidon permutation with trace output for debugging.

Returns (final_state, round_traces) where each trace entry contains
the state after that round. Useful for divergence localization when
comparing with Rust implementation (POS-006). -/
def permuteWithTrace (cfg : Config) (state : Array Fr) : (Array Fr × Array (Array Fr)) := Id.run do
  if state.size != cfg.width then return (state, #[])
  let halfFull := cfg.fullRounds / 2
  let mut st := state
  let mut round := 0
  let mut traces : Array (Array Fr) := #[]

  -- First half of full rounds
  for _ in [:halfFull] do
    st := fullRound cfg st round
    traces := traces.push st
    round := round + 1

  -- Partial rounds
  for _ in [:cfg.partialRounds] do
    st := partialRound cfg st round
    traces := traces.push st
    round := round + 1

  -- Second half of full rounds
  for _ in [:halfFull] do
    st := fullRound cfg st round
    traces := traces.push st
    round := round + 1

  return (st, traces)

end Jolt.Poseidon
