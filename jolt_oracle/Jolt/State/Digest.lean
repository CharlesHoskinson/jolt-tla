import Jolt.State.VMState
import Jolt.Transcript.State
import Jolt.Encoding.Bytes32

namespace Jolt.State

open Jolt.Transcript

/-- Compute state digest per §11.10.2.

Takes:
- cfg: Poseidon configuration
- programHash: 32-byte program hash (separate from VMState!)
- state: VM state including config_tags

Returns: digest as Fr -/
def computeStateDigest (cfg : Poseidon.Config) (programHash : Bytes32) (state : VMStateV1) :
    OracleResult Fr := do
  -- Validate state first
  state.validate

  -- Initialize transcript per §8.4 (absorbs "JOLT/TRANSCRIPT/V1")
  let mut t ← Transcript.initTranscript cfg

  -- Step 1: absorb_tag("JOLT/STATE/V1")
  t ← absorbTag t "JOLT/STATE/V1"

  -- Step 2: absorb_bytes(program_hash)
  t ← absorbBytes t programHash.data

  -- Step 3: absorb_u64(pc)
  t := absorbU64 t state.pc

  -- Step 4: absorb_u64(regs[i]) for i=0..31 (BEFORE step_counter!)
  for i in [:32] do
    t := absorbU64 t (state.regs.getD i 0)

  -- Step 5: absorb_u64(step_counter) (AFTER regs!)
  t := absorbU64 t state.stepCounter

  -- Step 6: absorb_bytes(rw_mem_root)
  t ← absorbBytes t state.rwMemRoot.data

  -- Step 7: absorb_bytes(io_root)
  t ← absorbBytes t state.ioRoot.data

  -- Step 8: absorb_u64(halted)
  t := absorbU64 t state.halted

  -- Step 9: absorb_u64(exit_code)
  t := absorbU64 t state.exitCode

  -- Step 10: absorb_tag("JOLT/CONFIG_TAGS/V1")
  t ← absorbTag t "JOLT/CONFIG_TAGS/V1"

  -- Step 11: absorb_u64(len(config_tags))
  t := absorbU64 t state.configTags.size.toUInt64

  -- Step 12: for each config tag
  for tag in state.configTags do
    -- absorb_tag("JOLT/TAG/V1")
    t ← absorbTag t "JOLT/TAG/V1"
    -- absorb_bytes(name)
    t ← absorbBytes t tag.name
    -- absorb_bytes(value)
    t ← absorbBytes t tag.value

  -- Steps 13-14: challenge_fr() → digest
  let (digest, _) := challengeFr t
  pure digest

/-- Verify state digest matches expected value. -/
def verifyStateDigest (cfg : Poseidon.Config) (programHash : Bytes32) (state : VMStateV1)
    (expectedDigest : Fr) : OracleResult Bool := do
  let computed ← computeStateDigest cfg programHash state
  pure (computed == expectedDigest)

end Jolt.State
