/-!
# NearFall Core Types

Base type definitions for the trace conformance kernel.

## Main Definitions

* `Digest` - Cryptographic digest wrapper
* `FieldElem` - Field element for public inputs
* `ChallengeType` - Challenge from transcript squeeze
* `Label` - Domain separation labels for transcript
* `ConfigType` - Resolved configuration
* `Event` - Trace event inductive (9 variants)
* `Trace` - Sequence of events
* `TranscriptState` - Fiat-Shamir transcript state
* `CheckState` - Trace checker state machine

## Implementation Notes

All types derive `DecidableEq` to enable decidable equality checks in proofs.
Structure wrappers are used (per Mathlib style) instead of opaque types.
Note: `Repr` is not derived for types containing `ByteArray` since the
standard library lacks this instance.

## References

* Jolt Spec §1-§11 for event semantics
* Jolt Spec §8 for transcript operations
* Jolt Spec §3.4 for configuration
-/

namespace NearFall

/-! ### Primitive Types -/

/-- Cryptographic digest. Uses structure wrapper per Mathlib style.

Represents the output of a hash function (e.g., Poseidon).
See Jolt Spec §8 for digest usage in transcripts. -/
structure Digest where
  /-- Raw bytes of the digest. -/
  bytes : ByteArray
  deriving DecidableEq, BEq, Inhabited

/-- Field element for public inputs.

In production, this would be a proper field element type.
Simplified to UInt64 for the conformance kernel.
See Jolt Spec §5.5 for public input assembly. -/
structure FieldElem where
  /-- Field element value (simplified representation). -/
  value : UInt64
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Challenge generated from transcript squeeze.

Contains the challenge bytes produced by squeezing the transcript.
See Jolt Spec §8.6 for challenge generation. -/
structure ChallengeType where
  /-- Challenge bytes from transcript squeeze. -/
  value : ByteArray
  deriving DecidableEq, BEq, Inhabited

/-! ### Domain Separation Labels -/

/-- Domain separation labels for transcript operations.

These labels ensure that absorptions in different contexts cannot be
confused, preventing cross-protocol attacks.
See Jolt Spec §8.4 for label definitions. -/
inductive Label where
  /-- VM state absorption label: JOLT/TRANSCRIPT/VM_STATE/V1 -/
  | vm_state
  /-- Challenge generation label: JOLT/TRANSCRIPT/CHALLENGE/V1 -/
  | challenge
  /-- SMT page hash label: JOLT/SMT/PAGE/V1 -/
  | smt_page
  /-- SMT node hash label: JOLT/SMT/NODE/V1 -/
  | smt_node
  /-- Batch commitment label: JOLT/BATCH/COMMIT/V1 -/
  | batch_commit
  /-- State digest label: JOLT/STATE/V1 -/
  | state_digest
  /-- Custom label for extensibility. -/
  | custom (s : String)
  deriving Repr, DecidableEq, BEq, Inhabited

/-! ### Configuration -/

/-- Resolved configuration from registry.

Contains all configuration parameters locked at execution start.
See Jolt Spec §3.4 for configuration resolution. -/
structure ConfigType where
  /-- Specification version string. -/
  spec_version : String
  /-- Maximum manifest size in bytes. -/
  max_manifest_bytes : Nat
  /-- Maximum number of intents. -/
  max_intents : Nat
  /-- Context bytes (32 bytes). -/
  context_bytes32 : ByteArray
  deriving DecidableEq

/-- Default configuration for testing. -/
instance : Inhabited ConfigType where
  default := {
    spec_version := "1.0.0"
    max_manifest_bytes := 65536
    max_intents := 256
    context_bytes32 := ByteArray.empty
  }

/-! ### Trace Events -/

/-- Trace events representing zkVM host operations.

Each variant maps to a JSON/CBOR object in the trace log.
The checker validates that events occur in the correct order
and satisfy all security invariants.

## Variants

* `start_run` - Execution begins (Jolt Spec §1)
* `config_resolved` - Configuration locked (Jolt Spec §3.4)
* `transcript_init` - New transcript for chunk (Jolt Spec §8.4)
* `absorb` - Data absorbed into transcript (Jolt Spec §8.5)
* `squeeze` - Challenge generated (Jolt Spec §8.6)
* `public_inputs_assembled` - PI ready for verifier (Jolt Spec §5.5)
* `chunk_start` - Continuation boundary (Jolt Spec §11.10)
* `chunk_end` - Chunk completion with digest (Jolt Spec §11.10)
* `verify_end` - All proofs verified (Jolt Spec §14)
-/
inductive Event where
  /-- Execution begins with a unique run identifier.
      Must be the first event in any valid trace.
      See Jolt Spec §1. -/
  | start_run (run_id : ByteArray)
  /-- Configuration resolved and locked.
      Must occur after start_run and before other operations.
      See Jolt Spec §3.4. -/
  | config_resolved (cfg : ConfigType)
  /-- Initialize transcript for a chunk.
      Creates fresh transcript state for the given chunk index.
      See Jolt Spec §8.4. -/
  | transcript_init (chunk_index : Nat)
  /-- Absorb labeled data into transcript.
      Domain separation via label prevents cross-context attacks.
      See Jolt Spec §8.5. -/
  | absorb (label : Label) (data : ByteArray)
  /-- Squeeze challenge from transcript.
      May only occur after all required absorptions.
      See Jolt Spec §8.6. -/
  | squeeze (label : Label) (challenge : ChallengeType)
  /-- Public inputs assembled for verifier.
      Contains all field elements for proof verification.
      See Jolt Spec §5.5. -/
  | public_inputs_assembled (inputs : List FieldElem)
  /-- Start of a continuation chunk.
      Links to previous chunk via digest for chain integrity.
      See Jolt Spec §11.10. -/
  | chunk_start (prev_digest : Digest) (chunk_index : Nat)
  /-- End of a continuation chunk.
      Records the digest for linking to the next chunk.
      See Jolt Spec §11.10. -/
  | chunk_end (digest : Digest)
  /-- All proofs verified, execution complete.
      Must be the final event in a valid trace.
      See Jolt Spec §14. -/
  | verify_end
  deriving DecidableEq

/-- A trace is a sequence of events. -/
abbrev Trace := List Event

/-! ### Transcript State -/

/-- Absorption entry: labeled data absorbed into transcript. -/
structure AbsorptionEntry where
  /-- Domain separation label. -/
  label : Label
  /-- Absorbed data. -/
  data : ByteArray
  deriving DecidableEq, BEq

/-- Transcript state for Fiat-Shamir transformation.

Tracks all absorptions for later soundness proofs.
The actual hash computation is abstracted; we only track
the absorption history for collision resistance arguments.
See Jolt Spec §8 for transcript semantics. -/
structure TranscriptState where
  /-- Chunk index this transcript belongs to. -/
  chunk_index : Nat
  /-- List of absorption entries in order. -/
  absorbed : List AbsorptionEntry
  /-- Whether squeeze has been called (no more absorptions allowed). -/
  squeezed : Bool
  deriving DecidableEq

/-- Empty transcript state. -/
def TranscriptState.empty : TranscriptState :=
  { chunk_index := 0, absorbed := [], squeezed := false }

/-- Initialize transcript for a specific chunk. -/
def TranscriptState.init (chunk_idx : Nat) : TranscriptState :=
  { chunk_index := chunk_idx, absorbed := [], squeezed := false }

instance : Inhabited TranscriptState where
  default := TranscriptState.empty

/-! ### Checker State -/

/-- Expected input tracking for no-early-squeeze invariant.

Tracks which inputs must be absorbed before squeeze is allowed. -/
structure ExpectedInputs where
  /-- Labels that must still be absorbed. -/
  pending : List Label
  deriving Repr, DecidableEq

/-- Empty expected inputs (squeeze allowed). -/
def ExpectedInputs.empty : ExpectedInputs := { pending := [] }

/-- Check if all expected inputs have been absorbed. -/
def ExpectedInputs.isEmpty (ei : ExpectedInputs) : Bool := ei.pending.isEmpty

instance : Inhabited ExpectedInputs where
  default := ExpectedInputs.empty

/-- Checker state machine state.

Tracks all information needed to validate trace invariants:
* Event ordering (start_run first, verify_end last)
* Transcript state for Fiat-Shamir
* Chunk linking for continuation integrity
* Expected inputs for no-early-squeeze

See Jolt Spec §15 for invariant definitions. -/
structure CheckState where
  /-- Whether start_run has been seen. -/
  seen_start : Bool
  /-- Resolved configuration, if any. -/
  config : Option ConfigType
  /-- Current transcript state. -/
  current_transcript : TranscriptState
  /-- Expected inputs that must be absorbed before squeeze. -/
  expected_inputs : ExpectedInputs
  /-- Current chunk index. -/
  current_chunk : Nat
  /-- Digest from the last completed chunk. -/
  last_chunk_digest : Option Digest
  /-- Buffer for assembled public inputs. -/
  public_inputs_buffer : List FieldElem
  /-- Whether verify_end has been seen. -/
  finished : Bool
  deriving DecidableEq

/-- Initial checker state before any events. -/
def CheckState.initial : CheckState := {
  seen_start := false
  config := none
  current_transcript := TranscriptState.empty
  expected_inputs := ExpectedInputs.empty
  current_chunk := 0
  last_chunk_digest := none
  public_inputs_buffer := []
  finished := false
}

instance : Inhabited CheckState where
  default := CheckState.initial

end NearFall
