import NearFall

/-!
# Tests.Basic

Basic test suite for the NearFall kernel.

## Main Tests
* Version string validation
* Type construction validation
* Initial state verification
* Event distinctness checks

## References
* Jolt Spec - Testing requirements
-/

namespace Tests

open NearFall

/-! ### Version Tests -/

-- Verify kernel version is defined (v0.2.0 = TLA+ integration)
#guard NearFall.version == "0.2.0"

/-- Example: version string is non-empty. -/
example : NearFall.version.length > 0 := by decide

/-! ### Type Construction Tests -/

-- Digest can be constructed
#guard (Digest.mk ByteArray.empty).bytes == ByteArray.empty

-- FieldElem can be constructed
#guard (FieldElem.mk 42).value == 42

-- ChallengeType can be constructed
#guard (ChallengeType.mk ByteArray.empty).value == ByteArray.empty

/-! ### Label Tests -/

-- All label variants are distinct
#guard Label.vm_state != Label.challenge
#guard Label.smt_page != Label.smt_node
#guard Label.batch_commit != Label.state_digest
#guard Label.custom "a" != Label.custom "b"

/-! ### Event Distinctness Tests -/

-- Different event types are not equal
#guard Event.verify_end != Event.start_run ByteArray.empty

/-! ### TranscriptState Tests -/

-- Empty transcript has no absorptions
#guard TranscriptState.empty.absorbed == []
#guard TranscriptState.empty.squeezed == false
#guard TranscriptState.empty.chunk_index == 0

-- Init creates fresh state for chunk
#guard (TranscriptState.init 5).chunk_index == 5
#guard (TranscriptState.init 5).absorbed == []

/-! ### ExpectedInputs Tests -/

-- Empty expected inputs allows squeeze
#guard ExpectedInputs.empty.isEmpty == true
#guard ExpectedInputs.empty.pending == []

/-! ### CheckState Tests -/

-- Initial state has not seen start
#guard CheckState.initial.seen_start == false
#guard CheckState.initial.finished == false
#guard CheckState.initial.current_chunk == 0
#guard CheckState.initial.config.isNone == true
#guard CheckState.initial.last_chunk_digest.isNone == true
#guard CheckState.initial.public_inputs_buffer == []

/-! ### Event Variant Count Verification -/

/-- Verify all 9 Event variants exist by constructing each.
    This ensures the Event type matches the Jolt spec. -/
example : List Event := [
  Event.start_run ByteArray.empty,
  Event.config_resolved default,
  Event.transcript_init 0,
  Event.absorb Label.vm_state ByteArray.empty,
  Event.squeeze Label.challenge (ChallengeType.mk ByteArray.empty),
  Event.public_inputs_assembled [],
  Event.chunk_start (Digest.mk ByteArray.empty) 0,
  Event.chunk_end (Digest.mk ByteArray.empty),
  Event.verify_end
]

end Tests
