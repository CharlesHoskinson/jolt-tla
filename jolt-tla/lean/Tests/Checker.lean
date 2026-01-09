import NearFall

/-!
# Tests.Checker

Test suite for the trace checker state machine.

## Test Categories
* Step function behavior tests
* Trace validation tests
* Acceptance/rejection tests
* State transition verification

## References
* Jolt Spec §15 - Security Invariants
-/

namespace Tests.Checker

open NearFall
open NearFall.Checker

/-! ### Step Function Tests -/

-- start_run succeeds from initial state
#guard (step CheckState.initial (.start_run ByteArray.empty)).isSome == true

-- start_run fails if already seen
example : step { CheckState.initial with seen_start := true } (.start_run ByteArray.empty) = none := rfl

-- config_resolved fails from initial (no start_run yet)
#guard (step CheckState.initial (.config_resolved default)).isNone == true

-- config_resolved succeeds after start_run
example : (step { CheckState.initial with seen_start := true } (.config_resolved default)).isSome := rfl

-- verify_end succeeds from initial (not finished)
#guard (step CheckState.initial .verify_end).isSome == true

-- verify_end fails if already finished
example : step { CheckState.initial with finished := true } .verify_end = none := rfl

-- absorb always succeeds (updates transcript)
#guard (step CheckState.initial (.absorb Label.vm_state ByteArray.empty)).isSome == true

-- squeeze succeeds if expected inputs empty
#guard (step CheckState.initial (.squeeze Label.challenge (ChallengeType.mk ByteArray.empty))).isSome == true

-- squeeze fails if expected inputs not empty
example : step { CheckState.initial with expected_inputs := { pending := [Label.vm_state] } }
               (.squeeze Label.challenge (ChallengeType.mk ByteArray.empty)) = none := rfl

-- public_inputs_assembled always succeeds
#guard (step CheckState.initial (.public_inputs_assembled [])).isSome == true

-- transcript_init succeeds if chunk index matches
#guard (step CheckState.initial (.transcript_init 0)).isSome == true

-- transcript_init fails if chunk index doesn't match
#guard (step CheckState.initial (.transcript_init 1)).isNone == true

-- chunk_start with idx=0 succeeds from initial (no last digest)
#guard (step CheckState.initial (.chunk_start (Digest.mk ByteArray.empty) 0)).isSome == true

-- chunk_start with idx=1 fails from initial
#guard (step CheckState.initial (.chunk_start (Digest.mk ByteArray.empty) 1)).isNone == true

-- chunk_end always succeeds
#guard (step CheckState.initial (.chunk_end (Digest.mk ByteArray.empty))).isSome == true

/-! ### Trace Validation Tests -/

-- Empty trace is accepted
#guard (check_trace []).isSome == true
example : check_trace [] = some CheckState.initial := rfl

-- Single start_run is accepted
#guard (check_trace [.start_run ByteArray.empty]).isSome == true

-- start_run followed by config_resolved is accepted
#guard (check_trace [.start_run ByteArray.empty, .config_resolved default]).isSome == true

-- config_resolved without start_run is rejected
#guard (check_trace [.config_resolved default]).isNone == true

-- Double start_run is rejected
#guard (check_trace [.start_run ByteArray.empty, .start_run ByteArray.empty]).isNone == true

-- Double verify_end is rejected
#guard (check_trace [.verify_end, .verify_end]).isNone == true

-- start_run then verify_end is accepted
#guard (check_trace [.start_run ByteArray.empty, .verify_end]).isSome == true

/-! ### Complex Trace Tests -/

-- Valid execution sequence
#guard (check_trace [
  .start_run ByteArray.empty,
  .config_resolved default,
  .absorb Label.vm_state ByteArray.empty,
  .squeeze Label.challenge (ChallengeType.mk ByteArray.empty),
  .verify_end
]).isSome == true

-- Multiple absorbs then squeeze is valid
#guard (check_trace [
  .absorb Label.vm_state ByteArray.empty,
  .absorb Label.smt_page ByteArray.empty,
  .absorb Label.batch_commit ByteArray.empty,
  .squeeze Label.challenge (ChallengeType.mk ByteArray.empty)
]).isSome == true

-- chunk_start(0) then chunk_end is valid
#guard (check_trace [
  .chunk_start (Digest.mk ByteArray.empty) 0,
  .chunk_end (Digest.mk ByteArray.empty)
]).isSome == true

/-! ### State After Step Tests -/

-- After start_run, seen_start is true
example : ∀ next,
    step CheckState.initial (.start_run ByteArray.empty) = some next →
    next.seen_start = true := by
  intro next h
  simp only [step, CheckState.initial] at h
  split at h
  · contradiction
  · simp only [Option.some.injEq] at h
    rw [← h]

-- After verify_end, finished is true
example : ∀ next,
    step CheckState.initial .verify_end = some next →
    next.finished = true := by
  intro next h
  simp only [step, CheckState.initial] at h
  split at h
  · contradiction
  · simp only [Option.some.injEq] at h
    rw [← h]

-- After config_resolved, config is set
example : ∀ next cfg,
    step { CheckState.initial with seen_start := true } (.config_resolved cfg) = some next →
    next.config = some cfg := by
  intro next cfg h
  simp only [step, CheckState.initial, Bool.not_true, Bool.false_or, Option.isSome_none] at h
  split at h
  · contradiction
  · simp only [Option.some.injEq] at h
    rw [← h]

/-! ### is_accepted Predicate Tests -/

-- Empty trace is accepted (as Prop)
example : is_accepted [] := by
  simp only [is_accepted, check_trace, check_trace_from, Option.isSome_some]

-- Double start is not accepted
example : ¬is_accepted [.start_run ByteArray.empty, .start_run ByteArray.empty] := by
  simp only [is_accepted, check_trace, check_trace_from, step, CheckState.initial,
             ↓reduceIte, Option.isSome_none, Bool.false_eq_true, not_false_eq_true]

end Tests.Checker
