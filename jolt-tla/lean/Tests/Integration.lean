import NearFall

/-!
# Tests.Integration

Integration tests for end-to-end trace validation.

## Test Categories
* Valid trace examples
* Invalid trace examples (rejection tests)
* Security property verification
* Soundness theorem application

## References
* Jolt Spec §1-§15 - Full execution model
-/

namespace Tests.Integration

open NearFall
open NearFall.Checker
open NearFall.Transcript
open NearFall.Soundness

/-! ### Valid Trace Examples -/

/-- Minimal valid trace: just verify_end -/
def minimalTrace : Trace := [.verify_end]
#guard (check_trace minimalTrace).isSome == true

/-- Simple execution: start, config, verify -/
def simpleExecution : Trace := [
  .start_run ByteArray.empty,
  .config_resolved default,
  .verify_end
]
#guard (check_trace simpleExecution).isSome == true

/-- Execution with transcript operations -/
def transcriptExecution : Trace := [
  .start_run ByteArray.empty,
  .config_resolved default,
  .transcript_init 0,
  .absorb Label.vm_state ByteArray.empty,
  .absorb Label.smt_page ByteArray.empty,
  .squeeze Label.challenge (ChallengeType.mk ByteArray.empty),
  .verify_end
]
#guard (check_trace transcriptExecution).isSome == true

/-- Execution with chunk operations -/
def chunkExecution : Trace := [
  .start_run ByteArray.empty,
  .chunk_start (Digest.mk ByteArray.empty) 0,
  .absorb Label.vm_state ByteArray.empty,
  .chunk_end (Digest.mk ByteArray.empty),
  .verify_end
]
#guard (check_trace chunkExecution).isSome == true

/-- Execution with public inputs -/
def publicInputsExecution : Trace := [
  .start_run ByteArray.empty,
  .config_resolved default,
  .public_inputs_assembled [FieldElem.mk 1, FieldElem.mk 2, FieldElem.mk 3],
  .verify_end
]
#guard (check_trace publicInputsExecution).isSome == true

/-! ### Invalid Trace Examples (Rejection Tests) -/

/-- Rejected: config before start -/
def configBeforeStart : Trace := [
  .config_resolved default,
  .start_run ByteArray.empty
]
#guard (check_trace configBeforeStart).isNone == true

/-- Rejected: double start_run -/
def doubleStart : Trace := [
  .start_run ByteArray.empty,
  .start_run ByteArray.empty
]
#guard (check_trace doubleStart).isNone == true

/-- Rejected: double verify_end -/
def doubleVerify : Trace := [
  .verify_end,
  .verify_end
]
#guard (check_trace doubleVerify).isNone == true

/-- Rejected: double config -/
def doubleConfig : Trace := [
  .start_run ByteArray.empty,
  .config_resolved default,
  .config_resolved default
]
#guard (check_trace doubleConfig).isNone == true

/-- Rejected: wrong chunk index -/
def wrongChunkIndex : Trace := [
  .chunk_start (Digest.mk ByteArray.empty) 1  -- Should be 0 for first chunk
]
#guard (check_trace wrongChunkIndex).isNone == true

/-- Rejected: wrong transcript_init index -/
def wrongTranscriptIndex : Trace := [
  .transcript_init 5  -- Should be 0 initially
]
#guard (check_trace wrongTranscriptIndex).isNone == true

/-! ### Security Property Tests -/

/-- Test: soundness theorem provides security obligations -/
example : SecurityObligations := soundness

/-- Test: no_double_start is enforced -/
example : ∀ (state : CheckState) (rid : ByteArray),
    state.seen_start = true →
    step state (.start_run rid) = none :=
  soundness.no_double_start_enforced

/-- Test: no_double_verify is enforced -/
example : ∀ (state : CheckState),
    state.finished = true →
    step state .verify_end = none :=
  soundness.no_double_verify_enforced

/-- Test: no_early_squeeze is enforced -/
example : ∀ (state : CheckState) (label : Label) (ch : ChallengeType),
    state.expected_inputs.isEmpty = false →
    step state (.squeeze label ch) = none :=
  soundness.no_early_squeeze_enforced

/-- Test: config_after_start is enforced -/
example : ∀ (state : CheckState) (cfg : ConfigType),
    state.seen_start = false →
    step state (.config_resolved cfg) = none :=
  soundness.config_after_start_enforced

/-! ### Trace Composition Tests -/

/-- Test: empty trace concatenation -/
example : check_trace_from CheckState.initial ([] ++ [.verify_end]) =
          check_trace_from CheckState.initial [.verify_end] := rfl

/-- Test: trace_concat theorem application -/
example : ∀ (s1 s2 s3 : CheckState),
    check_trace_from s1 [] = some s2 →
    check_trace_from s2 [.verify_end] = some s3 →
    check_trace_from s1 ([] ++ [.verify_end]) = some s3 :=
  trace_concat [] [.verify_end]

/-! ### State Monotonicity Tests -/

/-- Test: seen_start monotone property -/
example : ∀ (state next : CheckState) (e : Event),
    step state e = some next →
    state.seen_start = true →
    next.seen_start = true :=
  seen_start_monotone

/-- Test: finished rejects verify -/
example : ∀ (state : CheckState),
    state.finished = true →
    step state .verify_end = none :=
  finished_rejects_verify

/-! ### Prefix Validity Tests -/

/-- Test: accepted prefix theorem -/
example : ∀ (e : Event) (rest : Trace) (final : CheckState),
    check_trace_from CheckState.initial (e :: rest) = some final →
    ∃ next, step CheckState.initial e = some next ∧
            check_trace_from next rest = some final :=
  accepted_prefix_valid CheckState.initial

/-! ### Decidability Tests -/

-- is_accepted is decidable
#guard (decide (is_accepted [])) == true
#guard (decide (is_accepted [.start_run ByteArray.empty])) == true
#guard (decide (is_accepted [.start_run ByteArray.empty, .start_run ByteArray.empty])) == false

end Tests.Integration
