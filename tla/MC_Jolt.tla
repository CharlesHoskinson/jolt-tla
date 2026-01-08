(****************************************************************************)
(* Module: MC_Jolt.tla                                                      *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE MC_Jolt ----
(****************************************************************************)
(* Purpose: TLC Model Configuration for Jolt Specification                  *)
(* Usage: Use this module as the TLC "model" with JoltSpec                  *)
(* Version: 1.0                                                             *)
(* Notes: Provides concrete values for abstract constants, model operators  *)
(*        for hash functions, and state constraints for bounded checking.   *)
(****************************************************************************)
EXTENDS Invariants, TLC, Sequences

(****************************************************************************)
(* SMOKE TEST CONFIGURATION                                                  *)
(* Small values for fast TLC runs                                            *)
(****************************************************************************)

SMOKE_CHUNK_MAX_STEPS == 2
SMOKE_MAX_CHUNKS == 3
SMOKE_NUM_REGISTERS == 32
SMOKE_FR_MODULUS == 1000
SMOKE_FR_TLC_BOUND == 16384
SMOKE_U64_TLC_BOUND == 16384
SMOKE_PAGE_INDEX_TLC_BOUND == 4
SMOKE_MAX_DIRTY_PAGES == 2
SMOKE_MAX_ABSORPTIONS == 4

(****************************************************************************)
(* Domain Tag Strings (JOLT/ prefix)                                         *)
(****************************************************************************)

SMOKE_TAG_STRINGS == {
    "JOLT/SMT/PAGE/V1", "JOLT/SMT/NODE/V1", "JOLT/TRANSCRIPT/VM_STATE/V1",
    "JOLT/TRANSCRIPT/CHALLENGE/V1", "JOLT/TRANSCRIPT/V1",
    "JOLT/BATCH/HEADER_LEAF/V1", "JOLT/BATCH/FILL_LEAF/V1", "JOLT/BATCH/EMPTY_FILL_LEAF/V1",
    "JOLT/BATCH/PAD_LEAF/V1", "JOLT/BATCH/NODE/V1", "JOLT/STATE/V1", "JOLT/CHECKPOINTS/V1",
    "JOLT/BATCH/COMMIT/V1", "JOLT/CHECKPOINTS/DIGEST/V1", "JOLT/IO/INIT/V1",
    "JOLT/CONFIG_TAGS/V1", "JOLT/TAG/V1"
}

(****************************************************************************)
(* HASH FUNCTION MODEL OPERATORS                                             *)
(* These use simple arithmetic to ensure different inputs produce different *)
(* outputs while staying within TLC's bounds. NOT production algorithms!    *)
(****************************************************************************)

ValueFingerprint(x) == IF x \in Nat THEN x ELSE Len(ToString(x))

TagToNat(tag) ==
    CASE tag = "JOLT/SMT/PAGE/V1" -> 1
      [] tag = "JOLT/SMT/NODE/V1" -> 2
      [] tag = "JOLT/STATE/V1" -> 3
      [] tag = "JOLT/TRANSCRIPT/CHALLENGE/V1" -> 4
      [] tag = "JOLT/TRANSCRIPT/VM_STATE/V1" -> 5
      [] tag = "JOLT/CHECKPOINTS/V1" -> 6
      [] tag = "JOLT/BATCH/HEADER_LEAF/V1" -> 7
      [] tag = "JOLT/BATCH/FILL_LEAF/V1" -> 8
      [] tag = "JOLT/BATCH/EMPTY_FILL_LEAF/V1" -> 9
      [] tag = "JOLT/BATCH/PAD_LEAF/V1" -> 10
      [] tag = "JOLT/BATCH/NODE/V1" -> 11
      [] tag = "JOLT/TRANSCRIPT/V1" -> 12
      [] tag = "JOLT/BATCH/COMMIT/V1" -> 13
      [] tag = "JOLT/CHECKPOINTS/DIGEST/V1" -> 14
      [] tag = "JOLT/IO/INIT/V1" -> 15
      [] tag = "JOLT/CONFIG_TAGS/V1" -> 16
      [] tag = "JOLT/TAG/V1" -> 17
      [] OTHER -> 0

ModelPoseidonHashBytes(tag, data) ==
    (TagToNat(tag) * 100000 + ValueFingerprint(data)) % FR_TLC_BOUND

ModelPoseidonHashFr2(tag, fr1, fr2) ==
    (TagToNat(tag) * 100000 + fr1 * 257 + fr2) % FR_TLC_BOUND

ModelSHA256Hash(input) ==
    [i \in 0..31 |-> (ValueFingerprint(input) + i * 17) % 256]

ModelDefaultHashes == [d \in 0..32 |-> (d * 17 + 1) % FR_TLC_BOUND]

(****************************************************************************)
(* POSEIDON PARAMETERS (§3.4.1)                                              *)
(* JOLT_POSEIDON_FR_V1 concrete parameter values for model checking          *)
(****************************************************************************)

\* Poseidon parameters (t, r, c naming convention per §3.4.1)
POSEIDON_T == 3                            \* State width: t = 3
POSEIDON_R == 2                            \* Rate: r = 2
POSEIDON_C == 1                            \* Capacity: c = 1

\* Validate Poseidon parameter consistency with Hash.tla definitions
ASSUME POSEIDON_T = POSEIDON_WIDTH
ASSUME POSEIDON_R = POSEIDON_RATE
ASSUME POSEIDON_C = POSEIDON_CAPACITY
ASSUME POSEIDON_FULL_ROUNDS = 8
ASSUME POSEIDON_PARTIAL_ROUNDS = 60
ASSUME POSEIDON_T = POSEIDON_R + POSEIDON_C

(****************************************************************************)
(* STATE CONSTRAINTS                                                         *)
(* Bounds on exploration to keep TLC tractable                               *)
(****************************************************************************)

VM_TERMINATE_AFTER_STEPS == CHUNK_MAX_STEPS * (MAX_CHUNKS + 1)

ModelStepFn(state) ==
    IF state.halted = 1 THEN state
    ELSE LET nextCounter == state.step_counter + 1
             nextHalted == IF nextCounter >= VM_TERMINATE_AFTER_STEPS THEN 1 ELSE 0
         IN [state EXCEPT !.step_counter = nextCounter,
                          !.halted = nextHalted,
                          !.exit_code = 0]

StateConstraint ==
    /\ Len(sys.continuation.chunks) <= MAX_CHUNKS + 1
    /\ sys.vmState.step_counter <= CHUNK_MAX_STEPS * (MAX_CHUNKS + 2)

(****************************************************************************)
(* MODEL INIT                                                                *)
(* Concrete initial values for model checking                                *)
(****************************************************************************)

ModelBytes32 == [i \in 0..31 |-> 0]

ModelValueForKey(keyName) ==
    CASE keyName = KEY_SPEC_VERSION -> "1.0.0"
      [] keyName = KEY_MAX_MANIFEST_BYTES -> "512"
      [] keyName = KEY_MAX_INTENTS -> "8"
      [] keyName = KEY_MAX_CHECKPOINTS_BYTES -> "256"
      [] keyName = KEY_CONTEXT_BYTES32 -> "CONTEXT1"
      [] OTHER -> "1.0.0"

ModelRegistryEntry(keyName) ==
    [key |-> keyName,
     value |-> ModelValueForKey(keyName),
     required |-> TRUE,
     validated |-> TRUE]

ModelRegistry == [k \in RequiredKeys |-> ModelRegistryEntry(k)]

ModelInit == sys = InitSystemState(ModelRegistry, ModelBytes32, << >>, 0)

ModelSpec == ModelInit /\ [][Next]_sys

ModelFairSpec ==
    ModelSpec
    /\ WF_sys(StartExecution)
    /\ WF_sys(ExecuteOneChunk)
    /\ WF_sys(CompleteExecution)
    /\ WF_sys(ExecutionFailed)

====
