(****************************************************************************)
(* Module: MC_BadChain_Splice.tla                                          *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE MC_BadChain_Splice ----
(****************************************************************************)
(* Purpose: Non-vacuity test for INV_ATK_NoSplice                           *)
(* Pattern: B (invariant should catch bad accepted state)                   *)
(* Expected: TLC FAILS with invariant violation                             *)
(*                                                                          *)
(* Attack scenario: Prover splices chunks from two different executions.    *)
(* The chunks have different digestIn/digestOut values, breaking continuity.*)
(* INV_ATK_NoSplice must detect this and prevent the bad state.             *)
(****************************************************************************)
EXTENDS MC_Jolt

(****************************************************************************)
(* BAD INIT: Start in phase=COMPLETE with broken chain continuity           *)
(* This tests that INV_ATK_NoSplice is non-vacuous                          *)
(****************************************************************************)

BadChunk1 ==
    [chunkIndex |-> 0,
     program_hash |-> ModelBytes32,
     stateIn |-> InitVMState(INPUT_PTR, 0, OUTPUT_PTR, PUBLIC_OUTPUTS_SIZE, 0, STACK_PTR,
                             RootToBytes32(EmptyTreeRoot), RootToBytes32(EmptyTreeRoot),
                             ComputeConfigTags(ModelRegistry)),
     stateOut |-> InitVMState(INPUT_PTR, 0, OUTPUT_PTR, PUBLIC_OUTPUTS_SIZE, 0, STACK_PTR,
                              RootToBytes32(EmptyTreeRoot), RootToBytes32(EmptyTreeRoot),
                              ComputeConfigTags(ModelRegistry)),
     digestIn |-> 100,
     digestOut |-> 200,  \* This should chain to next chunk's digestIn
     isFinal |-> FALSE]

BadChunk2 ==
    [chunkIndex |-> 1,
     program_hash |-> ModelBytes32,
     stateIn |-> InitVMState(INPUT_PTR, 0, OUTPUT_PTR, PUBLIC_OUTPUTS_SIZE, 0, STACK_PTR,
                             RootToBytes32(EmptyTreeRoot), RootToBytes32(EmptyTreeRoot),
                             ComputeConfigTags(ModelRegistry)),
     stateOut |-> [InitVMState(INPUT_PTR, 0, OUTPUT_PTR, PUBLIC_OUTPUTS_SIZE, 0, STACK_PTR,
                               RootToBytes32(EmptyTreeRoot), RootToBytes32(EmptyTreeRoot),
                               ComputeConfigTags(ModelRegistry)) EXCEPT !.halted = 1],
     digestIn |-> 999,   \* BROKEN: doesn't match BadChunk1.digestOut (200)
     digestOut |-> 300,
     isFinal |-> TRUE]

\* Bad continuation with broken chain (splice attack)
BadContinuation ==
    [chunks |-> <<BadChunk1, BadChunk2>>,
     complete |-> TRUE,
     chunkCount |-> 2]

\* Start in COMPLETE phase with broken chain
BadInit ==
    sys = [phase |-> PHASE_COMPLETE,
           registry |-> ModelRegistry,
           programHash |-> ModelBytes32,
           vmState |-> BadChunk2.stateOut,
           continuation |-> BadContinuation,
           publicInputs |-> [program_hash_lo |-> 0, program_hash_hi |-> 0,
                             old_root_lo |-> 0, old_root_hi |-> 0,
                             new_root_lo |-> 0, new_root_hi |-> 0,
                             batch_commitment_lo |-> 0, batch_commitment_hi |-> 0,
                             checkpoints_digest_fr |-> 0, status_fr |-> 0, batch_nonce_fr |-> 0],
           publicOutputs |-> TrapOutputs(0, 0),
           batchNonce |-> 0,
           manifestBytes |-> << >>]

\* No transitions - just check initial state
BadNext == UNCHANGED sys

BadSpec == BadInit /\ [][BadNext]_sys

(****************************************************************************)
(* INVARIANT TO CHECK                                                        *)
(* TLC should find this invariant VIOLATED                                   *)
(****************************************************************************)

\* The attack invariant should catch the broken chain
CheckSpliceDetected == INV_ATK_NoSplice

====
