(****************************************************************************)
(* Module: MC_BadChain_Skip.tla                                            *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE MC_BadChain_Skip ----
(****************************************************************************)
(* Purpose: Non-vacuity test for INV_ATK_NoSkipChunk                        *)
(* Pattern: B (invariant should catch bad accepted state)                   *)
(* Expected: TLC FAILS with invariant violation                             *)
(*                                                                          *)
(* Attack scenario: Prover skips chunk containing critical logic.           *)
(* Chunks have non-sequential indices (0, 2) instead of (0, 1, 2).          *)
(* INV_ATK_NoSkipChunk must detect this.                                    *)
(****************************************************************************)
EXTENDS MC_Jolt

(****************************************************************************)
(* BAD INIT: Start in phase=COMPLETE with skipped chunk                     *)
(* Chunk indices jump from 0 to 2 (skipping 1)                              *)
(****************************************************************************)

SkipChunk1 ==
    [chunkIndex |-> 0,  \* First chunk
     program_hash |-> ModelBytes32,
     stateIn |-> InitVMState(INPUT_PTR, 0, OUTPUT_PTR, PUBLIC_OUTPUTS_SIZE, 0, STACK_PTR,
                             RootToBytes32(EmptyTreeRoot), RootToBytes32(EmptyTreeRoot),
                             ComputeConfigTags(ModelRegistry)),
     stateOut |-> InitVMState(INPUT_PTR, 0, OUTPUT_PTR, PUBLIC_OUTPUTS_SIZE, 0, STACK_PTR,
                              RootToBytes32(EmptyTreeRoot), RootToBytes32(EmptyTreeRoot),
                              ComputeConfigTags(ModelRegistry)),
     digestIn |-> 100,
     digestOut |-> 200,
     isFinal |-> FALSE]

SkipChunk2 ==
    [chunkIndex |-> 2,  \* SKIPPED: should be 1, but is 2
     program_hash |-> ModelBytes32,
     stateIn |-> InitVMState(INPUT_PTR, 0, OUTPUT_PTR, PUBLIC_OUTPUTS_SIZE, 0, STACK_PTR,
                             RootToBytes32(EmptyTreeRoot), RootToBytes32(EmptyTreeRoot),
                             ComputeConfigTags(ModelRegistry)),
     stateOut |-> [InitVMState(INPUT_PTR, 0, OUTPUT_PTR, PUBLIC_OUTPUTS_SIZE, 0, STACK_PTR,
                               RootToBytes32(EmptyTreeRoot), RootToBytes32(EmptyTreeRoot),
                               ComputeConfigTags(ModelRegistry)) EXCEPT !.halted = 1],
     digestIn |-> 200,  \* Properly chained digestIn
     digestOut |-> 300,
     isFinal |-> TRUE]

\* Continuation with skipped chunk (chunk 1 is missing)
SkipContinuation ==
    [chunks |-> <<SkipChunk1, SkipChunk2>>,
     complete |-> TRUE,
     chunkCount |-> 2]

\* Start in COMPLETE phase with skipped chunk
SkipBadInit ==
    sys = [phase |-> PHASE_COMPLETE,
           registry |-> ModelRegistry,
           programHash |-> ModelBytes32,
           vmState |-> SkipChunk2.stateOut,
           continuation |-> SkipContinuation,
           publicInputs |-> [program_hash_lo |-> 0, program_hash_hi |-> 0,
                             old_root_lo |-> 0, old_root_hi |-> 0,
                             new_root_lo |-> 0, new_root_hi |-> 0,
                             batch_commitment_lo |-> 0, batch_commitment_hi |-> 0,
                             checkpoints_digest_fr |-> 0, status_fr |-> 0, batch_nonce_fr |-> 0],
           publicOutputs |-> TrapOutputs(0, 0),
           batchNonce |-> 0,
           manifestBytes |-> << >>]

\* No transitions - just check initial state
SkipBadNext == UNCHANGED sys

SkipBadSpec == SkipBadInit /\ [][SkipBadNext]_sys

(****************************************************************************)
(* INVARIANT TO CHECK                                                        *)
(* TLC should find this invariant VIOLATED                                   *)
(****************************************************************************)

\* The attack invariant should catch the skipped chunk
CheckSkipDetected == INV_ATK_NoSkipChunk

====
