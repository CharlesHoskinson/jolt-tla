(****************************************************************************)
(* Module: JoltSpec.tla                                                     *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE JoltSpec ----
(****************************************************************************)
(* Purpose: Top-level composition of Jolt TLA+ specification                *)
(* Section Reference: All sections - integrated system behavior             *)
(* Version: 1.0                                                             *)
(* Notes: Complete state machine from initialization through execution to   *)
(*        completion or failure. Init/Next/Spec define the temporal spec.   *)
(****************************************************************************)
EXTENDS Wrapper, Registry, Naturals, Sequences, FiniteSets

(****************************************************************************)
(* Memory Layout Constants                                                   *)
(****************************************************************************)

INPUT_PTR == IO_REGION_BASE
OUTPUT_PTR == IO_REGION_BASE + (2 * PAGE_SIZE_BYTES)
STACK_PTR == RW_REGION_BASE + RW_REGION_SIZE

(****************************************************************************)
(* Domain Tags (transformed from NF/ to JOLT/)                               *)
(****************************************************************************)

TAG_BATCH_COMMITMENT == "JOLT/BATCH/COMMIT/V1"
TAG_CHECKPOINTS_DIGEST == "JOLT/CHECKPOINTS/DIGEST/V1"
TAG_IO_INIT == "JOLT/IO/INIT/V1"

(****************************************************************************)
(* Batch and Checkpoint Digest Computation                                   *)
(****************************************************************************)

BatchCommitmentBytes32(manifestBytes) ==
    IF Len(manifestBytes) = 0
    THEN ZeroBytes32
    ELSE SHA256Hash(manifestBytes)

CheckpointsDigestFr(trace) ==
    IF Len(trace) = 0 THEN 0
    ELSE PoseidonHashBytes(TAG_CHECKPOINTS_DIGEST, SumSet({trace[i].digestOut : i \in 1..Len(trace)}))

CheckpointsDigestBytes32(trace) == FrToBytes32LE(CheckpointsDigestFr(trace))

(****************************************************************************)
(* System Phases                                                             *)
(* The system progresses: INIT -> EXECUTING -> COMPLETE or FAILED           *)
(****************************************************************************)

PHASE_INIT == "init"
PHASE_EXECUTING == "executing"
PHASE_COMPLETE == "complete"
PHASE_FAILED == "failed"

SystemPhase == {PHASE_INIT, PHASE_EXECUTING, PHASE_COMPLETE, PHASE_FAILED}

(****************************************************************************)
(* SystemState: Complete system record                                       *)
(****************************************************************************)

SystemState == [
    phase: SystemPhase,
    registry: RegistryState,
    programHash: Bytes32,
    vmState: VMStateV1,
    continuation: ContinuationState,
    publicInputs: PublicInputsV1,
    publicOutputs: PublicOutputsV1,
    batchNonce: U64,
    manifestBytes: Seq(Byte)]

VARIABLE sys

(****************************************************************************)
(* InitSystemState: Create initial system state                              *)
(****************************************************************************)

InitSystemState(registry, programHash, manifestBytes, batchNonce) ==
    LET configTags == ComputeConfigTags(registry)
        initialRWRoot == RootToBytes32(EmptyTreeRoot)
        initialIORoot == RootToBytes32(ComputeInitialIORoot(manifestBytes, INPUT_PTR, Len(manifestBytes), IO_REGION_BASE))
        initVM == InitVMState(INPUT_PTR, Len(manifestBytes), OUTPUT_PTR, PUBLIC_OUTPUTS_SIZE, batchNonce, STACK_PTR,
                              initialRWRoot, initialIORoot, configTags)
    IN [phase |-> PHASE_INIT,
        registry |-> registry,
        programHash |-> programHash,
        vmState |-> initVM,
        continuation |-> InitContinuation(programHash, initVM),
        publicInputs |-> [program_hash_lo |-> 0, program_hash_hi |-> 0,
                          old_root_lo |-> 0, old_root_hi |-> 0,
                          new_root_lo |-> 0, new_root_hi |-> 0,
                          batch_commitment_lo |-> 0, batch_commitment_hi |-> 0,
                          checkpoints_digest_fr |-> 0, status_fr |-> 0, batch_nonce_fr |-> 0],
        publicOutputs |-> TrapOutputs(0, batchNonce),
        batchNonce |-> batchNonce,
        manifestBytes |-> manifestBytes]

(****************************************************************************)
(* Init: Initial state predicate                                             *)
(****************************************************************************)

Init == \E registry \in RegistryState, programHash \in Bytes32, batchNonce \in U64 :
    /\ RegistryDeploymentReady(registry)
    /\ sys = InitSystemState(registry, programHash, << >>, batchNonce)

(****************************************************************************)
(* State Transitions                                                         *)
(* Four possible transitions at each step                                    *)
(****************************************************************************)

\* Transition 1: Start execution (INIT -> EXECUTING)
StartExecution ==
    /\ sys.phase = PHASE_INIT
    /\ RegistryDeploymentReady(sys.registry)
    /\ sys' = [sys EXCEPT !.phase = PHASE_EXECUTING]

\* Transition 2: Execute one chunk (stay in EXECUTING)
ExecuteOneChunk ==
    /\ sys.phase = PHASE_EXECUTING
    /\ ~ContinuationComplete(sys.continuation)
    /\ LET stateIn == sys.vmState
           stateOut == ExecuteNSteps(stateIn, CHUNK_MAX_STEPS)
           newCont == ExecuteChunk(sys.continuation, stateIn, stateOut)
       IN sys' = [sys EXCEPT !.vmState = stateOut, !.continuation = newCont]

\* Transition 3: Complete execution (EXECUTING -> COMPLETE)
CompleteExecution ==
    /\ sys.phase = PHASE_EXECUTING
    /\ ContinuationComplete(sys.continuation)
    /\ LET trace == sys.continuation.chunks
           outputs == [status_u8 |-> TraceFinalState(trace).exit_code % 256,
                       reserved7 |-> ZeroReserved7,
                       batch_nonce_u64 |-> sys.batchNonce,
                       old_root_bytes32 |-> OldStateRoot(trace),
                       new_root_bytes32 |-> NewStateRoot(trace),
                       batch_commitment_bytes32 |-> BatchCommitmentBytes32(sys.manifestBytes),
                       checkpoints_digest_bytes32 |-> CheckpointsDigestBytes32(trace)]
           wrapperInput == [program_hash_bytes32 |-> sys.programHash,
                            executionTrace |-> trace,
                            publicOutputs |-> outputs,
                            batch_nonce_in |-> sys.batchNonce]
       IN sys' = [sys EXCEPT !.phase = PHASE_COMPLETE,
                             !.publicInputs = ConstructPublicInputs(wrapperInput),
                             !.publicOutputs = outputs]

\* Transition 4: Execution failed (EXECUTING -> FAILED)
ExecutionFailed ==
    /\ sys.phase = PHASE_EXECUTING
    /\ IsTrappedHalt(sys.vmState)
    /\ sys' = [sys EXCEPT !.phase = PHASE_FAILED,
                          !.publicOutputs = TrapOutputs(sys.vmState.exit_code, sys.batchNonce)]

(****************************************************************************)
(* Next: Disjunction of all transitions                                      *)
(****************************************************************************)

Next == \/ StartExecution
        \/ ExecuteOneChunk
        \/ CompleteExecution
        \/ ExecutionFailed

Stuttering == UNCHANGED sys
NextOrStutter == Next \/ Stuttering

(****************************************************************************)
(* Temporal Specification                                                    *)
(* Spec: "Start in Init, then forever apply Next or stutter"                *)
(****************************************************************************)

Spec == Init /\ [][Next]_sys
FairSpec == Spec /\ WF_sys(ExecuteOneChunk)

====
