(****************************************************************************)
(* Module: Invariants.tla                                                   *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE Invariants ----
(****************************************************************************)
(* Purpose: Centralized collection of all specification invariants          *)
(* Section Reference: §15 (Security), all module constraints                *)
(* Version: 1.0                                                             *)
(* Notes: 26 individual invariants + 6 composites organized by category:    *)
(*        - INV_TYPE_*  : Type well-formedness (4, medium severity)         *)
(*        - INV_BIND_*  : Cryptographic binding (7, critical severity)      *)
(*        - INV_SAFE_*  : Protocol correctness (7, high severity)           *)
(*        - INV_ATK_*   : Attack prevention (8, critical severity)          *)
(****************************************************************************)
EXTENDS JoltSpec

(****************************************************************************)
(* TYPE INVARIANTS                                                           *)
(* Verify that all values are well-typed                                    *)
(****************************************************************************)

INV_TYPE_SystemState ==
    /\ sys.phase \in SystemPhase
    /\ sys.batchNonce \in U64

INV_TYPE_Registry == RegistryStateTypeOK(sys.registry)

INV_TYPE_VMState ==
    /\ RegisterFileTypeOK(sys.vmState.regs)
    /\ sys.vmState.pc \in U64
    /\ sys.vmState.step_counter \in StepCounter
    /\ Bytes32TypeOK(sys.vmState.rw_mem_root_bytes32)
    /\ Bytes32TypeOK(sys.vmState.io_root_bytes32)
    /\ sys.vmState.halted \in HaltedFlag
    /\ sys.vmState.exit_code \in U64

INV_TYPE_ProgramHash == sys.programHash \in Bytes32

INV_TYPE_All ==
    /\ INV_TYPE_SystemState
    /\ INV_TYPE_Registry
    /\ INV_TYPE_VMState
    /\ INV_TYPE_ProgramHash

(****************************************************************************)
(* BINDING INVARIANTS (CRITICAL)                                             *)
(* Verify that public inputs correctly reflect execution state              *)
(****************************************************************************)

INV_BIND_StatusFr ==
    sys.phase = PHASE_COMPLETE =>
        sys.publicInputs.status_fr = U64ToFr(FinalExitStatus(sys.continuation.chunks))

INV_BIND_OldRoot ==
    sys.phase = PHASE_COMPLETE =>
        LET fr2 == Bytes32ToFr2(TraceInitialState(sys.continuation.chunks).rw_mem_root_bytes32)
        IN /\ sys.publicInputs.old_root_lo = fr2.lo
           /\ sys.publicInputs.old_root_hi = fr2.hi

INV_BIND_NewRoot ==
    sys.phase = PHASE_COMPLETE =>
        LET fr2 == Bytes32ToFr2(TraceFinalState(sys.continuation.chunks).rw_mem_root_bytes32)
        IN /\ sys.publicInputs.new_root_lo = fr2.lo
           /\ sys.publicInputs.new_root_hi = fr2.hi

INV_BIND_ProgramHash ==
    sys.phase = PHASE_COMPLETE =>
        LET fr2 == Bytes32ToFr2(sys.programHash)
        IN /\ sys.publicInputs.program_hash_lo = fr2.lo
           /\ sys.publicInputs.program_hash_hi = fr2.hi

INV_BIND_ConfigTags ==
    sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} =>
        sys.vmState.config_tags = ComputeConfigTags(sys.registry)

INV_BIND_StateDigest ==
    sys.phase = PHASE_COMPLETE =>
        \A i \in 1..Len(sys.continuation.chunks) :
            sys.continuation.chunks[i].digestIn =
                ComputeStateDigest(sys.programHash, sys.continuation.chunks[i].stateIn)

INV_BIND_Nonce ==
    sys.phase = PHASE_COMPLETE =>
        /\ sys.publicInputs.batch_nonce_fr = U64ToFr(sys.batchNonce)
        /\ sys.batchNonce = ReadReg(TraceInitialState(sys.continuation.chunks), REG_A4)

INV_BIND_All ==
    /\ INV_BIND_StatusFr
    /\ INV_BIND_OldRoot
    /\ INV_BIND_NewRoot
    /\ INV_BIND_ProgramHash
    /\ INV_BIND_ConfigTags
    /\ INV_BIND_StateDigest
    /\ INV_BIND_Nonce

(****************************************************************************)
(* SAFETY INVARIANTS                                                         *)
(* Verify protocol correctness properties                                    *)
(****************************************************************************)

INV_SAFE_RegistryReady ==
    sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} =>
        RegistryDeploymentReady(sys.registry)

INV_SAFE_NoTBD ==
    sys.phase # PHASE_INIT => NoTBDInvariant(sys.registry)

INV_SAFE_VMHaltedExitCode ==
    /\ (sys.vmState.halted = 0 => sys.vmState.exit_code = 0)
    /\ (sys.vmState.halted = 1 => sys.vmState.exit_code \in 0..255)

INV_SAFE_RegisterX0 == sys.vmState.regs[0] = 0

INV_SAFE_HaltedBinary == sys.vmState.halted \in {0, 1}

INV_SAFE_ContinuationChain ==
    Len(sys.continuation.chunks) > 1 => ContinuityInvariant(sys.continuation.chunks)

INV_SAFE_FinalChunkHalted ==
    sys.phase = PHASE_COMPLETE =>
        sys.continuation.chunks[Len(sys.continuation.chunks)].stateOut.halted = 1

INV_SAFE_All ==
    /\ INV_SAFE_RegistryReady
    /\ INV_SAFE_NoTBD
    /\ INV_SAFE_VMHaltedExitCode
    /\ INV_SAFE_RegisterX0
    /\ INV_SAFE_HaltedBinary
    /\ INV_SAFE_ContinuationChain
    /\ INV_SAFE_FinalChunkHalted

(****************************************************************************)
(* ATTACK PREVENTION INVARIANTS (CRITICAL)                                   *)
(* Each invariant prevents a specific attack vector                          *)
(****************************************************************************)

\* INV_ATK_NoPrefixProof: Prevents accepting incomplete execution
\* Attack: Prover proves first half of execution, skips critical logic
INV_ATK_NoPrefixProof ==
    sys.phase = PHASE_COMPLETE =>
        LET finalState == TraceFinalState(sys.continuation.chunks)
        IN /\ (sys.publicInputs.status_fr = U64ToFr(JOLT_STATUS_OK) =>
                  /\ IsSuccessfulHalt(finalState)
                  /\ finalState.halted = 1)
           /\ (IsSuccessfulHalt(finalState) /\ finalState.halted = 1 =>
                  sys.publicInputs.status_fr = U64ToFr(JOLT_STATUS_OK))

\* INV_ATK_NoSkipChunk: Prevents skipping chunks in sequence
\* Attack: Prover omits chunk containing critical logic
INV_ATK_NoSkipChunk == NoSkippedChunks(sys.continuation.chunks)

\* INV_ATK_NoSplice: Prevents splicing different executions
\* Attack: Prover mixes chunks from execution A and B
INV_ATK_NoSplice ==
    sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} =>
        ContinuityInvariant(sys.continuation.chunks)

\* INV_ATK_NoCrossConfig: Prevents using wrong configuration
\* Attack: Prove with permissive config, verify with strict
INV_ATK_NoCrossConfig ==
    sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} =>
        ConfigConsistentAcrossChunks(sys.continuation.chunks)

\* INV_ATK_NoRootForgery: Prevents forging memory state
\* Attack: Claim false initial/final memory state
INV_ATK_NoRootForgery ==
    sys.phase = PHASE_COMPLETE =>
        /\ INV_BIND_OldRoot
        /\ INV_BIND_NewRoot

\* INV_ATK_NoMemoryForgery: Prevents forging RW memory between chunks
\* Attack: Manipulate read-write memory root at chunk boundary
INV_ATK_NoMemoryForgery ==
    sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} =>
        \A i \in 1..(Len(sys.continuation.chunks) - 1) :
            sys.continuation.chunks[i].stateOut.rw_mem_root_bytes32 =
                sys.continuation.chunks[i+1].stateIn.rw_mem_root_bytes32

\* INV_ATK_NoIOForgery: Prevents forging IO memory between chunks
\* Attack: Manipulate input/output memory root at chunk boundary
INV_ATK_NoIOForgery ==
    sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} =>
        \A i \in 1..(Len(sys.continuation.chunks) - 1) :
            sys.continuation.chunks[i].stateOut.io_root_bytes32 =
                sys.continuation.chunks[i+1].stateIn.io_root_bytes32

\* INV_ATK_NoReplay: Prevents replaying old proofs
\* Attack: Reuse proof from different batch
INV_ATK_NoReplay ==
    sys.phase = PHASE_COMPLETE =>
        sys.publicInputs.batch_nonce_fr =
            U64ToFr(ReadReg(TraceInitialState(sys.continuation.chunks), REG_A4))

INV_ATK_All ==
    /\ INV_ATK_NoPrefixProof
    /\ INV_ATK_NoSkipChunk
    /\ INV_ATK_NoSplice
    /\ INV_ATK_NoCrossConfig
    /\ INV_ATK_NoRootForgery
    /\ INV_ATK_NoMemoryForgery
    /\ INV_ATK_NoIOForgery
    /\ INV_ATK_NoReplay

(****************************************************************************)
(* COMPOSITE INVARIANTS                                                      *)
(****************************************************************************)

AllInvariants ==
    /\ INV_TYPE_All
    /\ INV_BIND_All
    /\ INV_SAFE_All
    /\ INV_ATK_All

CriticalInvariants ==
    /\ INV_BIND_StatusFr
    /\ INV_BIND_OldRoot
    /\ INV_BIND_NewRoot
    /\ INV_SAFE_ContinuationChain
    /\ INV_ATK_NoPrefixProof
    /\ INV_ATK_NoSkipChunk
    /\ INV_ATK_NoSplice

(****************************************************************************)
(* LIVENESS PROPERTIES                                                       *)
(****************************************************************************)

LIVE_EventuallyTerminates == <>(sys.phase \in {PHASE_COMPLETE, PHASE_FAILED})
LIVE_ProgressFromInit == (sys.phase = PHASE_INIT) ~> (sys.phase # PHASE_INIT)

====
