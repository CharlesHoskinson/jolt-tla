(****************************************************************************)
(* Module: Wrapper.tla                                                      *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE Wrapper ----
(****************************************************************************)
(* Purpose: Halo2 wrapper circuit and public input constraints              *)
(* Section Reference: §5 (Wrapper proof interface and public inputs)        *)
(* Version: 1.0                                                             *)
(* Notes: Defines the 11 public inputs and 6 binding constraints that       *)
(*        constitute the wrapper proof statement.                           *)
(****************************************************************************)
EXTENDS Continuations, Encodings, Sequences

ASSUME U64_TLC_BOUND <= FR_TLC_BOUND
U64ToFr(u) == u

(****************************************************************************)
(* PublicInputsV1: The 11 Fr values exposed to on-chain verifier            *)
(* These are the only values the verifier sees; all else is hidden          *)
(****************************************************************************)

PublicInputsV1 == [
    program_hash_lo: Fr, program_hash_hi: Fr,
    old_root_lo: Fr, old_root_hi: Fr,
    new_root_lo: Fr, new_root_hi: Fr,
    batch_commitment_lo: Fr, batch_commitment_hi: Fr,
    checkpoints_digest_fr: Fr, status_fr: Fr, batch_nonce_fr: Fr]

(****************************************************************************)
(* PublicOutputsV1: The 144-byte structure in guest output buffer           *)
(* Written by Settlement Engine, read by wrapper circuit                    *)
(****************************************************************************)

PublicOutputsV1 == [
    status_u8: Byte, reserved7: [0..6 -> Byte], batch_nonce_u64: U64,
    old_root_bytes32: Bytes32, new_root_bytes32: Bytes32,
    batch_commitment_bytes32: Bytes32, checkpoints_digest_bytes32: Bytes32]

PUBLIC_OUTPUTS_SIZE == 144
ZeroReserved7 == [i \in 0..6 |-> 0]

(****************************************************************************)
(* Type Predicates                                                           *)
(****************************************************************************)

PublicOutputsTypeOK(outputs) ==
    /\ outputs.status_u8 \in Byte
    /\ DOMAIN outputs.reserved7 = 0..6 /\ \A i \in 0..6 : outputs.reserved7[i] \in Byte
    /\ outputs.batch_nonce_u64 \in U64
    /\ Bytes32TypeOK(outputs.old_root_bytes32) /\ Bytes32TypeOK(outputs.new_root_bytes32)
    /\ Bytes32TypeOK(outputs.batch_commitment_bytes32) /\ Bytes32TypeOK(outputs.checkpoints_digest_bytes32)

PublicInputsTypeOK(inputs) ==
    /\ inputs.program_hash_lo \in Fr /\ inputs.program_hash_hi \in Fr
    /\ inputs.old_root_lo \in Fr /\ inputs.old_root_hi \in Fr
    /\ inputs.new_root_lo \in Fr /\ inputs.new_root_hi \in Fr
    /\ inputs.batch_commitment_lo \in Fr /\ inputs.batch_commitment_hi \in Fr
    /\ inputs.checkpoints_digest_fr \in Fr /\ inputs.status_fr \in Fr /\ inputs.batch_nonce_fr \in Fr

IsTrapOutput(outputs) ==
    /\ outputs.old_root_bytes32 = ZeroBytes32 /\ outputs.new_root_bytes32 = ZeroBytes32
    /\ outputs.batch_commitment_bytes32 = ZeroBytes32 /\ outputs.checkpoints_digest_bytes32 = ZeroBytes32

(****************************************************************************)
(* Wrapper Input Structure                                                   *)
(****************************************************************************)

WrapperInput == [program_hash_bytes32: Bytes32, executionTrace: ExecutionTrace,
                 publicOutputs: PublicOutputsV1, batch_nonce_in: U64]

(****************************************************************************)
(* ConstructPublicInputs: Build 11 public inputs from execution             *)
(* This is the critical function that maps execution to verifiable outputs  *)
(****************************************************************************)

ConstructPublicInputs(input) ==
    LET progHashFr2 == Bytes32ToFr2(input.program_hash_bytes32)
        oldRootFr2 == Bytes32ToFr2(OldStateRoot(input.executionTrace))
        newRootFr2 == Bytes32ToFr2(NewStateRoot(input.executionTrace))
        batchCommitFr2 == Bytes32ToFr2(input.publicOutputs.batch_commitment_bytes32)
        checkpointsFr == Bytes32ToFrLE(input.publicOutputs.checkpoints_digest_bytes32)
        statusFr == U64ToFr(FinalExitStatus(input.executionTrace))
        nonceFr == U64ToFr(input.batch_nonce_in)
    IN [program_hash_lo |-> progHashFr2.lo, program_hash_hi |-> progHashFr2.hi,
        old_root_lo |-> oldRootFr2.lo, old_root_hi |-> oldRootFr2.hi,
        new_root_lo |-> newRootFr2.lo, new_root_hi |-> newRootFr2.hi,
        batch_commitment_lo |-> batchCommitFr2.lo, batch_commitment_hi |-> batchCommitFr2.hi,
        checkpoints_digest_fr |-> checkpointsFr, status_fr |-> statusFr, batch_nonce_fr |-> nonceFr]

(****************************************************************************)
(* §5.5 Wrapper Constraints                                                  *)
(* The 6 binding constraints that constitute the proof statement            *)
(****************************************************************************)

\* Constraint 1: Program hash binding
ProgramHashBinding(inputs, programHashBytes32) == LET fr2 == Bytes32ToFr2(programHashBytes32)
    IN /\ inputs.program_hash_lo = fr2.lo /\ inputs.program_hash_hi = fr2.hi

\* Constraint 2: Old root binding
OldRootBinding(inputs, trace) == LET fr2 == Bytes32ToFr2(TraceInitialState(trace).rw_mem_root_bytes32)
    IN /\ inputs.old_root_lo = fr2.lo /\ inputs.old_root_hi = fr2.hi

\* Constraint 3: New root binding
NewRootBinding(inputs, trace) == LET fr2 == Bytes32ToFr2(TraceFinalState(trace).rw_mem_root_bytes32)
    IN /\ inputs.new_root_lo = fr2.lo /\ inputs.new_root_hi = fr2.hi

\* Constraint 4: Status binding (CRITICAL for prefix-proof prevention)
StatusFrBinding(inputs, trace) == inputs.status_fr = U64ToFr(TraceFinalState(trace).exit_code)

\* Constraint 5: Halted binding
HaltedBinding(trace) == TraceFinalState(trace).halted = 1

\* Constraint 6: Nonce binding (replay prevention)
NonceBinding(inputs, trace) == inputs.batch_nonce_fr = U64ToFr(ReadReg(TraceInitialState(trace), REG_A4))

(****************************************************************************)
(* Output Constraints                                                        *)
(****************************************************************************)

ReservedBytesZero(outputs) == \A i \in 0..6 : outputs.reserved7[i] = 0
StatusMatchesExitCode(outputs, trace) == outputs.status_u8 = (FinalExitStatus(trace) % 256)
NonceMatchesInput(outputs, trace) == outputs.batch_nonce_u64 = ReadReg(TraceInitialState(trace), REG_A4)

(****************************************************************************)
(* Trap Output Construction                                                  *)
(* Creates a canonical output for trapped (failed) executions               *)
(****************************************************************************)

TrapOutputs(trapCode, batchNonceIn) == [
    status_u8 |-> trapCode % 256, reserved7 |-> ZeroReserved7, batch_nonce_u64 |-> batchNonceIn,
    old_root_bytes32 |-> ZeroBytes32, new_root_bytes32 |-> ZeroBytes32,
    batch_commitment_bytes32 |-> ZeroBytes32, checkpoints_digest_bytes32 |-> ZeroBytes32]

====
