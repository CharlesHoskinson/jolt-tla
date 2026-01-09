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
(* Status Enum: Matches Lean Jolt PublicInputs.Status                       *)
(* Decision: Use enum {0,1,2} instead of raw exit_code (0-255)              *)
(* This aligns TLA+ with the Lean oracle implementation.                    *)
(****************************************************************************)

\* Status values per Lean Jolt Wrapper/PublicInputs.lean
STATUS_SUCCESS == 0   \* Execution completed successfully (exit_code = 0)
STATUS_FAILURE == 1   \* Execution failed (exit_code > 0, any trap)
STATUS_PENDING == 2   \* Execution not yet complete (intermediate state)

Status == {STATUS_SUCCESS, STATUS_FAILURE, STATUS_PENDING}

\* Convert exit_code to Status enum
\* exit_code 0 -> Success, exit_code > 0 -> Failure
ExitCodeToStatus(exit_code) ==
    IF exit_code = 0 THEN STATUS_SUCCESS ELSE STATUS_FAILURE

\* Convert Status to Fr for public inputs
StatusToFr(status) == status  \* Identity since STATUS_* are already Fr-compatible

\* Derive status from halted flag and exit_code
\* Used when constructing public inputs from execution trace
DeriveStatus(halted, exit_code) ==
    IF halted = 0 THEN STATUS_PENDING
    ELSE IF exit_code = 0 THEN STATUS_SUCCESS
    ELSE STATUS_FAILURE

(****************************************************************************)
(* JOLT_WRAPPER_PROOF_SYSTEM_V1: Midnight-compatible proof system config    *)
(* Section Reference: spec.md §5.2                                         *)
(* These constants pin the proof system for byte-exact compatibility        *)
(****************************************************************************)

WrapperProofSystemV1 == [
    \* Proof system identity
    curve |-> "BLS12-381",
    pcs |-> "KZG",
    k |-> 14,
    domain_size |-> 16384,  \* 2^14

    \* SRS identity
    srs_id |-> "bls_midnight_2p14",
    \* srs_hash: TODO(NEEDS_EVIDENCE) - SHA-256 of actual Midnight SRS blob bytes

    \* Wire format tags
    proof_container |-> "proof-versioned",
    proof_tag |-> "proof[v5]",
    vk_tag |-> "verifier-key[v6]",
    binding_domain |-> "midnight:binding-input[v1]",

    \* Public input contract
    pub_inputs_len |-> 11,
    pub_inputs_order |-> <<
        "program_hash_lo", "program_hash_hi",
        "old_root_lo", "old_root_hi",
        "new_root_lo", "new_root_hi",
        "batch_commitment_lo", "batch_commitment_hi",
        "checkpoints_digest_fr", "status_fr", "batch_nonce_fr"
    >>,

    \* Encoding
    fr_encoding |-> "FrToBytes32LE",
    serialized_size |-> 352  \* 11 × 32 bytes
]

\* Convenience accessors
WRAPPER_PROOF_SYSTEM_CURVE == WrapperProofSystemV1.curve
WRAPPER_PROOF_SYSTEM_K == WrapperProofSystemV1.k
WRAPPER_PUBLIC_INPUTS_COUNT == WrapperProofSystemV1.pub_inputs_len

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
        \* Use Status enum {0,1,2} instead of raw exit_code
        finalState == TraceFinalState(input.executionTrace)
        statusFr == StatusToFr(DeriveStatus(finalState.halted, finalState.exit_code))
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
\* Uses Status enum {0,1,2}: Success=0, Failure=1, Pending=2
\* This matches Lean Jolt implementation
StatusFrBinding(inputs, trace) ==
    LET finalState == TraceFinalState(trace)
        expectedStatus == DeriveStatus(finalState.halted, finalState.exit_code)
    IN inputs.status_fr = StatusToFr(expectedStatus)

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

(****************************************************************************)
(* §4.2 ValidWrapperPayload: Fail-closed verification predicate            *)
(* Any mismatch implies rejection - no state transition occurs             *)
(* Reference: spec.md §5.2 - Wrapper proof validation                      *)
(****************************************************************************)

\* Check that wire format tags match pinned constants
ValidWireFormatTags(payload) ==
    /\ payload.proof_container_tag = WrapperProofSystemV1.proof_container
    /\ payload.proof_inner_tag = WrapperProofSystemV1.proof_tag
    /\ payload.vk_tag = WrapperProofSystemV1.vk_tag

\* Check that public inputs have correct count and order
ValidPublicInputsFormat(inputs) ==
    /\ Len(inputs) = WrapperProofSystemV1.pub_inputs_len
    /\ PublicInputsTypeOK(inputs)

\* Check that SRS identity matches (modeled as string equality)
ValidSRSIdentity(payload) ==
    payload.srs_id = WrapperProofSystemV1.srs_id

\* Check that proof system parameters match
ValidProofSystemParams(payload) ==
    /\ payload.curve = WrapperProofSystemV1.curve
    /\ payload.pcs = WrapperProofSystemV1.pcs
    /\ payload.k = WrapperProofSystemV1.k

\* Combined validation: ALL checks must pass for payload to be valid
\* Any mismatch causes rejection (fail-closed)
ValidWrapperPayload(payload, publicInputs) ==
    /\ ValidWireFormatTags(payload)
    /\ ValidPublicInputsFormat(publicInputs)
    /\ ValidSRSIdentity(payload)
    /\ ValidProofSystemParams(payload)

\* Explicit rejection predicate (for clarity in specs)
RejectWrapperPayload(payload, publicInputs) ==
    ~ValidWrapperPayload(payload, publicInputs)

(****************************************************************************)
(* §4.3 Nonce Replay Protection                                             *)
(* Tracks used nonces to prevent replay attacks                             *)
(* Reference: spec.md §5.2 - Nonce replay protection                       *)
(****************************************************************************)

\* State variable: set of already-used binding digests or nonces
\* In a model, this would be declared as: VARIABLE usedNonces
\* Here we define predicates for checking nonce validity

\* Check if nonce has been used before
NonceAlreadyUsed(nonce, usedNonces) ==
    nonce \in usedNonces

\* Check if nonce is fresh (not previously used)
NonceFresh(nonce, usedNonces) ==
    nonce \notin usedNonces

\* Monotonic nonce policy: new nonce must be greater than all previous
MonotonicNoncePolicy(newNonce, usedNonces) ==
    \A usedNonce \in usedNonces : newNonce > usedNonce

\* Accept nonce and update used set (for Next action)
AcceptNonce(nonce, usedNonces) ==
    usedNonces' = usedNonces \cup {nonce}

\* Complete wrapper validation including replay protection
ValidWrapperSubmission(payload, publicInputs, nonce, usedNonces) ==
    /\ ValidWrapperPayload(payload, publicInputs)
    /\ NonceFresh(nonce, usedNonces)

====
