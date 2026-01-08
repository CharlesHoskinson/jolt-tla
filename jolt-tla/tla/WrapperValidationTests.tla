(****************************************************************************)
(* Module: WrapperValidationTests.tla                                       *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE WrapperValidationTests ----
(****************************************************************************)
(* TLC Test Cases for JOLT_WRAPPER_PROOF_SYSTEM_V1 Validation               *)
(* Section Reference: CLAUDE_UPDATE_PLAN_JOLT_WRAPPER_PROOF_SYSTEM_V1 §4.4  *)
(* Purpose: Verify fail-closed validation logic for wrapper payloads        *)
(*                                                                          *)
(* This is a STANDALONE test module that does not depend on the full        *)
(* continuation spec machinery. It duplicates the wrapper constants and     *)
(* predicates for isolated testing.                                         *)
(****************************************************************************)
EXTENDS TLC, Sequences, Naturals

(****************************************************************************)
(* JOLT_WRAPPER_PROOF_SYSTEM_V1 Constants (copied from Wrapper.tla)         *)
(****************************************************************************)

WrapperProofSystemV1 == [
    curve |-> "BLS12-381",
    pcs |-> "KZG",
    k |-> 14,
    domain_size |-> 16384,
    srs_id |-> "bls_midnight_2p14",
    proof_container |-> "proof-versioned",
    proof_tag |-> "proof[v5]",
    vk_tag |-> "verifier-key[v6]",
    binding_domain |-> "midnight:binding-input[v1]",
    pub_inputs_len |-> 11,
    pub_inputs_order |-> <<
        "program_hash_lo", "program_hash_hi",
        "old_root_lo", "old_root_hi",
        "new_root_lo", "new_root_hi",
        "batch_commitment_lo", "batch_commitment_hi",
        "checkpoints_digest_fr", "status_fr", "batch_nonce_fr"
    >>,
    fr_encoding |-> "FrToBytes32LE",
    serialized_size |-> 352
]

(****************************************************************************)
(* Validation Predicates (copied from Wrapper.tla)                          *)
(****************************************************************************)

ValidWireFormatTags(payload) ==
    /\ payload.proof_container_tag = WrapperProofSystemV1.proof_container
    /\ payload.proof_inner_tag = WrapperProofSystemV1.proof_tag
    /\ payload.vk_tag = WrapperProofSystemV1.vk_tag

ValidSRSIdentity(payload) ==
    payload.srs_id = WrapperProofSystemV1.srs_id

ValidProofSystemParams(payload) ==
    /\ payload.curve = WrapperProofSystemV1.curve
    /\ payload.pcs = WrapperProofSystemV1.pcs
    /\ payload.k = WrapperProofSystemV1.k

NonceAlreadyUsed(nonce, usedNonces) ==
    nonce \in usedNonces

NonceFresh(nonce, usedNonces) ==
    nonce \notin usedNonces

MonotonicNoncePolicy(newNonce, usedNonces) ==
    \A usedNonce \in usedNonces : newNonce > usedNonce

(****************************************************************************)
(* Test Fixtures: Valid and Invalid Payloads                                *)
(****************************************************************************)

ValidPayload == [
    proof_container_tag |-> "proof-versioned",
    proof_inner_tag |-> "proof[v5]",
    vk_tag |-> "verifier-key[v6]",
    srs_id |-> "bls_midnight_2p14",
    curve |-> "BLS12-381",
    pcs |-> "KZG",
    k |-> 14
]

WrongProofContainerPayload == [
    proof_container_tag |-> "proof-WRONG",
    proof_inner_tag |-> "proof[v5]",
    vk_tag |-> "verifier-key[v6]",
    srs_id |-> "bls_midnight_2p14",
    curve |-> "BLS12-381",
    pcs |-> "KZG",
    k |-> 14
]

WrongProofInnerPayload == [
    proof_container_tag |-> "proof-versioned",
    proof_inner_tag |-> "proof[v4]",
    vk_tag |-> "verifier-key[v6]",
    srs_id |-> "bls_midnight_2p14",
    curve |-> "BLS12-381",
    pcs |-> "KZG",
    k |-> 14
]

WrongVKTagPayload == [
    proof_container_tag |-> "proof-versioned",
    proof_inner_tag |-> "proof[v5]",
    vk_tag |-> "verifier-key[v5]",
    srs_id |-> "bls_midnight_2p14",
    curve |-> "BLS12-381",
    pcs |-> "KZG",
    k |-> 14
]

WrongSRSPayload == [
    proof_container_tag |-> "proof-versioned",
    proof_inner_tag |-> "proof[v5]",
    vk_tag |-> "verifier-key[v6]",
    srs_id |-> "bls_wrong_srs",
    curve |-> "BLS12-381",
    pcs |-> "KZG",
    k |-> 14
]

WrongCurvePayload == [
    proof_container_tag |-> "proof-versioned",
    proof_inner_tag |-> "proof[v5]",
    vk_tag |-> "verifier-key[v6]",
    srs_id |-> "bls_midnight_2p14",
    curve |-> "BN254",
    pcs |-> "KZG",
    k |-> 14
]

WrongKPayload == [
    proof_container_tag |-> "proof-versioned",
    proof_inner_tag |-> "proof[v5]",
    vk_tag |-> "verifier-key[v6]",
    srs_id |-> "bls_midnight_2p14",
    curve |-> "BLS12-381",
    pcs |-> "KZG",
    k |-> 20
]

(****************************************************************************)
(* Test Assertions                                                           *)
(****************************************************************************)

\* Wire format tag tests
TestValidPayloadAccepted == ValidWireFormatTags(ValidPayload)
TestWrongProofContainerRejected == ~ValidWireFormatTags(WrongProofContainerPayload)
TestWrongProofInnerRejected == ~ValidWireFormatTags(WrongProofInnerPayload)
TestWrongVKTagRejected == ~ValidWireFormatTags(WrongVKTagPayload)

\* SRS and proof system tests
TestWrongSRSRejected == ~ValidSRSIdentity(WrongSRSPayload)
TestWrongCurveRejected == ~ValidProofSystemParams(WrongCurvePayload)
TestWrongKRejected == ~ValidProofSystemParams(WrongKPayload)
TestValidSRSAccepted == ValidSRSIdentity(ValidPayload)
TestValidProofSystemAccepted == ValidProofSystemParams(ValidPayload)

\* Nonce replay tests
TestFreshNonceAccepted == NonceFresh(100, {1, 2, 3})
TestUsedNonceRejected == NonceAlreadyUsed(2, {1, 2, 3})
TestMonotonicNonce == MonotonicNoncePolicy(100, {1, 2, 3})
TestNonMonotonicNonceRejected == ~MonotonicNoncePolicy(2, {1, 2, 3})

\* Public input order test
TestPublicInputsOrder ==
    /\ Len(WrapperProofSystemV1.pub_inputs_order) = 11
    /\ WrapperProofSystemV1.pub_inputs_order[1] = "program_hash_lo"
    /\ WrapperProofSystemV1.pub_inputs_order[11] = "batch_nonce_fr"

\* Serialized size test
TestSerializedSize == WrapperProofSystemV1.serialized_size = 352

(****************************************************************************)
(* Combined Test Invariant                                                  *)
(****************************************************************************)

AllWrapperTests ==
    /\ TestValidPayloadAccepted
    /\ TestWrongProofContainerRejected
    /\ TestWrongProofInnerRejected
    /\ TestWrongVKTagRejected
    /\ TestWrongSRSRejected
    /\ TestWrongCurveRejected
    /\ TestWrongKRejected
    /\ TestValidSRSAccepted
    /\ TestValidProofSystemAccepted
    /\ TestFreshNonceAccepted
    /\ TestUsedNonceRejected
    /\ TestMonotonicNonce
    /\ TestNonMonotonicNonceRejected
    /\ TestPublicInputsOrder
    /\ TestSerializedSize

\* Trivial spec for TLC (no state changes, just check invariants)
VARIABLE dummy

Init == dummy = 0
Next == UNCHANGED dummy
Spec == Init /\ [][Next]_dummy

====
