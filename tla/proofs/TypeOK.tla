(****************************************************************************)
(* Module: TypeOK.tla                                                       *)
(* Purpose: Type invariant and inductive proof for Jolt specification       *)
(* Part of: Unbounded/infinite-state verification for Jolt                  *)
(* Reference: infinitestate.md Phase 1.3                                    *)
(****************************************************************************)
---- MODULE TypeOK ----
(****************************************************************************)
(* This module defines the TypeOK invariant and proves it is inductive.     *)
(* TypeOK ensures all system state components are well-typed.               *)
(*                                                                          *)
(* Key components:                                                          *)
(*   - TypeOK: Main type invariant predicate                                *)
(*   - CommittedChunks: Alignment definition for cross-track verification   *)
(*   - TypeOKInductive: Proof that Spec => []TypeOK                         *)
(*   - VariantNonNeg: Derived from TypeOK (not a separate axiom)            *)
(****************************************************************************)
EXTENDS JoltSpec, CryptoModel, TLAPS

(****************************************************************************)
(* Chunk Record Type Predicate                                               *)
(****************************************************************************)

ChunkRecordTypeOK(chunk) ==
    /\ chunk.index \in ChunkIndex
    /\ chunk.stateIn \in VMStateV1
    /\ chunk.stateOut \in VMStateV1
    /\ chunk.digestIn \in Fr
    /\ chunk.digestOut \in Fr

(****************************************************************************)
(* TypeOK: Main Type Invariant                                               *)
(* Ensures all system state components are within their declared types      *)
(****************************************************************************)

TypeOK ==
    \* System phase is valid
    /\ sys.phase \in SystemPhase

    \* Batch nonce is valid
    /\ sys.batchNonce \in U64

    \* Registry is well-typed
    /\ RegistryStateTypeOK(sys.registry)

    \* Program hash is well-typed
    /\ sys.programHash \in Bytes32

    \* VM state is well-typed
    /\ RegisterFileTypeOK(sys.vmState.regs)
    /\ sys.vmState.pc \in U64
    /\ sys.vmState.step_counter \in StepCounter
    /\ Bytes32TypeOK(sys.vmState.rw_mem_root_bytes32)
    /\ Bytes32TypeOK(sys.vmState.io_root_bytes32)
    /\ sys.vmState.halted \in HaltedFlag
    /\ sys.vmState.exit_code \in U64

    \* Continuation chunks are well-typed
    /\ \A i \in DOMAIN sys.continuation.chunks :
           ChunkRecordTypeOK(sys.continuation.chunks[i])

    \* CommittedChunks is well-defined and bounded
    /\ CommittedChunks(sys) \in Nat
    /\ CommittedChunks(sys) <= MAX_CHUNKS

(****************************************************************************)
(* Alignment Definition Block                                                *)
(* Canonical "chunks committed" definition across both TLA+ and Lean tracks *)
(****************************************************************************)

\* TLA+ definition: number of chunks in the continuation
CommittedChunks(s) == Len(s.continuation.chunks)

\* Lean equivalent (for reference):
\*   def CommittedChunks (s : SystemState) : Nat := s.continuation.currentChunk
\* ALIGNMENT INVARIANT: CommittedChunks_TLA = CommittedChunks_Lean

(****************************************************************************)
(* Encoding Membership Lemmas                                                *)
(* Prove that state encodings are in CriticalPreimage                        *)
(****************************************************************************)

\* State encoding function (matches Continuations.tla EncodeState)
EncodeStateForCrypto(programHash, vmState) ==
    \* Canonical encoding: pc || regs[0..31] || step_counter || ...
    << programHash,
       vmState.pc,
       vmState.regs,
       vmState.step_counter,
       vmState.rw_mem_root_bytes32,
       vmState.io_root_bytes32,
       vmState.halted,
       vmState.exit_code >>

\* Lemma: All state encodings are in StateEncoding domain
LEMMA EncodeStateMembership ==
    \A ph \in Bytes32, s \in VMStateV1 :
        EncodeStateForCrypto(ph, s) \in StateEncoding
<1>1. TAKE ph \in Bytes32, s \in VMStateV1
<1>2. EncodeStateForCrypto(ph, s) \in StateEncoding
      \* Follows from StateEncoding being defined to include all valid encodings
      BY DEF EncodeStateForCrypto, StateEncoding
<1>3. QED BY <1>2

\* Lemma: State encodings in SE constructor are in CriticalPreimage
LEMMA EncodeStateInCritical ==
    \A ph \in Bytes32, s \in VMStateV1 :
        SE(EncodeStateForCrypto(ph, s)) \in CriticalPreimage
<1>1. TAKE ph \in Bytes32, s \in VMStateV1
<1>2. EncodeStateForCrypto(ph, s) \in StateEncoding
      BY EncodeStateMembership
<1>3. SE(EncodeStateForCrypto(ph, s)) \in Preimage
      BY <1>2 DEF Preimage, SE
<1>4. SE(EncodeStateForCrypto(ph, s)) \in CriticalPreimage
      BY <1>3 DEF CriticalPreimage
<1>5. QED BY <1>4

\* Lemma: All domain tags are in Tag
LEMMA TagMembership ==
    \A tag \in ALL_DOMAIN_TAGS : tag \in Tag
<1>1. ALL_DOMAIN_TAGS \subseteq Tag
      \* Follows from model instantiation
      BY DEF Tag, ALL_DOMAIN_TAGS
<1>2. QED BY <1>1

(****************************************************************************)
(* THEOREM: TypeOK is Inductive                                              *)
(* Proves Spec => []TypeOK using temporal induction                          *)
(****************************************************************************)

THEOREM TypeOKInductive == Spec => []TypeOK
<1>1. Init => TypeOK
      \* Init establishes all type constraints
      <2>1. ASSUME Init
      <2>2. sys.phase = PHASE_INIT
            BY <2>1 DEF Init, InitSystemState
      <2>3. PHASE_INIT \in SystemPhase
            BY DEF SystemPhase, PHASE_INIT
      <2>4. sys.phase \in SystemPhase
            BY <2>2, <2>3
      <2>5. sys.batchNonce \in U64
            BY <2>1 DEF Init, InitSystemState
      <2>6. CommittedChunks(sys) = 0
            BY <2>1 DEF Init, InitSystemState, InitContinuation, CommittedChunks
      <2>7. CommittedChunks(sys) \in Nat /\ CommittedChunks(sys) <= MAX_CHUNKS
            BY <2>6
      <2>8. \* Remaining type constraints follow from Init definition
            TypeOK
            BY <2>4, <2>5, <2>7 DEF TypeOK, Init, InitSystemState
      <2>9. QED BY <2>8

<1>2. TypeOK /\ [Next]_<<sys>> => TypeOK'
      \* Each action preserves TypeOK
      <2>1. SUFFICES ASSUME TypeOK, [Next]_<<sys>>
                     PROVE TypeOK'
            OBVIOUS
      <2>2. CASE UNCHANGED <<sys>>
            BY <2>2, <2>1 DEF TypeOK
      <2>3. CASE Next
            <3>1. CASE StartExecution
                  \* Phase changes INIT -> EXECUTING, other fields unchanged
                  BY <3>1 DEF StartExecution, TypeOK, SystemPhase
            <3>2. CASE ExecuteOneChunk
                  \* vmState updated, new chunk added to continuation
                  <4>1. CommittedChunks(sys') = CommittedChunks(sys) + 1
                        BY <3>2 DEF ExecuteOneChunk, CommittedChunks
                  <4>2. CommittedChunks(sys') <= MAX_CHUNKS
                        BY <4>1, <2>1 DEF TypeOK
                  <4>3. QED BY <3>2, <4>2 DEF ExecuteOneChunk, TypeOK
            <3>3. CASE CompleteExecution
                  \* Phase changes EXECUTING -> COMPLETE
                  BY <3>3 DEF CompleteExecution, TypeOK, SystemPhase
            <3>4. CASE ExecutionFailed
                  \* Phase changes EXECUTING -> FAILED
                  BY <3>4 DEF ExecutionFailed, TypeOK, SystemPhase
            <3>5. QED BY <3>1, <3>2, <3>3, <3>4 DEF Next
      <2>4. QED BY <2>2, <2>3

<1>3. QED BY <1>1, <1>2, PTL DEF Spec

(****************************************************************************)
(* VariantNonNeg: Variant is non-negative                                    *)
(* This is a CONSEQUENCE of TypeOK, not a separate invariant                 *)
(****************************************************************************)

\* Variant function definition (for reference - full definition in SafetyInduction)
Variant(s) ==
    IF s.phase \in {PHASE_COMPLETE, PHASE_FAILED} THEN 0
    ELSE (MAX_CHUNKS - CommittedChunks(s)) * CHUNK_MAX_STEPS +
         ((CHUNK_MAX_STEPS - 1) - (s.vmState.step_counter % CHUNK_MAX_STEPS))

\* Lemma: Variant is always non-negative when TypeOK holds
LEMMA VariantNonNeg == TypeOK => Variant(sys) >= 0
<1>1. ASSUME TypeOK
<1>2. CASE sys.phase \in {PHASE_COMPLETE, PHASE_FAILED}
      <2>1. Variant(sys) = 0
            BY <1>2 DEF Variant
      <2>2. QED BY <2>1
<1>3. CASE sys.phase \notin {PHASE_COMPLETE, PHASE_FAILED}
      <2>1. CommittedChunks(sys) <= MAX_CHUNKS
            BY <1>1 DEF TypeOK
      <2>2. MAX_CHUNKS - CommittedChunks(sys) >= 0
            BY <2>1
      <2>3. (MAX_CHUNKS - CommittedChunks(sys)) * CHUNK_MAX_STEPS >= 0
            BY <2>2
      <2>4. sys.vmState.step_counter % CHUNK_MAX_STEPS < CHUNK_MAX_STEPS
            \* Modulo is always less than divisor
            OBVIOUS
      <2>5. (CHUNK_MAX_STEPS - 1) - (sys.vmState.step_counter % CHUNK_MAX_STEPS) >= 0
            BY <2>4
      <2>6. Variant(sys) >= 0
            BY <2>3, <2>5, <1>3 DEF Variant
      <2>7. QED BY <2>6
<1>4. QED BY <1>2, <1>3

(****************************************************************************)
(* Corollary: Variant is always non-negative under Spec                      *)
(****************************************************************************)

COROLLARY VariantNonNegSpec == Spec => [](Variant(sys) >= 0)
BY TypeOKInductive, VariantNonNeg, PTL

====
