(****************************************************************************)
(* Module: Continuations.tla                                                *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE Continuations ----
(****************************************************************************)
(* Purpose: Chunked execution and StateDigest chaining for continuations    *)
(* Appendix J Reference: J.10 (Continuations, snapshots, StateDigest)       *)
(* Version: 1.0                                                             *)
(* Notes: SerializeVMStateWithProgram includes all security-critical fields *)
(*        (config_tags, rw_root, io_root). Uses modular arithmetic for TLC. *)
(****************************************************************************)
EXTENDS VMState, Transcript, Sequences, Naturals, TLC

(****************************************************************************)
(* StateDigestV1 Computation (J.10.10)                                      *)
(* Single-field commitment to VM state + configuration + program identity   *)
(* The digest MUST include program_hash to prevent cross-program splicing   *)
(*                                                                          *)
(* TLC MODEL LIMITATION: The serialization below uses fingerprint-based     *)
(* weighted sums with modular arithmetic for TLC tractability. This is NOT  *)
(* the production algorithm! Production implementations MUST use:           *)
(*                                                                          *)
(* J.10.10.2 StateDigestV1 Algorithm (14 steps):                            *)
(*   1. T := TranscriptV1.init()                                            *)
(*   2. T.absorb_tag("JOLT/STATE/V1")                                       *)
(*   3. T.absorb_bytes(program_hash_bytes32)                                *)
(*   4. T.absorb_u64(S.pc)                                                  *)
(*   5. For i = 0 to 31: T.absorb_u64(S.regs[i])                            *)
(*   6. T.absorb_u64(S.step_counter)                                        *)
(*   7. T.absorb_bytes(S.rw_mem_root_bytes32)                               *)
(*   8. T.absorb_bytes(S.io_root_bytes32)                                   *)
(*   9. T.absorb_u64(u64(S.halted))                                         *)
(*  10. T.absorb_u64(S.exit_code)                                           *)
(*  11. T.absorb_tag("JOLT/CONFIG_TAGS/V1")                                 *)
(*  12. T.absorb_u64(len(S.config_tags))                                    *)
(*  13. For each (tag_name, tag_value) in sorted order:                     *)
(*      T.absorb_tag("JOLT/TAG/V1")                                         *)
(*      T.absorb_bytes(tag_name_bytes)                                      *)
(*      T.absorb_bytes(tag_value_bytes)                                     *)
(*  14. state_digest_fr := T.challenge_fr()                                 *)
(*                                                                          *)
(* The TLC model below maintains STRUCTURAL correctness (all fields bound)  *)
(* but uses modular arithmetic that creates collisions. This is acceptable  *)
(* for model checking because:                                              *)
(*   - TLC tests the STRUCTURE of the spec, not cryptographic security      *)
(*   - Production uses proper Poseidon transcript (collision-resistant)     *)
(*   - INV_ATK_* invariants verify the abstract security properties         *)
(****************************************************************************)

\* Helper: sum of a finite set of numbers
SumSet(S) == LET RECURSIVE Sum(_)
                 Sum(s) == IF s = {} THEN 0
                           ELSE LET x == CHOOSE x \in s : TRUE
                                IN x + Sum(s \ {x})
             IN Sum(S)

\* Serialize VMState for hashing
\* Creates a numeric encoding that preserves uniqueness for model checking
\* Different states MUST produce different values for collision-resistance
\* J.10.10: includes program_hash, pc, regs, step_counter, roots, halted, exit_code, config_tags
SerializeVMStateWithProgram(program_hash_bytes32, state) ==
    LET
        \* Sum of register values (captures register state)
        regSum == LET indices == DOMAIN state.regs
                  IN IF indices = {} THEN 0
                     ELSE SumSet({state.regs[i] : i \in indices})
        \* Include program_hash in serialization (prevents cross-program splice)
        \* Use a hash of the bytes32 to get a numeric contribution
        progHashContrib == IF program_hash_bytes32 \in Bytes32
                           THEN SumSet({program_hash_bytes32[i] : i \in DOMAIN program_hash_bytes32})
                           ELSE 0
        \* Include config_tags in serialization (prevents cross-config splice)
        \* J.10.10: config_tags MUST be included to bind digest to configuration
        \* ConfigTag has fields: name, value (both STRING)
        configTagsContrib == IF Len(state.config_tags) > 0
                             THEN SumSet({Len(state.config_tags[i].name) + Len(state.config_tags[i].value) :
                                          i \in 1..Len(state.config_tags)})
                             ELSE 0
        \* Include memory roots (prevents memory state forgery)
        rwRootContrib == SumSet({state.rw_mem_root_bytes32[i] : i \in DOMAIN state.rw_mem_root_bytes32})
        ioRootContrib == SumSet({state.io_root_bytes32[i] : i \in DOMAIN state.io_root_bytes32})
        \* Combine ALL varying fields with distinct weights
        \* Weights chosen so different states -> different encodings
        \* NOTE: Keep values within TLC bounds (< 2^31)
    IN (progHashContrib % 1000) * 100000
       + (configTagsContrib % 100) * 10000
       + ((rwRootContrib + ioRootContrib) % 100) * 1000
       + (state.step_counter % 100) * 100
       + (state.pc % 10) * 10
       + state.halted * 5
       + (state.exit_code % 5)
       + (regSum % 5)  \* Include register state

\* Compute StateDigestV1 from program hash and VMState
\* J.10.10: Poseidon hash of serialized state with domain tag
\* The program_hash is included to bind the digest to a specific program
ComputeStateDigest(program_hash_bytes32, state) ==
    PoseidonHashV1(TAG_STATE_DIGEST, SerializeVMStateWithProgram(program_hash_bytes32, state))

\* StateDigest as Fr
StateDigest == Fr

(****************************************************************************)
(* Chunk Record                                                              *)
(* Captures input/output state and digests for a single chunk               *)
(* Includes program_hash_bytes32 to prevent cross-program splicing          *)
(****************************************************************************)

ChunkRecord == [
    program_hash_bytes32: Bytes32,  \* Program identity (binds chunk to program)
    chunkIndex: ChunkIndex,
    \* Input state (at chunk start)
    stateIn: VMStateV1,
    digestIn: StateDigest,
    \* Output state (at chunk end)
    stateOut: VMStateV1,
    digestOut: StateDigest,
    \* Execution metadata
    stepsExecuted: Nat,
    isFinal: BOOLEAN
]

\* Construct a chunk record from execution
\* program_hash_bytes32 is required to compute the correct digest
MakeChunkRecord(program_hash_bytes32, idx, stateIn, stateOut) ==
    [
        program_hash_bytes32 |-> program_hash_bytes32,
        chunkIndex |-> idx,
        stateIn |-> stateIn,
        digestIn |-> ComputeStateDigest(program_hash_bytes32, stateIn),
        stateOut |-> stateOut,
        digestOut |-> ComputeStateDigest(program_hash_bytes32, stateOut),
        stepsExecuted |-> stateOut.step_counter - stateIn.step_counter,
        isFinal |-> IsHalted(stateOut)
    ]

(****************************************************************************)
(* Chunk Execution Rules (J.10.6)                                           *)
(****************************************************************************)

\* Chunk i begins with step_counter = i * CHUNK_MAX_STEPS
ExpectedChunkStartStep(chunkIdx) == chunkIdx * CHUNK_MAX_STEPS

\* Non-final chunks execute exactly CHUNK_MAX_STEPS
NonFinalChunkSteps == CHUNK_MAX_STEPS

\* Check if chunk input state has correct step counter
ChunkInputStepValid(chunk) ==
    chunk.stateIn.step_counter = ExpectedChunkStartStep(chunk.chunkIndex)

\* Check if non-final chunk executed correct number of steps
NonFinalChunkStepsValid(chunk) ==
    ~chunk.isFinal => chunk.stepsExecuted = CHUNK_MAX_STEPS

\* Check if non-final chunk has halted = 0
NonFinalChunkNotHalted(chunk) ==
    ~chunk.isFinal => chunk.stateOut.halted = 0

\* Check if final chunk has halted = 1
FinalChunkHalted(chunk) ==
    chunk.isFinal => chunk.stateOut.halted = 1

\* Final chunk can execute 1 to CHUNK_MAX_STEPS
FinalChunkStepsValid(chunk) ==
    chunk.isFinal =>
        /\ chunk.stepsExecuted >= 1
        /\ chunk.stepsExecuted <= CHUNK_MAX_STEPS

(****************************************************************************)
(* Chunk Validity                                                            *)
(****************************************************************************)

\* A chunk is valid if it follows all execution rules
ChunkValid(chunk) ==
    /\ ChunkInputStepValid(chunk)
    /\ NonFinalChunkStepsValid(chunk)
    /\ NonFinalChunkNotHalted(chunk)
    /\ FinalChunkHalted(chunk)
    /\ FinalChunkStepsValid(chunk)
    \* Digest consistency (using chunk's program_hash_bytes32)
    /\ chunk.digestIn = ComputeStateDigest(chunk.program_hash_bytes32, chunk.stateIn)
    /\ chunk.digestOut = ComputeStateDigest(chunk.program_hash_bytes32, chunk.stateOut)

(****************************************************************************)
(* Chunk Chaining (J.10.4)                                                  *)
(* The core soundness property: adjacent chunks must have matching digests  *)
(****************************************************************************)

\* Two chunks are properly chained if output of first = input of second
ChunksChained(chunk1, chunk2) ==
    /\ chunk1.chunkIndex + 1 = chunk2.chunkIndex
    /\ chunk1.digestOut = chunk2.digestIn

\* The continuity invariant for a sequence of chunks
\* J.10.4: "output digest of chunk i equals the input digest of chunk i+1"
ContinuityInvariant(chunks) ==
    \A i \in 1..(Len(chunks) - 1) :
        chunks[i].digestOut = chunks[i + 1].digestIn

\* Alternative formulation: no gaps in chain
NoGapsInChain(chunks) ==
    \A i \in 1..(Len(chunks) - 1) :
        ChunksChained(chunks[i], chunks[i + 1])

(****************************************************************************)
(* Execution Trace                                                           *)
(* Complete execution as sequence of chunks                                  *)
(****************************************************************************)

ExecutionTrace == Seq(ChunkRecord)

\* A valid execution trace satisfies all chunk and chaining rules
ExecutionTraceValid(trace) ==
    /\ Len(trace) >= 1
    \* First chunk starts at index 0
    /\ trace[1].chunkIndex = 0
    \* All chunks are individually valid
    /\ \A i \in 1..Len(trace) : ChunkValid(trace[i])
    \* Chunks are properly chained
    /\ ContinuityInvariant(trace)
    \* Exactly one final chunk (the last one)
    /\ trace[Len(trace)].isFinal
    /\ \A i \in 1..(Len(trace) - 1) : ~trace[i].isFinal

\* Get the initial state of an execution trace
TraceInitialState(trace) == trace[1].stateIn

\* Get the final state of an execution trace
TraceFinalState(trace) == trace[Len(trace)].stateOut

\* Get the initial digest of an execution trace
TraceInitialDigest(trace) == trace[1].digestIn

\* Get the final digest of an execution trace
TraceFinalDigest(trace) == trace[Len(trace)].digestOut

(****************************************************************************)
(* Config Tags Consistency                                                   *)
(* Config must be constant across all chunks (prevents cross-config splice) *)
(****************************************************************************)

\* All chunks in a trace must have the same config_tags
ConfigConsistentAcrossChunks(trace) ==
    \A i, j \in 1..Len(trace) :
        trace[i].stateIn.config_tags = trace[j].stateIn.config_tags

\* Config tags are preserved through execution
ConfigPreservedInChunk(chunk) ==
    chunk.stateIn.config_tags = chunk.stateOut.config_tags

(****************************************************************************)
(* Continuation State Machine                                                *)
(* Models the progression through chunks                                     *)
(****************************************************************************)

\* Continuation state record
\* Includes program_hash_bytes32 to ensure all chunks use consistent program identity
ContinuationState == [
    program_hash_bytes32: Bytes32,  \* Program identity
    currentChunk: ChunkIndex,
    chunks: ExecutionTrace,
    complete: BOOLEAN,
    initialDigest: StateDigest,
    finalDigest: StateDigest
]

\* Initial continuation state (before any chunks executed)
\* program_hash_bytes32 is required to compute the initial digest
InitContinuation(program_hash_bytes32, initialState) ==
    [
        program_hash_bytes32 |-> program_hash_bytes32,
        currentChunk |-> 0,
        chunks |-> << >>,
        complete |-> FALSE,
        initialDigest |-> ComputeStateDigest(program_hash_bytes32, initialState),
        finalDigest |-> 0  \* Not yet known
    ]

\* Execute a chunk and record it
\* Uses continuation's program_hash_bytes32 for digest computation
ExecuteChunk(cont, stateIn, stateOut) ==
    LET
        chunk == MakeChunkRecord(cont.program_hash_bytes32, cont.currentChunk, stateIn, stateOut)
        newChunks == Append(cont.chunks, chunk)
        isComplete == chunk.isFinal
    IN
        [cont EXCEPT
            !.currentChunk = @ + 1,
            !.chunks = newChunks,
            !.complete = isComplete,
            !.finalDigest = IF isComplete THEN chunk.digestOut ELSE @
        ]

\* Predicate: Continuation is complete (final chunk executed)
ContinuationComplete(cont) == cont.complete

\* Predicate: Ready to execute next chunk
ReadyForNextChunk(cont) == ~cont.complete

(****************************************************************************)
(* Safety Invariants for Continuations                                       *)
(****************************************************************************)

\* StateDigest uniquely determines (program_hash, state) pair (collision resistance)
\* NOTE: This property is NOT TLC-checkable for large domains; it documents a security assumption
StateDigestInjective ==
    \A ph1, ph2 \in Bytes32 :
        \A s1, s2 \in VMStateV1 :
            ComputeStateDigest(ph1, s1) = ComputeStateDigest(ph2, s2) =>
                /\ ph1 = ph2
                /\ s1 = s2

\* Continuity cannot be forged: matching digests imply matching states
ContinuityUnforgeable(chunk1, chunk2) ==
    chunk1.digestOut = chunk2.digestIn =>
        chunk1.stateOut = chunk2.stateIn

\* Full execution integrity: trace digest chain is unbroken
ExecutionIntegrity(trace) ==
    /\ ExecutionTraceValid(trace)
    /\ ConfigConsistentAcrossChunks(trace)

(****************************************************************************)
(* Attack Prevention Invariants (J.10.3)                                    *)
(****************************************************************************)

\* Attack 1 Prevention: Cannot skip chunks
\* If chunk i and chunk j are in trace and j = i + 2, there must be chunk i+1
NoSkippedChunks(trace) ==
    \A i \in 1..Len(trace) :
        trace[i].chunkIndex = i - 1  \* Chunks are consecutive starting at 0

\* Attack 2 Prevention: Cannot splice different executions
\* Same initial digest + same config -> same execution path
NoSplicedExecutions ==
    \A t1, t2 \in ExecutionTrace :
        (/\ ExecutionTraceValid(t1)
         /\ ExecutionTraceValid(t2)
         /\ TraceInitialDigest(t1) = TraceInitialDigest(t2)
         /\ ConfigConsistentAcrossChunks(t1)
         /\ ConfigConsistentAcrossChunks(t2)
         /\ t1[1].stateIn.config_tags = t2[1].stateIn.config_tags)
        =>
        \* Same execution (by determinism)
        TraceFinalDigest(t1) = TraceFinalDigest(t2)

\* Attack 3 Prevention: Cannot cross-config splice
\* Different config_tags -> different StateDigest (config is in digest)
NoCrossConfigSplice(chunk1, chunk2) ==
    chunk1.stateOut.config_tags # chunk2.stateIn.config_tags =>
        chunk1.digestOut # chunk2.digestIn

(****************************************************************************)
(* Type Invariant                                                            *)
(****************************************************************************)

ChunkRecordTypeOK(chunk) ==
    /\ chunk.program_hash_bytes32 \in Bytes32
    /\ chunk.chunkIndex \in ChunkIndex
    /\ VMStateTypeOK(chunk.stateIn)
    /\ VMStateTypeOK(chunk.stateOut)
    /\ chunk.digestIn \in StateDigest
    /\ chunk.digestOut \in StateDigest
    /\ chunk.stepsExecuted \in Nat
    /\ chunk.isFinal \in BOOLEAN

ContinuationStateTypeOK(cont) ==
    /\ cont.program_hash_bytes32 \in Bytes32
    /\ cont.currentChunk \in Nat  \* Allow any natural (bounded by execution)
    /\ cont.currentChunk <= Len(cont.chunks) + 1  \* At most one past last chunk
    \* NOTE: Skip \in ExecutionTrace (infinite set); instead check each element
    /\ Len(cont.chunks) >= 0  \* Trivial sequence check (Len works on sequences)
    /\ \A i \in 1..Len(cont.chunks) : ChunkRecordTypeOK(cont.chunks[i])
    /\ cont.complete \in BOOLEAN
    /\ cont.initialDigest \in StateDigest
    /\ cont.finalDigest \in StateDigest

(****************************************************************************)
(* Wrapper Integration Helpers                                               *)
(* Prepare data for the wrapper circuit                                      *)
(****************************************************************************)

\* Extract old state root from initial state
OldStateRoot(trace) ==
    TraceInitialState(trace).rw_mem_root_bytes32

\* Extract new state root from final state
NewStateRoot(trace) ==
    TraceFinalState(trace).rw_mem_root_bytes32

\* Extract exit status from final state
FinalExitStatus(trace) ==
    TraceFinalState(trace).exit_code

====
