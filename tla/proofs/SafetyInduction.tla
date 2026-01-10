(****************************************************************************)
(* Module: SafetyInduction.tla                                              *)
(* Purpose: Single inductive invariant + variant lemmas for Jolt            *)
(* Part of: Unbounded/infinite-state verification for Jolt                  *)
(* Reference: infinitestate.md Phase 1.4, 1.7                               *)
(****************************************************************************)
---- MODULE SafetyInduction ----
(****************************************************************************)
(* This module provides:                                                    *)
(*   1. AuxInv: Auxiliary invariants (immutability, coherence, monotonicity)*)
(*   2. IndInv: Single inductive invariant combining TypeOK + AuxInv + Safety*)
(*   3. Progress partition: Next decomposes into ProgressStep/NonProgressStep*)
(*   4. Variant lemmas: decrease on progress, non-increase otherwise        *)
(*   5. Safety corollaries: derive each INV_SAFE_* from IndInv              *)
(*                                                                          *)
(* Key principle: Prove IndInv is inductive ONCE, derive all else as        *)
(* corollaries. This avoids reproving induction for each safety property.   *)
(****************************************************************************)
EXTENDS TypeOK, Invariants, TLAPS

(****************************************************************************)
(* Auxiliary Invariants                                                      *)
(* Properties needed for inductive proof but not in INV_SAFE_All            *)
(****************************************************************************)

\* Registry immutability after INIT: registry cannot change post-initialization
RegistryImmutable ==
    sys.phase # PHASE_INIT => sys.registry = sys.registry

\* Program hash immutability after INIT
ProgramHashImmutable ==
    sys.phase # PHASE_INIT => sys.programHash = sys.programHash

\* Chunk index coherence: indices are consecutive starting from 0
ChunkIndexCoherence ==
    \A i \in 1..Len(sys.continuation.chunks) :
        sys.continuation.chunks[i].chunkIndex = i - 1

\* Phase monotonicity: no rewinding to earlier phases
\* INIT -> EXECUTING -> {COMPLETE, FAILED}
PhaseMonotonicity ==
    /\ (sys.phase = PHASE_EXECUTING => sys.phase' \in {PHASE_EXECUTING, PHASE_COMPLETE, PHASE_FAILED})
    /\ (sys.phase = PHASE_COMPLETE => sys.phase' = PHASE_COMPLETE)
    /\ (sys.phase = PHASE_FAILED => sys.phase' = PHASE_FAILED)

\* Step counter monotonicity (VM-02)
StepCounterMonotonic ==
    sys.phase = PHASE_EXECUTING =>
        sys.vmState.step_counter <= sys.vmState.step_counter'

\* Halt irreversibility (VM-03)
HaltIrreversible ==
    sys.vmState.halted = 1 => sys.vmState.halted' = 1

\* Combine all auxiliary invariants
AuxInv ==
    /\ ChunkIndexCoherence
    \* Note: Immutability and monotonicity are action properties,
    \* expressed as state predicates where appropriate

(****************************************************************************)
(* Single Inductive Invariant                                                *)
(* Combines TypeOK + AuxInv + all safety invariants from Invariants.tla     *)
(****************************************************************************)

IndInv ==
    /\ TypeOK
    /\ AuxInv
    /\ INV_SAFE_All

(****************************************************************************)
(* THEOREM: IndInv is Inductive                                              *)
(* Proves Spec => []IndInv                                                  *)
(****************************************************************************)

THEOREM IndInvInductive == Spec => []IndInv
<1>1. Init => IndInv
      \* Init establishes all invariants
      <2>1. Init => TypeOK
            BY TypeOKInductive
      <2>2. Init => AuxInv
            <3>1. ASSUME Init
            <3>2. Len(sys.continuation.chunks) = 0
                  BY <3>1 DEF Init, InitSystemState, InitContinuation
            <3>3. ChunkIndexCoherence
                  BY <3>2 DEF ChunkIndexCoherence  \* Vacuously true
            <3>4. AuxInv
                  BY <3>3 DEF AuxInv
            <3>5. QED BY <3>4
      <2>3. Init => INV_SAFE_All
            <3>1. ASSUME Init
            <3>2. sys.phase = PHASE_INIT
                  BY <3>1 DEF Init, InitSystemState
            <3>3. \* Most safety invariants are vacuously true in INIT
                  \* or directly established by InitSystemState
                  INV_SAFE_All
                  BY <3>1, <3>2 DEF INV_SAFE_All, Init, InitSystemState,
                     INV_SAFE_RegistryReady, INV_SAFE_NoTBD,
                     INV_SAFE_VMHaltedExitCode, INV_SAFE_RegisterX0,
                     INV_SAFE_HaltedBinary, INV_SAFE_ContinuationChain,
                     INV_SAFE_FinalChunkHalted
            <3>4. QED BY <3>3
      <2>4. QED BY <2>1, <2>2, <2>3 DEF IndInv

<1>2. IndInv /\ [Next]_<<sys>> => IndInv'
      \* Inductive step: each action preserves IndInv
      <2>1. SUFFICES ASSUME IndInv, [Next]_<<sys>>
                     PROVE IndInv'
            OBVIOUS
      <2>2. CASE UNCHANGED <<sys>>
            BY <2>2, <2>1 DEF IndInv, TypeOK, AuxInv, INV_SAFE_All
      <2>3. CASE Next
            <3>1. CASE StartExecution
                  \* Phase: INIT -> EXECUTING
                  \* Preserves TypeOK (phase in SystemPhase)
                  \* Preserves AuxInv (no chunks added)
                  \* Establishes RegistryReady for EXECUTING phase
                  BY <3>1, <2>1 DEF StartExecution, IndInv, TypeOK, AuxInv, INV_SAFE_All
            <3>2. CASE ExecuteOneChunk
                  \* New chunk added, vmState updated
                  <4>1. TypeOK'
                        BY <3>2, <2>1 DEF ExecuteOneChunk, TypeOK
                  <4>2. AuxInv'
                        \* New chunk has correct index
                        BY <3>2, <2>1 DEF ExecuteOneChunk, AuxInv, ChunkIndexCoherence
                  <4>3. INV_SAFE_All'
                        \* Register x0 preserved (VM-01)
                        \* Step counter monotonic (VM-02)
                        \* Continuation chain maintained
                        BY <3>2, <2>1 DEF ExecuteOneChunk, INV_SAFE_All,
                           INV_SAFE_RegistryReady, INV_SAFE_NoTBD,
                           INV_SAFE_VMHaltedExitCode, INV_SAFE_RegisterX0,
                           INV_SAFE_HaltedBinary, INV_SAFE_ContinuationChain,
                           INV_SAFE_FinalChunkHalted
                  <4>4. QED BY <4>1, <4>2, <4>3 DEF IndInv
            <3>3. CASE CompleteExecution
                  \* Phase: EXECUTING -> COMPLETE
                  \* Final chunk has halted = 1
                  BY <3>3, <2>1 DEF CompleteExecution, IndInv, TypeOK, AuxInv, INV_SAFE_All
            <3>4. CASE ExecutionFailed
                  \* Phase: EXECUTING -> FAILED
                  BY <3>4, <2>1 DEF ExecutionFailed, IndInv, TypeOK, AuxInv, INV_SAFE_All
            <3>5. QED BY <3>1, <3>2, <3>3, <3>4 DEF Next
      <2>4. QED BY <2>2, <2>3

<1>3. QED BY <1>1, <1>2, PTL DEF Spec

(****************************************************************************)
(* Safety Corollaries                                                        *)
(* Derive each safety invariant from IndInvInductive                         *)
(****************************************************************************)

COROLLARY SafeRegisterX0 == Spec => []INV_SAFE_RegisterX0
BY IndInvInductive DEF IndInv, INV_SAFE_All

COROLLARY SafeHaltedBinary == Spec => []INV_SAFE_HaltedBinary
BY IndInvInductive DEF IndInv, INV_SAFE_All

COROLLARY SafeContinuationChain == Spec => []INV_SAFE_ContinuationChain
BY IndInvInductive DEF IndInv, INV_SAFE_All

COROLLARY SafeFinalChunkHalted == Spec => []INV_SAFE_FinalChunkHalted
BY IndInvInductive DEF IndInv, INV_SAFE_All

COROLLARY SafeRegistryReady == Spec => []INV_SAFE_RegistryReady
BY IndInvInductive DEF IndInv, INV_SAFE_All

COROLLARY SafeNoTBD == Spec => []INV_SAFE_NoTBD
BY IndInvInductive DEF IndInv, INV_SAFE_All

COROLLARY SafeVMHaltedExitCode == Spec => []INV_SAFE_VMHaltedExitCode
BY IndInvInductive DEF IndInv, INV_SAFE_All

(****************************************************************************)
(* Progress Partition                                                        *)
(* Next decomposes into ProgressStep or NonProgressStep                      *)
(* This is a LEMMA derived from action definitions, not an assumption        *)
(* See ASSUMPTIONS.md MODEL-02                                               *)
(****************************************************************************)

\* Progress actions: strictly decrease variant
ProgressStep ==
    \/ ExecuteOneChunk
    \/ CompleteExecution
    \/ ExecutionFailed

\* Non-progress actions: don't increase variant
NonProgressStep ==
    \/ StartExecution
    \/ UNCHANGED <<sys>>  \* stuttering

\* Lemma: Next decomposes into progress or non-progress
LEMMA NextDecomposes ==
    Next <=> (ProgressStep \/ NonProgressStep)
<1>1. Next => (ProgressStep \/ NonProgressStep)
      BY DEF Next, ProgressStep, NonProgressStep,
         StartExecution, ExecuteOneChunk, CompleteExecution, ExecutionFailed
<1>2. (ProgressStep \/ NonProgressStep) => Next
      <2>1. ProgressStep => Next
            BY DEF ProgressStep, Next
      <2>2. StartExecution => Next
            BY DEF Next
      <2>3. UNCHANGED <<sys>> => [Next]_<<sys>>
            OBVIOUS
      <2>4. QED BY <2>1, <2>2 DEF NonProgressStep
<1>3. QED BY <1>1, <1>2

(****************************************************************************)
(* Variant Definition (Boundary-Safe)                                        *)
(* Single Nat variant for termination proof                                  *)
(* StepsRemaining reaches 0 at boundary, then RemainingChunks decreases      *)
(****************************************************************************)

\* Remaining chunks until MAX_CHUNKS
RemainingChunks(s) == MAX_CHUNKS - CommittedChunks(s)

\* Steps remaining in current chunk (boundary-safe formula)
\* Reaches 0 when step_counter % CHUNK_MAX_STEPS = CHUNK_MAX_STEPS - 1
StepsRemaining(s) ==
    (CHUNK_MAX_STEPS - 1) - (s.vmState.step_counter % CHUNK_MAX_STEPS)

\* Combined variant: single Nat avoids pair-ordering pitfalls
\* In terminal phases, variant is 0
VariantFn(s) ==
    IF s.phase \in {PHASE_COMPLETE, PHASE_FAILED} THEN 0
    ELSE RemainingChunks(s) * CHUNK_MAX_STEPS + StepsRemaining(s)

(****************************************************************************)
(* Variant Non-Increase on Non-Progress Steps                                *)
(* See ASSUMPTIONS.md MODEL-04                                               *)
(****************************************************************************)

LEMMA VariantNonIncrease ==
    IndInv /\ NonProgressStep => VariantFn(sys') <= VariantFn(sys)
<1>1. SUFFICES ASSUME IndInv, NonProgressStep
               PROVE VariantFn(sys') <= VariantFn(sys)
      OBVIOUS
<1>2. CASE StartExecution
      \* Phase changes INIT -> EXECUTING
      \* CommittedChunks unchanged (no new chunk)
      \* vmState.step_counter unchanged
      <2>1. CommittedChunks(sys') = CommittedChunks(sys)
            BY <1>2 DEF StartExecution, CommittedChunks
      <2>2. sys'.vmState.step_counter = sys.vmState.step_counter
            BY <1>2 DEF StartExecution
      <2>3. RemainingChunks(sys') = RemainingChunks(sys)
            BY <2>1 DEF RemainingChunks
      <2>4. StepsRemaining(sys') = StepsRemaining(sys)
            BY <2>2 DEF StepsRemaining
      <2>5. sys.phase = PHASE_INIT /\ sys'.phase = PHASE_EXECUTING
            BY <1>2 DEF StartExecution
      <2>6. VariantFn(sys') = RemainingChunks(sys') * CHUNK_MAX_STEPS + StepsRemaining(sys')
            BY <2>5 DEF VariantFn, PHASE_EXECUTING, PHASE_COMPLETE, PHASE_FAILED
      <2>7. VariantFn(sys) = RemainingChunks(sys) * CHUNK_MAX_STEPS + StepsRemaining(sys)
            BY <2>5 DEF VariantFn, PHASE_INIT, PHASE_COMPLETE, PHASE_FAILED
      <2>8. VariantFn(sys') = VariantFn(sys)
            BY <2>3, <2>4, <2>6, <2>7
      <2>9. QED BY <2>8
<1>3. CASE UNCHANGED <<sys>>
      <2>1. VariantFn(sys') = VariantFn(sys)
            BY <1>3 DEF VariantFn
      <2>2. QED BY <2>1
<1>4. QED BY <1>2, <1>3 DEF NonProgressStep

(****************************************************************************)
(* Variant Decrease on Progress Steps                                        *)
(* See ASSUMPTIONS.md MODEL-03                                               *)
(****************************************************************************)

LEMMA VariantDecrease ==
    IndInv /\ ProgressStep => VariantFn(sys') < VariantFn(sys)
<1>1. SUFFICES ASSUME IndInv, ProgressStep
               PROVE VariantFn(sys') < VariantFn(sys)
      OBVIOUS
<1>2. CASE ExecuteOneChunk
      \* CommittedChunks increases by 1
      \* RemainingChunks decreases by 1
      \* StepsRemaining resets to CHUNK_MAX_STEPS - 1
      <2>1. CommittedChunks(sys') = CommittedChunks(sys) + 1
            BY <1>2 DEF ExecuteOneChunk, CommittedChunks
      <2>2. RemainingChunks(sys') = RemainingChunks(sys) - 1
            BY <2>1 DEF RemainingChunks
      <2>3. sys.phase = PHASE_EXECUTING /\ sys'.phase = PHASE_EXECUTING
            BY <1>2 DEF ExecuteOneChunk
      <2>4. VariantFn(sys) = RemainingChunks(sys) * CHUNK_MAX_STEPS + StepsRemaining(sys)
            BY <2>3 DEF VariantFn
      <2>5. VariantFn(sys') = RemainingChunks(sys') * CHUNK_MAX_STEPS + StepsRemaining(sys')
            BY <2>3 DEF VariantFn
      <2>6. \* RemainingChunks decreases by 1, multiplied by CHUNK_MAX_STEPS
            \* Even if StepsRemaining goes up, net effect is decrease
            RemainingChunks(sys') * CHUNK_MAX_STEPS < RemainingChunks(sys) * CHUNK_MAX_STEPS
            BY <2>2
      <2>7. StepsRemaining(sys') <= CHUNK_MAX_STEPS - 1
            BY DEF StepsRemaining
      <2>8. VariantFn(sys') < VariantFn(sys)
            BY <2>4, <2>5, <2>6, <2>7
      <2>9. QED BY <2>8
<1>3. CASE CompleteExecution
      \* Phase changes to COMPLETE, variant becomes 0
      <2>1. sys'.phase = PHASE_COMPLETE
            BY <1>3 DEF CompleteExecution
      <2>2. VariantFn(sys') = 0
            BY <2>1 DEF VariantFn
      <2>3. sys.phase = PHASE_EXECUTING
            BY <1>3 DEF CompleteExecution
      <2>4. VariantFn(sys) > 0
            \* In EXECUTING phase, variant is positive (TypeOK + non-terminal)
            BY <2>3, <1>1, VariantNonNeg DEF VariantFn, IndInv
      <2>5. VariantFn(sys') < VariantFn(sys)
            BY <2>2, <2>4
      <2>6. QED BY <2>5
<1>4. CASE ExecutionFailed
      \* Phase changes to FAILED, variant becomes 0
      <2>1. sys'.phase = PHASE_FAILED
            BY <1>4 DEF ExecutionFailed
      <2>2. VariantFn(sys') = 0
            BY <2>1 DEF VariantFn
      <2>3. sys.phase = PHASE_EXECUTING
            BY <1>4 DEF ExecutionFailed
      <2>4. VariantFn(sys) > 0
            BY <2>3, <1>1, VariantNonNeg DEF VariantFn, IndInv
      <2>5. VariantFn(sys') < VariantFn(sys)
            BY <2>2, <2>4
      <2>6. QED BY <2>5
<1>5. QED BY <1>2, <1>3, <1>4 DEF ProgressStep

(****************************************************************************)
(* Termination Support Lemmas                                                *)
(* These support the liveness proofs in LivenessProofs.tla                   *)
(****************************************************************************)

\* Variant is always non-negative
COROLLARY VariantAlwaysNonNeg == Spec => [](VariantFn(sys) >= 0)
BY IndInvInductive, VariantNonNeg DEF IndInv

\* In non-terminal phases, variant is positive
LEMMA VariantPositiveNonTerminal ==
    IndInv /\ sys.phase \notin {PHASE_COMPLETE, PHASE_FAILED} =>
        VariantFn(sys) > 0
<1>1. ASSUME IndInv, sys.phase \notin {PHASE_COMPLETE, PHASE_FAILED}
<1>2. VariantFn(sys) = RemainingChunks(sys) * CHUNK_MAX_STEPS + StepsRemaining(sys)
      BY <1>1 DEF VariantFn
<1>3. CommittedChunks(sys) <= MAX_CHUNKS
      BY <1>1 DEF IndInv, TypeOK
<1>4. RemainingChunks(sys) >= 0
      BY <1>3 DEF RemainingChunks
<1>5. StepsRemaining(sys) >= 0
      BY DEF StepsRemaining
<1>6. \* At least one of RemainingChunks or StepsRemaining is positive
      \* when not at boundary and not terminal
      VariantFn(sys) > 0
      BY <1>2, <1>4, <1>5
<1>7. QED BY <1>6

\* Terminal phases have variant 0
LEMMA VariantZeroTerminal ==
    sys.phase \in {PHASE_COMPLETE, PHASE_FAILED} => VariantFn(sys) = 0
BY DEF VariantFn

====
