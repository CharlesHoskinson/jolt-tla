(****************************************************************************)
(* Module: LivenessProofs.tla                                               *)
(* Purpose: Liveness theorems via WF/ENABLED patterns                       *)
(* Part of: Unbounded/infinite-state verification for Jolt                  *)
(* Reference: infinitestate.md Phase 1.6                                    *)
(****************************************************************************)
---- MODULE LivenessProofs ----
(****************************************************************************)
(* This module proves liveness properties under weak fairness:              *)
(*   1. ProgressFromInit: WF(StartExecution) => (INIT ~> not INIT)          *)
(*   2. ProgressFromExecuting: WF(ExecuteChunk) => progress in EXECUTING    *)
(*   3. WrapperTerminates: FairSpec => <>(COMPLETE \/ FAILED)               *)
(*                                                                          *)
(* Proof Pattern (Merz):                                                    *)
(* For P ~> Q under WF(A):                                                  *)
(*   1. P => ENABLED <<A>>_vars                                             *)
(*   2. P /\ <<A>>_vars => Q'                                               *)
(*   3. P /\ [Next]_vars => P' \/ Q'                                        *)
(*   4. P /\ [Next]_vars => (P' => (ENABLED <<A>>_vars)')                   *)
(*                                                                          *)
(* CONTINGENCY: If TLAPS ENABLED proofs become unstable, use Lean as        *)
(* primary liveness oracle (see ASSUMPTIONS.md UNW-02).                     *)
(****************************************************************************)
EXTENDS SafetyInduction, TLAPS

(****************************************************************************)
(* Fair Specification                                                        *)
(****************************************************************************)

\* Weak fairness on StartExecution
WF_StartExecution == WF_vars(StartExecution)

\* Weak fairness on ExecuteChunk (ExecuteOneChunk in SafetyInduction)
WF_ExecuteChunk == WF_vars(ExecuteOneChunk)

\* Fair specification: Spec with fairness constraints
FairSpec == Spec /\ WF_StartExecution /\ WF_ExecuteChunk

(****************************************************************************)
(* ENABLED Lemmas                                                            *)
(* These are the key lemmas for WF proofs                                    *)
(****************************************************************************)

\* StartExecution is enabled in INIT phase
LEMMA StartExecutionEnabled ==
    sys.phase = PHASE_INIT => ENABLED <<StartExecution>>_vars
<1>1. ASSUME sys.phase = PHASE_INIT
<1>2. \* Construct witness for enabled action
      \* StartExecution changes phase from INIT to EXECUTING
      \E sys' \in SystemStateType :
          /\ sys'.phase = PHASE_EXECUTING
          /\ sys'.vmState = sys.vmState
          /\ sys'.continuation = sys.continuation
          /\ sys'.programHash = sys.programHash
      BY DEF SystemStateType
<1>3. ENABLED <<StartExecution>>_vars
      \* The witness from <1>2 satisfies StartExecution
      BY <1>1, <1>2 DEF StartExecution, ENABLED
<1>4. QED BY <1>1, <1>3

\* ExecuteOneChunk is enabled in EXECUTING phase when not complete
LEMMA ExecuteChunkEnabled ==
    sys.phase = PHASE_EXECUTING /\ ~sys.continuation.isComplete
        => ENABLED <<ExecuteOneChunk>>_vars
<1>1. ASSUME sys.phase = PHASE_EXECUTING
             /\ ~sys.continuation.isComplete
<1>2. \* ExecuteOneChunk can always add another chunk until complete
      ENABLED <<ExecuteOneChunk>>_vars
      BY <1>1 DEF ExecuteOneChunk, ENABLED
<1>3. QED BY <1>1, <1>2

\* At least one progress action is enabled in non-terminal states
LEMMA NonTerminalProgressEnabled ==
    sys.phase \in {PHASE_INIT, PHASE_EXECUTING} =>
        \/ ENABLED <<StartExecution>>_vars
        \/ ENABLED <<ExecuteOneChunk>>_vars
        \/ ENABLED <<CompleteExecution>>_vars
        \/ ENABLED <<ExecutionFailed>>_vars
<1>1. ASSUME sys.phase \in {PHASE_INIT, PHASE_EXECUTING}
<1>2. CASE sys.phase = PHASE_INIT
      <2>1. ENABLED <<StartExecution>>_vars
            BY StartExecutionEnabled, <1>2
      <2>2. QED BY <2>1
<1>3. CASE sys.phase = PHASE_EXECUTING
      <2>1. CASE sys.continuation.isComplete
            <3>1. ENABLED <<CompleteExecution>>_vars
                  BY <1>3, <2>1 DEF CompleteExecution, ENABLED
            <3>2. QED BY <3>1
      <2>2. CASE sys.vmState.isTrappedHalt
            <3>1. ENABLED <<ExecutionFailed>>_vars
                  BY <1>3, <2>2 DEF ExecutionFailed, ENABLED
            <3>2. QED BY <3>1
      <2>3. CASE ~sys.continuation.isComplete /\ ~sys.vmState.isTrappedHalt
            <3>1. ENABLED <<ExecuteOneChunk>>_vars
                  BY ExecuteChunkEnabled, <1>3, <2>3
            <3>2. QED BY <3>1
      <2>4. QED BY <2>1, <2>2, <2>3
<1>4. QED BY <1>1, <1>2, <1>3

(****************************************************************************)
(* Progress from INIT (LIVE_ProgressFromInit)                                *)
(* Under WF(StartExecution), the system leaves INIT phase                    *)
(****************************************************************************)

\* Predicate: system is in INIT phase
InInit == sys.phase = PHASE_INIT

\* Predicate: system is not in INIT phase
NotInInit == sys.phase # PHASE_INIT

THEOREM ProgressFromInit ==
    FairSpec => (InInit ~> NotInInit)
(****************************************************************************)
(* Proof follows Merz pattern:                                              *)
(* 1. InInit => ENABLED <<StartExecution>>_vars                             *)
(* 2. InInit /\ <<StartExecution>>_vars => NotInInit'                       *)
(* 3. InInit /\ [Next]_vars => InInit' \/ NotInInit'                        *)
(* 4. InInit /\ [Next]_vars => (InInit' => ENABLED')                        *)
(****************************************************************************)
<1>1. \* Obligation 1: In INIT, StartExecution is enabled
      InInit => ENABLED <<StartExecution>>_vars
      BY StartExecutionEnabled DEF InInit
<1>2. \* Obligation 2: StartExecution takes us out of INIT
      InInit /\ <<StartExecution>>_vars => NotInInit'
      BY DEF InInit, NotInInit, StartExecution
<1>3. \* Obligation 3: Stuttering stays in INIT, actions go somewhere
      InInit /\ [Next]_vars => InInit' \/ NotInInit'
      <2>1. CASE UNCHANGED vars
            BY <2>1 DEF InInit
      <2>2. CASE Next
            <3>1. CASE StartExecution
                  BY <3>1 DEF NotInInit, StartExecution
            <3>2. CASE ExecuteOneChunk \/ CompleteExecution \/ ExecutionFailed
                  \* These require EXECUTING phase, so InInit is false
                  BY <3>2 DEF InInit, ExecuteOneChunk, CompleteExecution, ExecutionFailed
            <3>3. QED BY <2>2, <3>1, <3>2 DEF Next, Step
      <2>3. QED BY <2>1, <2>2
<1>4. \* Obligation 4: Enabledness stability
      \* While in INIT, StartExecution remains enabled
      InInit /\ [Next]_vars => (InInit' => (ENABLED <<StartExecution>>_vars)')
      <2>1. \* If we're still in INIT after the step, StartExecution is enabled
            ASSUME InInit, [Next]_vars, InInit'
      <2>2. (ENABLED <<StartExecution>>_vars)'
            \* Use <1>1 on primed state: InInit' => ENABLED'
            BY <2>1, StartExecutionEnabled DEF InInit
      <2>3. QED BY <2>1, <2>2
<1>5. QED BY <1>1, <1>2, <1>3, <1>4, PTL DEF FairSpec, WF_StartExecution

(****************************************************************************)
(* Progress from EXECUTING                                                   *)
(* Under WF(ExecuteChunk), either completes or fails                         *)
(****************************************************************************)

\* Predicate: in EXECUTING and not complete
ExecutingNotComplete ==
    sys.phase = PHASE_EXECUTING /\ ~sys.continuation.isComplete

\* Predicate: progress made (either done, failed, or chunk added)
MadeProgress ==
    sys.phase \in {PHASE_COMPLETE, PHASE_FAILED} \/
    sys.continuation.isComplete \/
    sys.continuation.currentChunk > sys.continuation.currentChunk

THEOREM ProgressFromExecuting ==
    FairSpec => (ExecutingNotComplete ~> MadeProgress)
<1>1. ExecutingNotComplete => ENABLED <<ExecuteOneChunk>>_vars
      BY ExecuteChunkEnabled DEF ExecutingNotComplete
<1>2. ExecutingNotComplete /\ <<ExecuteOneChunk>>_vars => MadeProgress'
      BY DEF ExecutingNotComplete, MadeProgress, ExecuteOneChunk
<1>3. ExecutingNotComplete /\ [Next]_vars =>
          ExecutingNotComplete' \/ MadeProgress'
      (* Case split on which action occurs *)
      BY DEF ExecutingNotComplete, MadeProgress, Next, Step
<1>4. ExecutingNotComplete /\ [Next]_vars =>
          (ExecutingNotComplete' => (ENABLED <<ExecuteOneChunk>>_vars)')
      BY <1>1 DEF ExecutingNotComplete
<1>5. QED BY <1>1, <1>2, <1>3, <1>4, PTL DEF FairSpec, WF_ExecuteChunk

(****************************************************************************)
(* Wrapper Termination (Main Liveness Theorem)                               *)
(* Under FairSpec, the system eventually reaches a terminal phase            *)
(****************************************************************************)

\* Terminal phases
IsTerminalPhase == sys.phase \in {PHASE_COMPLETE, PHASE_FAILED}

\* Non-terminal phases
IsNonTerminalPhase == sys.phase \in {PHASE_INIT, PHASE_EXECUTING}

THEOREM WrapperTerminates ==
    FairSpec => <>IsTerminalPhase
(****************************************************************************)
(* Proof Strategy:                                                          *)
(* 1. Variant is bounded (Nat, so well-founded)                             *)
(* 2. Progress steps strictly decrease variant                              *)
(* 3. Non-progress steps don't increase variant                             *)
(* 4. Weak fairness ensures progress steps are taken when enabled           *)
(* 5. At least one progress action is enabled in non-terminal states        *)
(* Therefore, terminal state is eventually reached.                         *)
(****************************************************************************)
<1>1. \* By ProgressFromInit: eventually leave INIT
      FairSpec => (InInit ~> NotInInit)
      BY ProgressFromInit
<1>2. \* By ProgressFromExecuting: eventually leave EXECUTING
      FairSpec => (ExecutingNotComplete ~> MadeProgress)
      BY ProgressFromExecuting
<1>3. \* Terminal phases are absorbing
      IndInv /\ IsTerminalPhase /\ [Next]_vars => IsTerminalPhase'
      BY DEF IndInv, IsTerminalPhase, Next, Step
<1>4. \* Variant argument: variant decreases on progress, bounded below by 0
      \* This uses VariantDecrease and VariantNonIncrease from SafetyInduction
      IndInv /\ IsNonTerminalPhase => VariantFn(sys) > 0
      BY DEF IndInv, IsNonTerminalPhase, VariantFn
<1>5. \* Progress enabled in non-terminal (NonTerminalProgressEnabled)
      IndInv /\ IsNonTerminalPhase =>
          \/ ENABLED <<StartExecution>>_vars
          \/ ENABLED <<ExecuteOneChunk>>_vars
          \/ ENABLED <<CompleteExecution>>_vars
          \/ ENABLED <<ExecutionFailed>>_vars
      BY NonTerminalProgressEnabled DEF IsNonTerminalPhase
<1>6. \* By well-founded induction on variant:
      \* variant decreases, bounded below, fairness forces progress
      \* => eventually variant = 0 => terminal phase
      FairSpec => <>IsTerminalPhase
      BY <1>1, <1>2, <1>3, <1>4, <1>5, PTL, VariantDecrease, VariantNonIncrease
<1>7. QED BY <1>6

(****************************************************************************)
(* Conditional Liveness: VM Halts => Proper Termination                      *)
(****************************************************************************)

\* Assumption: program eventually halts (not an axiom!)
AssumeProgramHalts == <>(sys.vmState.halted = 1)

\* Complete execution (not failed)
ProperCompletion == sys.phase = PHASE_COMPLETE

THEOREM ConditionalProperCompletion ==
    FairSpec /\ AssumeProgramHalts => <>ProperCompletion
<1>1. FairSpec => <>IsTerminalPhase
      BY WrapperTerminates
<1>2. \* If program halts successfully and not trapped, we reach COMPLETE
      AssumeProgramHalts /\ sys.vmState.exit_code = JOLT_STATUS_OK =>
          <>ProperCompletion
      BY DEF AssumeProgramHalts, ProperCompletion, CompleteExecution
<1>3. QED BY <1>1, <1>2, PTL

(****************************************************************************)
(* Leads-To Composition                                                      *)
(****************************************************************************)

\* Complete liveness chain: Init ~> Terminal
THEOREM InitLeadsToTerminal ==
    FairSpec => (InInit ~> IsTerminalPhase)
<1>1. FairSpec => (InInit ~> NotInInit)
      BY ProgressFromInit
<1>2. \* After leaving INIT, either in EXECUTING or already terminal
      NotInInit => (sys.phase = PHASE_EXECUTING \/ IsTerminalPhase)
      BY DEF NotInInit, IsTerminalPhase
<1>3. \* From EXECUTING, eventually terminal (by variant argument)
      FairSpec => (sys.phase = PHASE_EXECUTING ~> IsTerminalPhase)
      (* Uses variant decrease + fairness *)
      BY VariantDecrease, VariantNonIncrease, PTL
<1>4. \* Compose: Init ~> NotInit and NotInit ~> Terminal
      FairSpec => (InInit ~> IsTerminalPhase)
      BY <1>1, <1>2, <1>3, PTL
<1>5. QED BY <1>4

(****************************************************************************)
(* Fairness Obligation Summary                                               *)
(****************************************************************************)

\* All fairness requirements for complete liveness
\* FAIR-01: WF(StartExecution) - ensures leaving INIT
\* FAIR-02: WF(ExecuteChunk) - ensures progress in EXECUTING

====
