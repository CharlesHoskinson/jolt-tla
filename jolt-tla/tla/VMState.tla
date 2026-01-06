(****************************************************************************)
(* Module: VMState.tla                                                      *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE VMState ----
(****************************************************************************)
(* Purpose: RISC-V VM state machine for deterministic guest execution       *)
(* Appendix J Reference: J.5 (Guest VM), J.10.5 (VMStateV1)                 *)
(* Version: 1.0                                                             *)
(* Notes: ExecuteStep has Assert type guard. VMStateTypeOK uses predicate   *)
(*        form to avoid exponential set enumeration.                        *)
(****************************************************************************)
EXTENDS Types, SMT, SMTOps, Sequences

(****************************************************************************)
(* CONSTANTS                                                                 *)
(****************************************************************************)

CONSTANTS
    \* Abstract step function: VMState -> VMState
    \* Models deterministic instruction execution
    \* Declared as operator constant to avoid TLC trying to enumerate VMStateV1
    \* when checking function membership (STEP_FN \in [VMStateV1 -> VMStateV1]).
    \* Type safety is ensured by the cfg file operator definition.
    STEP_FN(_),

    \* Entry point address
    ENTRY_POINT,

    \* Memory region configuration
    RW_REGION_BASE,
    RW_REGION_SIZE,
    IO_REGION_BASE,
    IO_REGION_SIZE

ASSUME ENTRY_POINT \in U64
ASSUME RW_REGION_BASE \in Nat /\ RW_REGION_SIZE \in Nat
ASSUME IO_REGION_BASE \in Nat /\ IO_REGION_SIZE \in Nat

(****************************************************************************)
(* VMStateV1 Type Definition (J.10.5)                                       *)
(****************************************************************************)

\* Configuration tag entry: (name, value) pair
\* For TLC tractability: all values are serialized as strings
\* (Actual implementation uses byte encodings per J.2.8)
ConfigTag == [name: STRING, value: STRING]

ConfigTagTypeOK(tag) ==
    /\ tag.name \in STRING
    /\ tag.value \in STRING

\* VMStateV1 record matching J.10.5 exactly
VMStateV1 == [
    regs: RegisterFile,             \* 32 u64 registers (x0-x31)
    pc: U64,                        \* Program counter
    step_counter: StepCounter,      \* Total instructions executed
    rw_mem_root_bytes32: Bytes32,   \* RW memory SMT root
    io_root_bytes32: Bytes32,       \* I/O memory SMT root
    halted: HaltedFlag,             \* 0 = running, 1 = terminated
    exit_code: U64,                 \* Exit status (valid when halted=1)
    config_tags: Seq(ConfigTag)     \* Registry projection (J.2.8)
]

(****************************************************************************)
(* Initial VM State (J.5.8)                                                 *)
(****************************************************************************)

\* ABI register indices
REG_A0 == 10    \* Input pointer
REG_A1 == 11    \* Input length
REG_A2 == 12    \* Output pointer
REG_A3 == 13    \* Output max
REG_A4 == 14    \* Batch nonce
REG_SP == 2     \* Stack pointer

\* Construct initial register file with ABI registers set
InitRegisters(inputPtr, inputLen, outputPtr, outputMax, batchNonce, stackPtr) ==
    [i \in RegisterIndex |->
        CASE i = 0 -> 0              \* x0 is hardwired zero
          [] i = REG_A0 -> inputPtr
          [] i = REG_A1 -> inputLen
          [] i = REG_A2 -> outputPtr
          [] i = REG_A3 -> outputMax
          [] i = REG_A4 -> batchNonce
          [] i = REG_SP -> stackPtr
          [] OTHER -> 0              \* All other registers are zero
    ]

\* Construct initial VM state
InitVMState(inputPtr, inputLen, outputPtr, outputMax, batchNonce, stackPtr,
            initialRWRoot, initialIORoot, configTags) ==
    [
        regs |-> InitRegisters(inputPtr, inputLen, outputPtr, outputMax,
                               batchNonce, stackPtr),
        pc |-> ENTRY_POINT,
        step_counter |-> 0,
        rw_mem_root_bytes32 |-> initialRWRoot,
        io_root_bytes32 |-> initialIORoot,
        halted |-> 0,
        exit_code |-> 0,
        config_tags |-> configTags
    ]

(****************************************************************************)
(* VM State Predicates                                                       *)
(****************************************************************************)

\* Is the VM still running?
IsRunning(state) == state.halted = 0

\* Has the VM halted?
IsHalted(state) == state.halted = 1

\* Did the VM halt successfully?
IsSuccessfulHalt(state) ==
    /\ IsHalted(state)
    /\ state.exit_code = JOLT_STATUS_OK

\* Did the VM trap?
IsTrappedHalt(state) ==
    /\ IsHalted(state)
    /\ IsVmTrap(state.exit_code)

\* Get exit code as status code (only valid when halted)
GetExitStatus(state) ==
    IF IsHalted(state)
    THEN state.exit_code
    ELSE 0

(****************************************************************************)
(* Register Access                                                           *)
(****************************************************************************)

\* Read register (x0 always returns 0; out-of-range indices read as 0)
ReadReg(state, idx) ==
    IF idx = 0
    THEN 0
    ELSE IF idx \in RegisterIndex
         THEN state.regs[idx]
         ELSE 0

\* Write register (x0 writes are ignored; out-of-range indices are no-ops)
WriteReg(state, idx, value) ==
    IF idx = 0 \/ idx \notin RegisterIndex
    THEN state
    ELSE [state EXCEPT !.regs[idx] = value]

(****************************************************************************)
(* Step Execution (Abstract)                                                 *)
(****************************************************************************)

\* Execute one instruction step
\* This is modeled abstractly via STEP_FN constant
\* Real implementation would decode and execute RISC-V instructions
\* MEDIUM FIX: Added type guard to verify STEP_FN returns valid VMState
ExecuteStep(state) ==
    IF IsHalted(state)
    THEN state  \* No-op if already halted
    ELSE LET result == STEP_FN(state)
             \* Type guard: verify STEP_FN returned a valid state
             \* This catches malformed STEP_FN implementations at runtime
             typeOK == /\ result.halted \in {0, 1}
                       /\ result.exit_code \in 0..255
                       /\ result.step_counter >= state.step_counter
         IN  IF Assert(typeOK, "STEP_FN returned invalid VMState")
             THEN result
             ELSE state  \* Unreachable: Assert fails if typeOK is FALSE

\* Execute N steps
RECURSIVE ExecuteNSteps(_, _)
ExecuteNSteps(state, n) ==
    IF n = 0 \/ IsHalted(state)
    THEN state
    ELSE ExecuteNSteps(ExecuteStep(state), n - 1)

(****************************************************************************)
(* Halt Transitions (J.5.9)                                                 *)
(****************************************************************************)

\* Normal exit via syscall (J.5.8.3)
\* exit_code comes from low 8 bits of a0
NormalExit(state, exitCodeFromA0) ==
    [state EXCEPT
        !.halted = 1,
        !.exit_code = exitCodeFromA0 % 256
    ]

\* Trap with specific status code
TrapWith(state, trapCode) ==
    [state EXCEPT
        !.halted = 1,
        !.exit_code = trapCode
    ]

\* Trap: Illegal instruction (J.5.9.3)
TrapIllegalInstruction(state) ==
    TrapWith(state, JOLT_STATUS_TRAP_ILLEGAL_INSTRUCTION)

\* Trap: Bad memory access (J.5.9.3)
TrapBadMemory(state) ==
    TrapWith(state, JOLT_STATUS_TRAP_BAD_MEMORY)

\* Trap: Forbidden syscall (J.5.9.3)
TrapForbiddenSyscall(state) ==
    TrapWith(state, JOLT_STATUS_TRAP_FORBIDDEN_SYSCALL)

\* Trap: Out of memory (J.5.9.3)
TrapOOM(state) ==
    TrapWith(state, JOLT_STATUS_TRAP_OOM)

\* Trap: Internal error (J.5.9.3)
TrapInternal(state) ==
    TrapWith(state, JOLT_STATUS_TRAP_INTERNAL)

(****************************************************************************)
(* Step Counter Management                                                   *)
(****************************************************************************)

\* Increment step counter by 1 (J.5.5: uniform increment for all instructions)
IncrementStepCounter(state) ==
    [state EXCEPT !.step_counter = @ + 1]

\* Check if chunk step limit reached
ChunkStepLimitReached(state) ==
    state.step_counter % CHUNK_MAX_STEPS = 0 /\ state.step_counter > 0

\* Get current chunk index
CurrentChunkIndex(state) ==
    state.step_counter \div CHUNK_MAX_STEPS

(****************************************************************************)
(* Memory Root Updates                                                       *)
(****************************************************************************)

\* Update RW memory root after memory write
UpdateRWRoot(state, newRootBytes32) ==
    [state EXCEPT !.rw_mem_root_bytes32 = newRootBytes32]

\* Update IO memory root after I/O write
UpdateIORoot(state, newRootBytes32) ==
    [state EXCEPT !.io_root_bytes32 = newRootBytes32]

\* Update both memory roots
UpdateMemoryRoots(state, newRWRoot, newIORoot) ==
    [state EXCEPT
        !.rw_mem_root_bytes32 = newRWRoot,
        !.io_root_bytes32 = newIORoot
    ]

(****************************************************************************)
(* Type Invariant                                                            *)
(****************************************************************************)

\* Predicate: check RegisterFile type (avoids huge set enumeration)
RegisterFileTypeOK(regs) ==
    /\ DOMAIN regs = RegisterIndex
    /\ \A i \in RegisterIndex : regs[i] \in U64

\* Predicate: check Bytes32 type (avoids huge set enumeration)
Bytes32TypeOK(bytes) ==
    /\ DOMAIN bytes = 0..31
    /\ \A i \in 0..31 : bytes[i] \in Byte

VMStateTypeOK(state) ==
    /\ RegisterFileTypeOK(state.regs)
    /\ state.pc \in U64
    /\ state.step_counter \in StepCounter
    /\ Bytes32TypeOK(state.rw_mem_root_bytes32)
    /\ Bytes32TypeOK(state.io_root_bytes32)
    /\ state.halted \in HaltedFlag
    /\ state.exit_code \in U64
    /\ \A i \in 1..Len(state.config_tags) : ConfigTagTypeOK(state.config_tags[i])

(****************************************************************************)
(* Safety Invariants (J.10.5 Constraints)                                   *)
(****************************************************************************)

\* Constraint 1: halted in {0, 1}
HaltedFlagValid(state) == state.halted \in {0, 1}

\* Constraint 2: If halted = 0, then exit_code = 0
RunningExitCodeZero(state) ==
    state.halted = 0 => state.exit_code = 0

\* Constraint 3: If halted = 1, then exit_code in [0, 255]
HaltedExitCodeValid(state) ==
    state.halted = 1 => state.exit_code \in 0..255

\* Register x0 is always zero (RISC-V spec)
RegisterX0Zero(state) == state.regs[0] = 0

\* Combined VMState safety invariant
VMStateSafetyInvariant(state) ==
    /\ HaltedFlagValid(state)
    /\ RunningExitCodeZero(state)
    /\ HaltedExitCodeValid(state)
    /\ RegisterX0Zero(state)

\* Full VMState invariant (type + safety)
VMStateInvariant(state) ==
    /\ VMStateTypeOK(state)
    /\ VMStateSafetyInvariant(state)

(****************************************************************************)
(* Determinism Property                                                      *)
(* Same state + same inputs -> same next state                              *)
(****************************************************************************)

\* The step function is deterministic
VMStepDeterministic ==
    \A s1, s2 \in VMStateV1 :
        s1 = s2 => ExecuteStep(s1) = ExecuteStep(s2)

(****************************************************************************)
(* State Transition Validity                                                 *)
(* Valid transitions preserve invariants                                     *)
(****************************************************************************)

\* Any valid step preserves the safety invariant
StepPreservesInvariant(state) ==
    VMStateSafetyInvariant(state) =>
        VMStateSafetyInvariant(ExecuteStep(state))

\* Halting is irreversible
HaltIsIrreversible(state) ==
    IsHalted(state) => IsHalted(ExecuteStep(state))

\* Step counter is monotonic
StepCounterMonotonic(state, nextState) ==
    nextState.step_counter >= state.step_counter

(****************************************************************************)
(* State Comparison Helpers                                                  *)
(****************************************************************************)

\* Check if two states have equal core fields (excluding step_counter)
CoreStateEqual(s1, s2) ==
    /\ s1.regs = s2.regs
    /\ s1.pc = s2.pc
    /\ s1.rw_mem_root_bytes32 = s2.rw_mem_root_bytes32
    /\ s1.io_root_bytes32 = s2.io_root_bytes32
    /\ s1.halted = s2.halted
    /\ s1.exit_code = s2.exit_code

\* Full state equality
StateEqual(s1, s2) ==
    /\ CoreStateEqual(s1, s2)
    /\ s1.step_counter = s2.step_counter
    /\ s1.config_tags = s2.config_tags

====
