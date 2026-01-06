---------------------------- MODULE JoltContinuations ----------------------------
(****************************************************************************)
(* JOLT CONTINUATION FORMAL SPECIFICATION                                   *)
(* ======================================================================== *)
(*                                                                          *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(*                                                                          *)
(* This TLA+ specification formally models the Jolt zkVM continuation       *)
(* mechanism for chunk-based proving. It is the machine-checkable           *)
(* companion to the prose specification (spec.md).                          *)
(*                                                                          *)
(* Repository: https://github.com/CharlesHoskinson/jolt-tla                 *)
(*                                                                          *)
(* WHAT THIS SPECIFIES:                                                     *)
(*   - VMState: RISC-V VM state (registers, PC, memory roots, halt flag)    *)
(*   - Continuations: Chunk-based execution with state digests              *)
(*   - StateDigest: Cryptographic commitment to VM state at boundaries      *)
(*   - SMT: Sparse Merkle Tree for memory commitment                        *)
(*   - Transcript: Fiat-Shamir transcript construction                      *)
(*   - Invariants: 26 individual + 6 composite safety/attack properties     *)
(*                                                                          *)
(* HOW TO RUN:                                                              *)
(*   java -jar tla2tools.jar -config Jolt.cfg JoltContinuations.tla         *)
(*                                                                          *)
(* REFERENCES:                                                              *)
(*   - Jolt Paper: ePrint 2023/1217                                         *)
(*   - Prose Spec: spec.md                                                   *)
(*                                                                          *)
(****************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

(****************************************************************************)
(* SECTION 1: CONSTANTS AND CONFIGURATION                                   *)
(* ======================================================================== *)
(* These constants control model checking bounds. Production implementations*)
(* use much larger values (e.g., CHUNK_MAX_STEPS ~ 10^6).                   *)
(****************************************************************************)

CONSTANTS
    CHUNK_MAX_STEPS,        \* Max VM steps per chunk (TLC: 2, Prod: ~10^6)
    MAX_CHUNKS,             \* Max chunks in continuation (TLC: 3)
    NUM_REGISTERS,          \* RISC-V register count (always 32)
    FR_MODULUS,             \* BLS12-381 scalar field modulus (abstracted)
    FR_TLC_BOUND,           \* TLC bound for Fr arithmetic
    U64_TLC_BOUND,          \* TLC bound for u64 values
    PAGE_INDEX_TLC_BOUND,   \* TLC bound for memory page indices
    MAX_DIRTY_PAGES,        \* Max dirty pages per chunk
    MAX_ABSORPTIONS         \* Max transcript absorptions

(****************************************************************************)
(* SECTION 2: CONSTANT ASSUMPTIONS                                          *)
(* ======================================================================== *)
(* These ASSUME statements are checked by SANY and document constraints.    *)
(****************************************************************************)

ASSUME CHUNK_MAX_STEPS \in Nat /\ CHUNK_MAX_STEPS > 0
ASSUME MAX_CHUNKS \in Nat /\ MAX_CHUNKS > 0
ASSUME NUM_REGISTERS = 32           \* Protocol requirement: RV64 has 32 regs
ASSUME FR_MODULUS \in Nat /\ FR_MODULUS > 0
ASSUME FR_TLC_BOUND \in Nat /\ FR_TLC_BOUND > 0 /\ FR_TLC_BOUND <= FR_MODULUS
ASSUME U64_TLC_BOUND \in Nat /\ U64_TLC_BOUND > 0
ASSUME U64_TLC_BOUND <= FR_TLC_BOUND    \* For U64ToFr conversion

(****************************************************************************)
(* SECTION 3: TYPE DEFINITIONS                                              *)
(* ======================================================================== *)
(* Foundation types used throughout the specification.                      *)
(* These correspond to Section 2.4 of the prose specification.              *)
(****************************************************************************)

\* Single byte (0-255)
Byte == 0..255

\* 32-byte array (e.g., SHA-256 outputs, state roots)
\* Index 0 is LSB in little-endian interpretation
Bytes32 == [0..31 -> Byte]

\* Zero-initialized Bytes32
ZeroBytes32 == [i \in 0..31 |-> 0]

\* Field element in BLS12-381 scalar field
\* In production: integers mod r (about 2^255)
\* For TLC: bounded integers [0, FR_TLC_BOUND)
Fr == 0..(FR_TLC_BOUND - 1)

\* Byte-valued field element (0..255), constrained to TLC-bounded Fr
FrByte == 0..(IF FR_TLC_BOUND >= 256 THEN 255 ELSE FR_TLC_BOUND - 1)

\* Pair of field elements for encoding 256-bit values (Section 7.5)
\* lo: low 248 bits (31 bytes), hi: high 8 bits (1 byte)
Fr2 == [lo: Fr, hi: FrByte]

\* 64-bit unsigned integer - TLC-bounded subset
U64 == 0..(U64_TLC_BOUND - 1)

\* Status codes (Section 6)
StatusCode == 0..255

\* Register index (0-31 for RISC-V)
RegisterIndex == 0..(NUM_REGISTERS - 1)

\* Halted flag (0 = running, 1 = terminated)
HaltedFlag == {0, 1}

\* Chunk index for continuation tracking
ChunkIndex == 0..(MAX_CHUNKS - 1)

\* Step counter within execution (bounded for TLC)
StepCounter == 0..((MAX_CHUNKS + 1) * CHUNK_MAX_STEPS)

\* Register file type (32 registers, each a U64)
RegisterFile == [RegisterIndex -> U64]

\* Zero-initialized register file
ZeroRegisters == [i \in RegisterIndex |-> 0]

(****************************************************************************)
(* SECTION 4: STATUS CODES                                                  *)
(* ======================================================================== *)
(* RISC-V VM exit status codes. See Section 6 of prose specification.       *)
(****************************************************************************)

JOLT_STATUS_OK == 0                           \* Successful execution
JOLT_STATUS_TRAP_ILLEGAL_INSTRUCTION == 1     \* Illegal/forbidden instruction
JOLT_STATUS_TRAP_BAD_MEMORY == 2              \* Bad memory access
JOLT_STATUS_TRAP_FORBIDDEN_SYSCALL == 3       \* Disallowed syscall
JOLT_STATUS_TRAP_OOM == 4                     \* Out of memory
JOLT_STATUS_TRAP_INTERNAL == 5                \* Internal VM failure

TrapCodes == {
    JOLT_STATUS_TRAP_ILLEGAL_INSTRUCTION,
    JOLT_STATUS_TRAP_BAD_MEMORY,
    JOLT_STATUS_TRAP_FORBIDDEN_SYSCALL,
    JOLT_STATUS_TRAP_OOM,
    JOLT_STATUS_TRAP_INTERNAL
}

IsVmTrap(code) == code \in TrapCodes
IsSuccess(code) == code = JOLT_STATUS_OK

(****************************************************************************)
(* SECTION 5: TYPE PREDICATES                                               *)
(* ======================================================================== *)
(* Type-checking predicates for compound types.                             *)
(****************************************************************************)

Bytes32TypeOK(b) == DOMAIN b = 0..31 /\ \A i \in 0..31 : b[i] \in Byte
RegisterFileTypeOK(regs) == DOMAIN regs = RegisterIndex /\ \A i \in RegisterIndex : regs[i] \in U64

(****************************************************************************)
(* SECTION 6: ENCODING PRIMITIVES                                           *)
(* ======================================================================== *)
(* Byte/field encoding. See Section 7 of prose specification.               *)
(****************************************************************************)

\* Convert 32 bytes to Fr2 (low 248 bits, high 8 bits)
\* This is how 256-bit values fit into BLS12-381 field elements
Bytes32ToFr2(b) ==
    LET lo == (b[0] + b[1]*256 + b[2]*65536) % FR_TLC_BOUND
        hi == b[31] % FR_TLC_BOUND
    IN [lo |-> lo, hi |-> hi]

\* Interpret first bytes of Bytes32 as Fr (little-endian, truncated)
Bytes32ToFrLE(b) == (b[0] + b[1]*256 + b[2]*65536 + b[3]*16777216) % FR_TLC_BOUND

\* Convert Fr to Bytes32 (little-endian encoding)
FrToBytes32LE(fr) ==
    [i \in 0..31 |-> IF i < 4 THEN (fr \div (256^i)) % 256 ELSE 0]

(****************************************************************************)
(* SECTION 7: HASH FUNCTION ABSTRACTIONS                                    *)
(* ======================================================================== *)
(* Abstract hash functions for model checking. Production uses Poseidon and *)
(* SHA-256. TLC uses fingerprint-based approximations.                      *)
(*                                                                          *)
(* IMPORTANT: These model operators maintain structural correctness but     *)
(* create collisions. This is acceptable for model checking because:        *)
(*   - TLC tests the STRUCTURE of the spec, not cryptographic security      *)
(*   - Production uses proper Poseidon/SHA-256 (collision-resistant)        *)
(*   - INV_ATK_* invariants verify abstract security properties             *)
(****************************************************************************)

\* Domain separation tags (JOLT/ prefix)
TAG_STATE_DIGEST == "JOLT/STATE/V1"
TAG_SMT_PAGE == "JOLT/SMT/PAGE/V1"
TAG_SMT_NODE == "JOLT/SMT/NODE/V1"
TAG_CONFIG_TAGS == "JOLT/CONFIG_TAGS/V1"
TAG_TAG == "JOLT/TAG/V1"

\* Map tag to numeric value for hashing
TagToNat(tag) ==
    CASE tag = "JOLT/SMT/PAGE/V1" -> 1
      [] tag = "JOLT/SMT/NODE/V1" -> 2
      [] tag = "JOLT/STATE/V1" -> 3
      [] tag = "JOLT/BATCH/COMMIT/V1" -> 4
      [] tag = "JOLT/CHECKPOINTS/DIGEST/V1" -> 5
      [] tag = "JOLT/IO/INIT/V1" -> 6
      [] tag = "JOLT/CONFIG_TAGS/V1" -> 7
      [] tag = "JOLT/TAG/V1" -> 8
      [] OTHER -> 0

\* Poseidon hash (domain-separated, returns Fr)
PoseidonHashV1(tag, data) ==
    (TagToNat(tag) * 100000 + (IF data \in Nat THEN data ELSE 0)) % FR_TLC_BOUND

PoseidonHashBytes(tag, data) == PoseidonHashV1(tag, data)

\* SHA-256 hash (returns Bytes32)
SHA256Hash(input) ==
    LET fp == IF input \in Nat THEN input ELSE Len(ToString(input))
    IN [i \in 0..31 |-> (fp + i * 17) % 256]

(****************************************************************************)
(* SECTION 8: SMT (SPARSE MERKLE TREE)                                      *)
(* ======================================================================== *)
(* Memory commitment structure. See Section 11.8 of prose specification.    *)
(****************************************************************************)

SMT_DEPTH == 32                     \* Tree depth (32 levels for 32-bit addresses)
SMT_EMPTY_LEAF_HASH == 0            \* Hash of empty leaf
PageIndex == 0..(PAGE_INDEX_TLC_BOUND - 1)  \* Page indices for TLC

\* SMT root is an Fr value
SMTRoot == Fr

\* Empty tree has a specific root hash
EmptyTreeRoot == SMT_EMPTY_LEAF_HASH

\* Convert root to Bytes32 representation
RootToBytes32(root) == FrToBytes32LE(root)

(****************************************************************************)
(* SECTION 9: MEMORY MAP                                                    *)
(* ======================================================================== *)
(* Guest VM memory layout. See Section 6 of prose specification.            *)
(****************************************************************************)

PAGE_SIZE_BYTES == 4096             \* 4KB pages
IO_REGION_BASE == 0                 \* I/O region start
IO_REGION_SIZE == 4 * PAGE_SIZE_BYTES
RW_REGION_BASE == IO_REGION_SIZE    \* Read-write region start
RW_REGION_SIZE == 8 * PAGE_SIZE_BYTES

\* Memory regions
MemRegion == [base: U64, size: U64]

\* Check if address is in I/O region
IsIOAddress(addr) == addr >= IO_REGION_BASE /\ addr < IO_REGION_BASE + IO_REGION_SIZE

\* Check if address is in RW region
IsRWAddress(addr) == addr >= RW_REGION_BASE /\ addr < RW_REGION_BASE + RW_REGION_SIZE

(****************************************************************************)
(* SECTION 10: CONFIGURATION TAGS                                           *)
(* ======================================================================== *)
(* Registry configuration. See Section 3 of prose specification.            *)
(****************************************************************************)

\* Config tag record
ConfigTag == [name: STRING, value: STRING]
ConfigTagSeq == Seq(ConfigTag)

\* Registry keys
KEY_SPEC_VERSION == "JOLT_SPEC_VERSION_V1"
KEY_MAX_MANIFEST_BYTES == "JOLT_MAX_MANIFEST_BYTES_V1"
KEY_MAX_INTENTS == "JOLT_MAX_INTENTS_V1"
KEY_MAX_CHECKPOINTS_BYTES == "JOLT_MAX_CHECKPOINTS_BYTES_V1"
KEY_CONTEXT_BYTES32 == "JOLT_CONTEXT_BYTES32_V1"

RequiredKeys == {
    KEY_SPEC_VERSION,
    KEY_MAX_MANIFEST_BYTES,
    KEY_MAX_INTENTS,
    KEY_MAX_CHECKPOINTS_BYTES,
    KEY_CONTEXT_BYTES32
}

\* Registry entry
RegistryEntry == [key: STRING, value: STRING, required: BOOLEAN, validated: BOOLEAN]
RegistryState == [RequiredKeys -> RegistryEntry]

\* Check if registry is deployment-ready (no TBD values)
RegistryDeploymentReady(registry) ==
    \A k \in RequiredKeys : registry[k].validated /\ registry[k].value # "TBD"

NoTBDInvariant(registry) == RegistryDeploymentReady(registry)

RegistryStateTypeOK(registry) ==
    /\ DOMAIN registry = RequiredKeys
    /\ \A k \in RequiredKeys : registry[k].key \in STRING

\* Compute config_tags from registry
ComputeConfigTags(registry) ==
    << [name |-> KEY_SPEC_VERSION, value |-> registry[KEY_SPEC_VERSION].value] >>

(****************************************************************************)
(* SECTION 11: VM STATE                                                     *)
(* ======================================================================== *)
(* RISC-V VM state record. See Section 11.5 of prose specification.         *)
(****************************************************************************)

REG_A0 == 10    \* Argument registers
REG_A1 == 11
REG_A2 == 12
REG_A3 == 13
REG_A4 == 14    \* Batch nonce is passed in A4

VMStateV1 == [
    regs: RegisterFile,             \* 32 registers
    pc: U64,                        \* Program counter
    step_counter: StepCounter,      \* Steps executed
    rw_mem_root_bytes32: Bytes32,   \* Read-write memory root
    io_root_bytes32: Bytes32,       \* I/O memory root
    halted: HaltedFlag,             \* 0=running, 1=halted
    exit_code: U64,                 \* Exit status
    config_tags: ConfigTagSeq       \* Configuration binding
]

VMStateTypeOK(state) ==
    /\ RegisterFileTypeOK(state.regs)
    /\ state.pc \in U64
    /\ state.step_counter \in StepCounter
    /\ Bytes32TypeOK(state.rw_mem_root_bytes32)
    /\ Bytes32TypeOK(state.io_root_bytes32)
    /\ state.halted \in HaltedFlag
    /\ state.exit_code \in U64

\* Read register (x0 is always 0 in RISC-V)
ReadReg(state, idx) == IF idx = 0 THEN 0 ELSE state.regs[idx]

\* Write register (x0 writes are ignored)
WriteReg(state, idx, val) ==
    IF idx = 0 THEN state
    ELSE [state EXCEPT !.regs[idx] = val]

\* State predicates
IsHalted(state) == state.halted = 1
IsRunning(state) == state.halted = 0
IsSuccessfulHalt(state) == state.halted = 1 /\ state.exit_code = JOLT_STATUS_OK
IsTrappedHalt(state) == state.halted = 1 /\ state.exit_code # JOLT_STATUS_OK

\* Initialize VM state
InitVMState(inputPtr, inputLen, outputPtr, outputSize, batchNonce, stackPtr,
            initialRWRoot, initialIORoot, configTags) ==
    [regs |-> [i \in RegisterIndex |->
                   CASE i = REG_A0 -> inputPtr
                     [] i = REG_A1 -> inputLen
                     [] i = REG_A2 -> outputPtr
                     [] i = REG_A3 -> outputSize
                     [] i = REG_A4 -> batchNonce
                     [] OTHER -> IF i = 2 THEN stackPtr ELSE 0],
     pc |-> 0,
     step_counter |-> 0,
     rw_mem_root_bytes32 |-> initialRWRoot,
     io_root_bytes32 |-> initialIORoot,
     halted |-> 0,
     exit_code |-> 0,
     config_tags |-> configTags]

\* Execute N steps (model: increment counter, halt when limit reached)
VM_TERMINATE_AFTER == CHUNK_MAX_STEPS * (MAX_CHUNKS + 1)

ExecuteOneStep(state) ==
    IF state.halted = 1 THEN state
    ELSE LET nextCounter == state.step_counter + 1
             shouldHalt == nextCounter >= VM_TERMINATE_AFTER
         IN [state EXCEPT !.step_counter = nextCounter,
                          !.halted = IF shouldHalt THEN 1 ELSE 0,
                          !.exit_code = IF shouldHalt THEN JOLT_STATUS_OK ELSE 0]

ExecuteNSteps(state, n) ==
    LET RECURSIVE Exec(_, _)
        Exec(s, remaining) ==
            IF remaining = 0 \/ s.halted = 1 THEN s
            ELSE Exec(ExecuteOneStep(s), remaining - 1)
    IN Exec(state, n)

(****************************************************************************)
(* SECTION 12: STATE DIGEST                                                 *)
(* ======================================================================== *)
(* Cryptographic commitment to VM state. See Section 11.10.                 *)
(*                                                                          *)
(* StateDigestV1 Algorithm (14 steps in production):                        *)
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
(****************************************************************************)

\* Helper: sum of a finite set
SumSet(S) == LET RECURSIVE Sum(_)
                 Sum(s) == IF s = {} THEN 0
                           ELSE LET x == CHOOSE x \in s : TRUE
                                IN x + Sum(s \ {x})
             IN Sum(S)

\* Serialize VMState for hashing (model: weighted sum of fields)
SerializeVMStateWithProgram(program_hash_bytes32, state) ==
    LET regSum == SumSet({state.regs[i] : i \in DOMAIN state.regs})
        progHashContrib == SumSet({program_hash_bytes32[i] : i \in DOMAIN program_hash_bytes32})
        configTagsContrib == IF Len(state.config_tags) > 0
                             THEN SumSet({Len(state.config_tags[i].name) + Len(state.config_tags[i].value) :
                                          i \in 1..Len(state.config_tags)})
                             ELSE 0
        rwRootContrib == SumSet({state.rw_mem_root_bytes32[i] : i \in DOMAIN state.rw_mem_root_bytes32})
        ioRootContrib == SumSet({state.io_root_bytes32[i] : i \in DOMAIN state.io_root_bytes32})
    IN (progHashContrib % 1000) * 100000
       + (configTagsContrib % 100) * 10000
       + ((rwRootContrib + ioRootContrib) % 100) * 1000
       + (state.step_counter % 100) * 100
       + (state.pc % 10) * 10
       + state.halted * 5
       + (state.exit_code % 5)
       + (regSum % 5)

\* Compute StateDigestV1 from program hash and VMState
ComputeStateDigest(program_hash_bytes32, state) ==
    PoseidonHashV1(TAG_STATE_DIGEST, SerializeVMStateWithProgram(program_hash_bytes32, state))

StateDigest == Fr

(****************************************************************************)
(* SECTION 13: CHUNK RECORDS AND EXECUTION TRACE                            *)
(* ======================================================================== *)
(* Chunk-based execution model. See Section 11 of prose specification.      *)
(****************************************************************************)

ChunkRecord == [
    program_hash_bytes32: Bytes32,  \* Program identity
    chunkIndex: ChunkIndex,
    stateIn: VMStateV1,
    digestIn: StateDigest,
    stateOut: VMStateV1,
    digestOut: StateDigest,
    stepsExecuted: Nat,
    isFinal: BOOLEAN
]

MakeChunkRecord(program_hash_bytes32, idx, stateIn, stateOut) ==
    [program_hash_bytes32 |-> program_hash_bytes32,
     chunkIndex |-> idx,
     stateIn |-> stateIn,
     digestIn |-> ComputeStateDigest(program_hash_bytes32, stateIn),
     stateOut |-> stateOut,
     digestOut |-> ComputeStateDigest(program_hash_bytes32, stateOut),
     stepsExecuted |-> stateOut.step_counter - stateIn.step_counter,
     isFinal |-> IsHalted(stateOut)]

ExecutionTrace == Seq(ChunkRecord)

\* The CORE SECURITY PROPERTY: Continuity invariant
\* Adjacent chunks must have matching digests (output of i = input of i+1)
ContinuityInvariant(chunks) ==
    \A i \in 1..(Len(chunks) - 1) :
        chunks[i].digestOut = chunks[i + 1].digestIn

\* No gaps in chunk sequence
NoSkippedChunks(chunks) ==
    \A i \in 1..Len(chunks) : chunks[i].chunkIndex = i - 1

\* Config tags must be consistent across all chunks
ConfigConsistentAcrossChunks(chunks) ==
    \A i, j \in 1..Len(chunks) :
        chunks[i].stateIn.config_tags = chunks[j].stateIn.config_tags

\* Extract initial/final states from trace
TraceInitialState(trace) == trace[1].stateIn
TraceFinalState(trace) == trace[Len(trace)].stateOut
TraceInitialDigest(trace) == trace[1].digestIn
TraceFinalDigest(trace) == trace[Len(trace)].digestOut
FinalExitStatus(trace) == TraceFinalState(trace).exit_code

(****************************************************************************)
(* SECTION 14: CONTINUATION STATE MACHINE                                   *)
(* ======================================================================== *)
(* Models progression through chunks.                                        *)
(****************************************************************************)

ContinuationState == [
    program_hash_bytes32: Bytes32,
    currentChunk: Nat,
    chunks: ExecutionTrace,
    complete: BOOLEAN,
    initialDigest: StateDigest,
    finalDigest: StateDigest
]

InitContinuation(program_hash_bytes32, initialState) ==
    [program_hash_bytes32 |-> program_hash_bytes32,
     currentChunk |-> 0,
     chunks |-> << >>,
     complete |-> FALSE,
     initialDigest |-> ComputeStateDigest(program_hash_bytes32, initialState),
     finalDigest |-> 0]

ExecuteChunk(cont, stateIn, stateOut) ==
    LET chunk == MakeChunkRecord(cont.program_hash_bytes32, cont.currentChunk, stateIn, stateOut)
        newChunks == Append(cont.chunks, chunk)
        isComplete == chunk.isFinal
    IN [cont EXCEPT !.currentChunk = @ + 1,
                    !.chunks = newChunks,
                    !.complete = isComplete,
                    !.finalDigest = IF isComplete THEN chunk.digestOut ELSE @]

ContinuationComplete(cont) == cont.complete

\* Extract state roots from trace
OldStateRoot(trace) == TraceInitialState(trace).rw_mem_root_bytes32
NewStateRoot(trace) == TraceFinalState(trace).rw_mem_root_bytes32

(****************************************************************************)
(* SECTION 15: WRAPPER AND PUBLIC INPUTS                                    *)
(* ======================================================================== *)
(* Halo2 wrapper circuit interface. See Section 5 of prose specification.   *)
(****************************************************************************)

\* The 11 public inputs exposed to on-chain verifier
PublicInputsV1 == [
    program_hash_lo: Fr, program_hash_hi: Fr,
    old_root_lo: Fr, old_root_hi: Fr,
    new_root_lo: Fr, new_root_hi: Fr,
    batch_commitment_lo: Fr, batch_commitment_hi: Fr,
    checkpoints_digest_fr: Fr, status_fr: Fr, batch_nonce_fr: Fr]

\* Public outputs written by Settlement Engine
PublicOutputsV1 == [
    status_u8: Byte, reserved7: [0..6 -> Byte], batch_nonce_u64: U64,
    old_root_bytes32: Bytes32, new_root_bytes32: Bytes32,
    batch_commitment_bytes32: Bytes32, checkpoints_digest_bytes32: Bytes32]

PUBLIC_OUTPUTS_SIZE == 144
ZeroReserved7 == [i \in 0..6 |-> 0]

U64ToFr(u) == u  \* Identity within TLC bounds

\* Construct 11 public inputs from execution trace
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

TrapOutputs(trapCode, batchNonceIn) == [
    status_u8 |-> trapCode % 256, reserved7 |-> ZeroReserved7, batch_nonce_u64 |-> batchNonceIn,
    old_root_bytes32 |-> ZeroBytes32, new_root_bytes32 |-> ZeroBytes32,
    batch_commitment_bytes32 |-> ZeroBytes32, checkpoints_digest_bytes32 |-> ZeroBytes32]

(****************************************************************************)
(* SECTION 16: SMT HELPERS                                                  *)
(* ======================================================================== *)
(* Additional SMT operations.                                                *)
(****************************************************************************)

ComputeInitialIORoot(manifestBytes, inputPtr, inputLen, ioBase) ==
    IF Len(manifestBytes) = 0 THEN EmptyTreeRoot
    ELSE (Len(manifestBytes) + inputPtr) % FR_TLC_BOUND

(****************************************************************************)
(* SECTION 17: SYSTEM STATE MACHINE                                         *)
(* ======================================================================== *)
(* Top-level composition. Four phases: INIT -> EXECUTING -> COMPLETE/FAILED *)
(****************************************************************************)

\* Memory layout
INPUT_PTR == IO_REGION_BASE
OUTPUT_PTR == IO_REGION_BASE + (2 * PAGE_SIZE_BYTES)
STACK_PTR == RW_REGION_BASE + RW_REGION_SIZE

\* Domain tags for batch/checkpoint operations
TAG_BATCH_COMMITMENT == "JOLT/BATCH/COMMIT/V1"
TAG_CHECKPOINTS_DIGEST == "JOLT/CHECKPOINTS/DIGEST/V1"

BatchCommitmentBytes32(manifestBytes) ==
    IF Len(manifestBytes) = 0 THEN ZeroBytes32
    ELSE SHA256Hash(manifestBytes)

CheckpointsDigestFr(trace) ==
    IF Len(trace) = 0 THEN 0
    ELSE PoseidonHashBytes(TAG_CHECKPOINTS_DIGEST, SumSet({trace[i].digestOut : i \in 1..Len(trace)}))

CheckpointsDigestBytes32(trace) == FrToBytes32LE(CheckpointsDigestFr(trace))

\* System phases
PHASE_INIT == "init"
PHASE_EXECUTING == "executing"
PHASE_COMPLETE == "complete"
PHASE_FAILED == "failed"
SystemPhase == {PHASE_INIT, PHASE_EXECUTING, PHASE_COMPLETE, PHASE_FAILED}

\* System state record
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

\* Model init helper
ModelValueForKey(keyName) ==
    CASE keyName = KEY_SPEC_VERSION -> "1.0.0"
      [] keyName = KEY_MAX_MANIFEST_BYTES -> "512"
      [] keyName = KEY_MAX_INTENTS -> "8"
      [] keyName = KEY_MAX_CHECKPOINTS_BYTES -> "256"
      [] keyName = KEY_CONTEXT_BYTES32 -> "CONTEXT1"
      [] OTHER -> "1.0.0"

ModelRegistryEntry(keyName) ==
    [key |-> keyName, value |-> ModelValueForKey(keyName), required |-> TRUE, validated |-> TRUE]

ModelRegistry == [k \in RequiredKeys |-> ModelRegistryEntry(k)]
ModelBytes32 == [i \in 0..31 |-> 0]

Init == sys = InitSystemState(ModelRegistry, ModelBytes32, << >>, 0)

StartExecution ==
    /\ sys.phase = PHASE_INIT
    /\ RegistryDeploymentReady(sys.registry)
    /\ sys' = [sys EXCEPT !.phase = PHASE_EXECUTING]

ExecuteOneChunk ==
    /\ sys.phase = PHASE_EXECUTING
    /\ ~ContinuationComplete(sys.continuation)
    /\ LET stateIn == sys.vmState
           stateOut == ExecuteNSteps(stateIn, CHUNK_MAX_STEPS)
           newCont == ExecuteChunk(sys.continuation, stateIn, stateOut)
       IN sys' = [sys EXCEPT !.vmState = stateOut, !.continuation = newCont]

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

ExecutionFailed ==
    /\ sys.phase = PHASE_EXECUTING
    /\ IsTrappedHalt(sys.vmState)
    /\ sys' = [sys EXCEPT !.phase = PHASE_FAILED,
                          !.publicOutputs = TrapOutputs(sys.vmState.exit_code, sys.batchNonce)]

Next == \/ StartExecution \/ ExecuteOneChunk \/ CompleteExecution \/ ExecutionFailed

Spec == Init /\ [][Next]_sys

(****************************************************************************)
(* SECTION 18: INVARIANTS                                                   *)
(* ======================================================================== *)
(* All 26 individual + 6 composite invariants by category. INV_ATK_*        *)
(* prevents a specific attack vector documented in Section 15.              *)
(****************************************************************************)

\* ---------- TYPE INVARIANTS ----------

INV_TYPE_SystemState == sys.phase \in SystemPhase /\ sys.batchNonce \in U64
INV_TYPE_Registry == RegistryStateTypeOK(sys.registry)
INV_TYPE_VMState == VMStateTypeOK(sys.vmState)
INV_TYPE_ProgramHash == sys.programHash \in Bytes32
INV_TYPE_All == INV_TYPE_SystemState /\ INV_TYPE_Registry /\ INV_TYPE_VMState /\ INV_TYPE_ProgramHash

\* ---------- BINDING INVARIANTS (CRITICAL) ----------

INV_BIND_StatusFr ==
    sys.phase = PHASE_COMPLETE =>
        sys.publicInputs.status_fr = U64ToFr(FinalExitStatus(sys.continuation.chunks))

INV_BIND_OldRoot ==
    sys.phase = PHASE_COMPLETE =>
        LET fr2 == Bytes32ToFr2(TraceInitialState(sys.continuation.chunks).rw_mem_root_bytes32)
        IN sys.publicInputs.old_root_lo = fr2.lo /\ sys.publicInputs.old_root_hi = fr2.hi

INV_BIND_NewRoot ==
    sys.phase = PHASE_COMPLETE =>
        LET fr2 == Bytes32ToFr2(TraceFinalState(sys.continuation.chunks).rw_mem_root_bytes32)
        IN sys.publicInputs.new_root_lo = fr2.lo /\ sys.publicInputs.new_root_hi = fr2.hi

INV_BIND_ProgramHash ==
    sys.phase = PHASE_COMPLETE =>
        LET fr2 == Bytes32ToFr2(sys.programHash)
        IN sys.publicInputs.program_hash_lo = fr2.lo /\ sys.publicInputs.program_hash_hi = fr2.hi

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

INV_BIND_All == INV_BIND_StatusFr /\ INV_BIND_OldRoot /\ INV_BIND_NewRoot /\ INV_BIND_ProgramHash
                /\ INV_BIND_ConfigTags /\ INV_BIND_StateDigest /\ INV_BIND_Nonce

\* ---------- SAFETY INVARIANTS ----------

INV_SAFE_RegistryReady ==
    sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} => RegistryDeploymentReady(sys.registry)

INV_SAFE_NoTBD == sys.phase # PHASE_INIT => NoTBDInvariant(sys.registry)

INV_SAFE_VMHaltedExitCode ==
    (sys.vmState.halted = 0 => sys.vmState.exit_code = 0) /\
    (sys.vmState.halted = 1 => sys.vmState.exit_code \in 0..255)

INV_SAFE_RegisterX0 == sys.vmState.regs[0] = 0

INV_SAFE_HaltedBinary == sys.vmState.halted \in {0, 1}

INV_SAFE_ContinuationChain ==
    Len(sys.continuation.chunks) > 1 => ContinuityInvariant(sys.continuation.chunks)

INV_SAFE_FinalChunkHalted ==
    sys.phase = PHASE_COMPLETE =>
        sys.continuation.chunks[Len(sys.continuation.chunks)].stateOut.halted = 1

INV_SAFE_All == INV_SAFE_RegistryReady /\ INV_SAFE_NoTBD /\ INV_SAFE_VMHaltedExitCode
                /\ INV_SAFE_RegisterX0 /\ INV_SAFE_HaltedBinary
                /\ INV_SAFE_ContinuationChain /\ INV_SAFE_FinalChunkHalted

\* ---------- ATTACK PREVENTION INVARIANTS (CRITICAL) ----------

\* Prevents accepting incomplete execution (Attack: prove first half, skip balance check)
INV_ATK_NoPrefixProof ==
    sys.phase = PHASE_COMPLETE =>
        LET finalState == TraceFinalState(sys.continuation.chunks)
        IN (sys.publicInputs.status_fr = U64ToFr(JOLT_STATUS_OK) =>
                IsSuccessfulHalt(finalState) /\ finalState.halted = 1) /\
           (IsSuccessfulHalt(finalState) /\ finalState.halted = 1 =>
                sys.publicInputs.status_fr = U64ToFr(JOLT_STATUS_OK))

\* Prevents skipping chunks (Attack: omit chunk with critical logic)
INV_ATK_NoSkipChunk == NoSkippedChunks(sys.continuation.chunks)

\* Prevents splicing different executions (Attack: mix chunks from A and B)
INV_ATK_NoSplice ==
    sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} =>
        ContinuityInvariant(sys.continuation.chunks)

\* Prevents using wrong configuration (Attack: prove with permissive, verify with strict)
INV_ATK_NoCrossConfig ==
    sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} =>
        ConfigConsistentAcrossChunks(sys.continuation.chunks)

\* Prevents forging memory state (Attack: claim false initial/final state)
INV_ATK_NoRootForgery ==
    sys.phase = PHASE_COMPLETE => INV_BIND_OldRoot /\ INV_BIND_NewRoot

\* Prevents forging RW memory between chunks (Attack: manipulate memory root at boundary)
INV_ATK_NoMemoryForgery ==
    sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} =>
        \A i \in 1..(Len(sys.continuation.chunks) - 1) :
            sys.continuation.chunks[i].stateOut.rw_mem_root_bytes32 =
                sys.continuation.chunks[i+1].stateIn.rw_mem_root_bytes32

\* Prevents forging IO memory between chunks (Attack: manipulate I/O root at boundary)
INV_ATK_NoIOForgery ==
    sys.phase \in {PHASE_EXECUTING, PHASE_COMPLETE} =>
        \A i \in 1..(Len(sys.continuation.chunks) - 1) :
            sys.continuation.chunks[i].stateOut.io_root_bytes32 =
                sys.continuation.chunks[i+1].stateIn.io_root_bytes32

\* Prevents replaying old proofs (Attack: reuse proof from different batch)
INV_ATK_NoReplay ==
    sys.phase = PHASE_COMPLETE =>
        sys.publicInputs.batch_nonce_fr =
            U64ToFr(ReadReg(TraceInitialState(sys.continuation.chunks), REG_A4))

INV_ATK_All == INV_ATK_NoPrefixProof /\ INV_ATK_NoSkipChunk /\ INV_ATK_NoSplice
               /\ INV_ATK_NoCrossConfig /\ INV_ATK_NoRootForgery
               /\ INV_ATK_NoMemoryForgery /\ INV_ATK_NoIOForgery /\ INV_ATK_NoReplay

\* ---------- COMPOSITE INVARIANTS ----------

AllInvariants == INV_TYPE_All /\ INV_BIND_All /\ INV_SAFE_All /\ INV_ATK_All

(****************************************************************************)
(* SECTION 19: STATE CONSTRAINT                                             *)
(* ======================================================================== *)
(* Bounds for TLC exploration.                                               *)
(****************************************************************************)

StateConstraint ==
    /\ Len(sys.continuation.chunks) <= MAX_CHUNKS + 1
    /\ sys.vmState.step_counter <= CHUNK_MAX_STEPS * (MAX_CHUNKS + 2)

=============================================================================
