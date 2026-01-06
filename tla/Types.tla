(****************************************************************************)
(* Module: Types.tla                                                        *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE Types ----
(****************************************************************************)
(* Purpose: Foundational types, constants, and status codes for Jolt        *)
(* Appendix J Reference: J.5.9.3 (status codes), J.6 (encodings),           *)
(*                       J.10.5 (VMStateV1 field types)                     *)
(* Version: 1.0                                                             *)
(* Notes: Uses (MAX_CHUNKS + 1) * CHUNK_MAX_STEPS for StepCounter to allow  *)
(*        state constraint pruning without type errors.                     *)
(****************************************************************************)
EXTENDS Integers, FiniteSets

(****************************************************************************)
(* CONSTANTS                                                                 *)
(* Spec-anchors define protocol values; TLC bounds enable model checking    *)
(****************************************************************************)

CONSTANTS
    CHUNK_MAX_STEPS,    \* Max guest instructions per chunk (J.10.6)
    MAX_CHUNKS,         \* TLC bound: max chunks modeled in a single run
    NUM_REGISTERS,      \* Fixed at 32 for RV64IMC (J.5)
    FR_MODULUS,         \* BLS12-381 scalar field modulus (spec anchor)
    FR_TLC_BOUND,       \* Finite subset for TLC enumeration
    U64_TLC_BOUND       \* Finite subset for u64 enumeration

(****************************************************************************)
(* ASSUME: Constrain constants for TLC tractability and protocol compliance *)
(****************************************************************************)

ASSUME CHUNK_MAX_STEPS \in Nat /\ CHUNK_MAX_STEPS > 0
ASSUME MAX_CHUNKS \in Nat /\ MAX_CHUNKS > 0
ASSUME NUM_REGISTERS = 32                           \* Protocol requirement: RV64 has exactly 32 registers
ASSUME FR_MODULUS \in Nat /\ FR_MODULUS > 0         \* Spec anchor (true value ~2^255)
ASSUME FR_TLC_BOUND \in Nat /\ FR_TLC_BOUND > 0 /\ FR_TLC_BOUND <= FR_MODULUS
ASSUME U64_TLC_BOUND \in Nat /\ U64_TLC_BOUND > 0

(****************************************************************************)
(* Basic Type Sets                                                           *)
(****************************************************************************)

\* Single byte (J.6)
Byte == 0..255

\* 32-byte array as function (avoids Seq length issues in TLC)
\* Index 0 is LSB in little-endian interpretation
Bytes32 == [0..31 -> Byte]

\* Field element (BLS12-381 scalar field) - TLC-bounded subset
\* True domain is 0..(FR_MODULUS-1); we use smaller set for checking
Fr == 0..(FR_TLC_BOUND - 1)

\* Byte-valued field element (0..255), constrained to TLC-bounded Fr
\* In the full protocol this is exactly 0..255; for small FR_TLC_BOUND models,
\* this collapses to 0..(FR_TLC_BOUND-1) to keep FrByte \subseteq Fr.
FrByte == 0..(IF FR_TLC_BOUND >= 256 THEN 255 ELSE FR_TLC_BOUND - 1)

\* Pair of field elements for encoding 256-bit values (J.6.5)
\* lo: low 248 bits (31 bytes), hi: high 8 bits (1 byte)
Fr2 == [lo: Fr, hi: FrByte]

\* 64-bit unsigned integer - TLC-bounded subset
\* True domain is 0..2^64-1; we use smaller set for checking
U64 == 0..(U64_TLC_BOUND - 1)

\* Status codes (J.5.9.3)
StatusCode == 0..255

\* Register index (J.5, J.10.5)
RegisterIndex == 0..(NUM_REGISTERS - 1)

\* Halted flag (J.10.5: "0 = running, 1 = terminated")
HaltedFlag == {0, 1}

\* Chunk index for continuation tracking
ChunkIndex == 0..(MAX_CHUNKS - 1)

\* Step counter within execution (bounded for TLC)
\* Allow one extra chunk beyond MAX_CHUNKS to permit state constraint to prune
StepCounter == 0..((MAX_CHUNKS + 1) * CHUNK_MAX_STEPS)

(****************************************************************************)
(* Status Code Constants (J.5.9.3 JOLT_STATUS_CODES_V1)                     *)
(****************************************************************************)

JOLT_STATUS_OK == 0                           \* Successful execution
JOLT_STATUS_TRAP_ILLEGAL_INSTRUCTION == 1     \* Illegal/forbidden instruction
JOLT_STATUS_TRAP_BAD_MEMORY == 2              \* Out-of-range or protected memory access
JOLT_STATUS_TRAP_FORBIDDEN_SYSCALL == 3       \* Disallowed syscall
JOLT_STATUS_TRAP_OOM == 4                     \* OOM or snapshot cap exceeded
JOLT_STATUS_TRAP_INTERNAL == 5                \* Internal VM invariant failure

\* Set of all defined trap codes
TrapCodes == {
    JOLT_STATUS_TRAP_ILLEGAL_INSTRUCTION,
    JOLT_STATUS_TRAP_BAD_MEMORY,
    JOLT_STATUS_TRAP_FORBIDDEN_SYSCALL,
    JOLT_STATUS_TRAP_OOM,
    JOLT_STATUS_TRAP_INTERNAL
}

(****************************************************************************)
(* Status Code Predicates                                                    *)
(****************************************************************************)

\* Returns TRUE iff code indicates a VM trap (J.5.9.3)
IsVmTrap(code) == code \in TrapCodes

\* Returns TRUE iff code indicates successful execution
IsSuccess(code) == code = JOLT_STATUS_OK

\* Returns TRUE iff code is a valid V1 status code
IsValidStatusCode(code) == code \in StatusCode

(****************************************************************************)
(* Helper: Zero-initialized Bytes32                                          *)
(****************************************************************************)

ZeroBytes32 == [i \in 0..31 |-> 0]

(****************************************************************************)
(* Helper: Register file type (32 registers, each a U64)                     *)
(****************************************************************************)

RegisterFile == [RegisterIndex -> U64]

\* Zero-initialized register file
ZeroRegisters == [i \in RegisterIndex |-> 0]

(****************************************************************************)
(* Type Invariant for this module's constants                                *)
(****************************************************************************)

TypesConstantsOK ==
    /\ CHUNK_MAX_STEPS \in Nat \ {0}
    /\ MAX_CHUNKS \in Nat \ {0}
    /\ NUM_REGISTERS = 32
    /\ FR_MODULUS \in Nat \ {0}
    /\ FR_TLC_BOUND \in Nat \ {0}
    /\ FR_TLC_BOUND <= FR_MODULUS
    /\ U64_TLC_BOUND \in Nat \ {0}

====
