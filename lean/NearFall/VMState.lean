import NearFall.TLATypes
import NearFall.SMT

/-!
# VM State Modeling

RISC-V VM state machine for deterministic guest execution, matching jolt-tla.

## Main Definitions

* `RegisterFile` - 32 RISC-V registers (x0-x31)
* `ConfigTag` - Configuration name/value pair
* `VMStateV1` - Full VM state with 8 fields
* VM predicates (IsRunning, IsHalted, etc.)

## References

* jolt-tla/tla/VMState.tla
* Jolt Spec §5 (Guest VM), §10.5 (VMStateV1)
-/

namespace NearFall.VMState

open TLATypes SMT

/-! ### Register Constants -/

/-- Number of RISC-V registers. -/
def NUM_REGISTERS : Nat := 32

/-- Register index type (0..31). -/
abbrev RegisterIndex := Fin 32

/-- ABI register indices (J.5.8). -/
def REG_A0 : RegisterIndex := ⟨10, by decide⟩  -- Input pointer
def REG_A1 : RegisterIndex := ⟨11, by decide⟩  -- Input length
def REG_A2 : RegisterIndex := ⟨12, by decide⟩  -- Output pointer
def REG_A3 : RegisterIndex := ⟨13, by decide⟩  -- Output max
def REG_A4 : RegisterIndex := ⟨14, by decide⟩  -- Batch nonce
def REG_SP : RegisterIndex := ⟨2, by decide⟩   -- Stack pointer
def REG_X0 : RegisterIndex := ⟨0, by decide⟩   -- Hardwired zero

/-! ### Register File -/

/-- Register file: 32 u64 registers.

**TLA+ equivalent**: `RegisterFile == [RegisterIndex -> U64]` -/
structure RegisterFile where
  /-- Register values (x0-x31). -/
  regs : Array U64
  /-- Proof that array has exactly 32 elements. -/
  h_len : regs.size = 32
  deriving DecidableEq

namespace RegisterFile

/-- Create a 32-element zero array. -/
private def zeroArray : Array U64 :=
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

/-- Create register file with all zeros. -/
def zeros : RegisterFile := ⟨zeroArray, rfl⟩

/-- Read register (x0 always returns 0). -/
def read (rf : RegisterFile) (idx : RegisterIndex) : U64 :=
  if idx.val = 0 then 0
  else rf.regs[idx.val]'(by have := rf.h_len; omega)

/-- Write register (x0 writes are ignored).

Security fix: was a no-op, now properly updates array.
Attack prevented: Nonce/ABI register binding bypass via ignored writes. -/
def write (rf : RegisterFile) (idx : RegisterIndex) (value : U64) : RegisterFile :=
  if idx.val = 0 then rf  -- x0 writes are ignored per RISC-V spec
  else
    have h : idx.val < rf.regs.size := by have := rf.h_len; omega
    let newRegs := rf.regs.set idx.val value
    ⟨newRegs, by simp [newRegs, rf.h_len]⟩

/-- Create initial register file with ABI registers set. -/
def init (inputPtr inputLen outputPtr outputMax batchNonce stackPtr : U64) : RegisterFile :=
  zeros
    |> (·.write REG_A0 inputPtr)
    |> (·.write REG_A1 inputLen)
    |> (·.write REG_A2 outputPtr)
    |> (·.write REG_A3 outputMax)
    |> (·.write REG_A4 batchNonce)
    |> (·.write REG_SP stackPtr)

end RegisterFile

instance : Inhabited RegisterFile where
  default := RegisterFile.zeros

instance : BEq RegisterFile where
  beq a b := a.regs == b.regs

/-! ### Configuration Tags -/

/-- Configuration tag entry: (name, value) pair.

Per J.2.8, tags are serialized as bytes. We model them as strings for simplicity.

**TLA+ equivalent**: `ConfigTag == [name: STRING, value: STRING]` -/
structure ConfigTag where
  /-- Tag name. -/
  name : String
  /-- Tag value. -/
  value : String
  deriving Repr, DecidableEq, BEq, Inhabited

/-! ### VMStateV1 (J.10.5) -/

/-- Full VM state record matching TLA+ VMStateV1 exactly.

8 fields as specified in J.10.5:
1. regs - 32 u64 registers
2. pc - program counter
3. step_counter - total instructions executed
4. rw_mem_root_bytes32 - RW memory SMT root
5. io_root_bytes32 - I/O memory SMT root
6. halted - 0 = running, 1 = terminated
7. exit_code - exit status (valid when halted=1)
8. config_tags - registry projection

**TLA+ equivalent**: VMStateV1 record -/
structure VMStateV1 where
  /-- 32 u64 registers (x0-x31). -/
  regs : RegisterFile
  /-- Program counter. -/
  pc : U64
  /-- Total instructions executed. -/
  step_counter : StepCounter
  /-- RW memory SMT root. -/
  rw_mem_root_bytes32 : Bytes32
  /-- I/O memory SMT root. -/
  io_root_bytes32 : Bytes32
  /-- Halted flag (0 = running, 1 = terminated). -/
  halted : HaltedFlag
  /-- Exit status code (valid when halted=1). -/
  exit_code : StatusCode
  /-- Configuration tags. -/
  config_tags : List ConfigTag
  deriving DecidableEq

namespace VMStateV1

/-- Create initial VM state.

Per J.5.8, sets up ABI registers and initial memory roots. -/
def init (entryPoint : U64)
         (inputPtr inputLen outputPtr outputMax batchNonce stackPtr : U64)
         (initialRWRoot initialIORoot : Bytes32)
         (configTags : List ConfigTag) : VMStateV1 := {
  regs := RegisterFile.init inputPtr inputLen outputPtr outputMax batchNonce stackPtr
  pc := entryPoint
  step_counter := 0
  rw_mem_root_bytes32 := initialRWRoot
  io_root_bytes32 := initialIORoot
  halted := .running
  exit_code := JOLT_STATUS_OK
  config_tags := configTags
}

/-! ### VM State Predicates -/

/-- Is the VM still running? -/
def isRunning (state : VMStateV1) : Bool :=
  state.halted == .running

/-- Has the VM halted? -/
def isHalted (state : VMStateV1) : Bool :=
  state.halted == .halted

/-- Did the VM halt successfully? -/
def isSuccessfulHalt (state : VMStateV1) : Bool :=
  state.isHalted && state.exit_code == JOLT_STATUS_OK

/-- Did the VM trap? -/
def isTrappedHalt (state : VMStateV1) : Bool :=
  state.isHalted && isVmTrap state.exit_code

/-- Get exit code as status code (only valid when halted). -/
def getExitStatus (state : VMStateV1) : StatusCode :=
  if state.isHalted then state.exit_code else 0

/-! ### Register Access -/

/-- Read register. -/
def readReg (state : VMStateV1) (idx : RegisterIndex) : U64 :=
  state.regs.read idx

/-- Write register. -/
def writeReg (state : VMStateV1) (idx : RegisterIndex) (value : U64) : VMStateV1 :=
  { state with regs := state.regs.write idx value }

/-! ### Halt Transitions (J.5.9) -/

/-- Normal exit via syscall (J.5.8.3).

exit_code comes from low 8 bits of a0. -/
def normalExit (state : VMStateV1) (exitCodeFromA0 : U64) : VMStateV1 :=
  { state with
    halted := .halted
    exit_code := (exitCodeFromA0 % 256).toUInt8
  }

/-- Trap with specific status code. -/
def trapWith (state : VMStateV1) (trapCode : StatusCode) : VMStateV1 :=
  { state with
    halted := .halted
    exit_code := trapCode
  }

/-- Trap: Illegal instruction. -/
def trapIllegalInstruction (state : VMStateV1) : VMStateV1 :=
  state.trapWith JOLT_STATUS_TRAP_ILLEGAL_INSTRUCTION

/-- Trap: Bad memory access. -/
def trapBadMemory (state : VMStateV1) : VMStateV1 :=
  state.trapWith JOLT_STATUS_TRAP_BAD_MEMORY

/-- Trap: Forbidden syscall. -/
def trapForbiddenSyscall (state : VMStateV1) : VMStateV1 :=
  state.trapWith JOLT_STATUS_TRAP_FORBIDDEN_SYSCALL

/-- Trap: Out of memory. -/
def trapOOM (state : VMStateV1) : VMStateV1 :=
  state.trapWith JOLT_STATUS_TRAP_OOM

/-- Trap: Internal error. -/
def trapInternal (state : VMStateV1) : VMStateV1 :=
  state.trapWith JOLT_STATUS_TRAP_INTERNAL

/-! ### Step Counter Management -/

/-- Increment step counter by 1 (J.5.5). -/
def incrementStepCounter (state : VMStateV1) : VMStateV1 :=
  { state with step_counter := state.step_counter + 1 }

/-- Get current chunk index. -/
def currentChunkIndex (state : VMStateV1) (chunkMaxSteps : Nat) : ChunkIndex :=
  state.step_counter / chunkMaxSteps

/-! ### Memory Root Updates -/

/-- Update RW memory root after memory write. -/
def updateRWRoot (state : VMStateV1) (newRootBytes32 : Bytes32) : VMStateV1 :=
  { state with rw_mem_root_bytes32 := newRootBytes32 }

/-- Update IO memory root after I/O write. -/
def updateIORoot (state : VMStateV1) (newRootBytes32 : Bytes32) : VMStateV1 :=
  { state with io_root_bytes32 := newRootBytes32 }

/-- Update both memory roots. -/
def updateMemoryRoots (state : VMStateV1) (newRWRoot newIORoot : Bytes32) : VMStateV1 :=
  { state with
    rw_mem_root_bytes32 := newRWRoot
    io_root_bytes32 := newIORoot
  }

/-! ### State Comparison -/

/-- Check if two states have equal core fields (excluding step_counter).
Security fix: added config_tags. -/
def coreStateEqual (s1 s2 : VMStateV1) : Bool :=
  s1.regs == s2.regs &&
  s1.pc == s2.pc &&
  s1.rw_mem_root_bytes32 == s2.rw_mem_root_bytes32 &&
  s1.io_root_bytes32 == s2.io_root_bytes32 &&
  s1.halted == s2.halted &&
  s1.exit_code == s2.exit_code &&
  s1.config_tags == s2.config_tags

end VMStateV1

instance : Inhabited VMStateV1 where
  default := {
    regs := RegisterFile.zeros
    pc := 0
    step_counter := 0
    rw_mem_root_bytes32 := Bytes32.zero
    io_root_bytes32 := Bytes32.zero
    halted := .running
    exit_code := JOLT_STATUS_OK
    config_tags := []
  }

/-- Security fix: added config_tags to BEq.
Attack prevented: Cross-config state splicing where config_tags differ but == returns true. -/
instance : BEq VMStateV1 where
  beq a b :=
    a.regs == b.regs &&
    a.pc == b.pc &&
    a.step_counter == b.step_counter &&
    a.rw_mem_root_bytes32 == b.rw_mem_root_bytes32 &&
    a.io_root_bytes32 == b.io_root_bytes32 &&
    a.halted == b.halted &&
    a.exit_code == b.exit_code &&
    a.config_tags == b.config_tags  -- Security fix: was missing

/-! ### Type Invariants -/

/-- Register file type invariant (always true by construction). -/
def registerFileTypeOK (rf : RegisterFile) : Prop :=
  rf.regs.size = 32

/-- VMState type invariant. -/
def vmStateTypeOK (state : VMStateV1) : Prop :=
  registerFileTypeOK state.regs ∧
  bytes32_well_formed state.rw_mem_root_bytes32 ∧
  bytes32_well_formed state.io_root_bytes32

/-! ### Safety Invariants (J.10.5 Constraints) -/

/-- Constraint 1: halted is binary. -/
def haltedFlagValid (state : VMStateV1) : Prop :=
  state.halted = .running ∨ state.halted = .halted

/-- Constraint 2: If halted = 0, then exit_code = 0. -/
def runningExitCodeZero (state : VMStateV1) : Prop :=
  state.halted = .running → state.exit_code = JOLT_STATUS_OK

/-- Constraint 3: If halted = 1, then exit_code in [0, 255]. -/
def haltedExitCodeValid (state : VMStateV1) : Prop :=
  state.halted = .halted → state.exit_code.toNat ≤ 255

/-- Register x0 is always zero (RISC-V spec). -/
def registerX0Zero (state : VMStateV1) : Prop :=
  state.regs.read REG_X0 = 0

/-- Combined VMState safety invariant. -/
def vmStateSafetyInvariant (state : VMStateV1) : Prop :=
  haltedFlagValid state ∧
  runningExitCodeZero state ∧
  haltedExitCodeValid state ∧
  registerX0Zero state

/-- Full VMState invariant (type + safety). -/
def vmStateInvariant (state : VMStateV1) : Prop :=
  vmStateTypeOK state ∧ vmStateSafetyInvariant state

/-! ### Theorems -/

/-- Register x0 is always zero after reading. -/
theorem read_x0_zero (rf : RegisterFile) : rf.read REG_X0 = 0 := by
  simp [RegisterFile.read, REG_X0]

/-- Halted flag is always valid (by construction). -/
theorem halted_flag_always_valid (state : VMStateV1) : haltedFlagValid state := by
  unfold haltedFlagValid
  cases state.halted <;> simp

/-- Initial state has running = true. -/
theorem init_is_running
    (ep ip il op om bn sp : U64)
    (rw io : Bytes32) (tags : List ConfigTag) :
    (VMStateV1.init ep ip il op om bn sp rw io tags).isRunning = true := by
  simp only [VMStateV1.init, VMStateV1.isRunning]
  rfl

/-- Halting is reflected in isHalted. -/
theorem trap_is_halted (state : VMStateV1) (code : StatusCode) :
    (state.trapWith code).isHalted = true := by
  simp only [VMStateV1.trapWith, VMStateV1.isHalted]
  rfl

end NearFall.VMState
