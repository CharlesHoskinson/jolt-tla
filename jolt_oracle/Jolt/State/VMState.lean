import Jolt.Errors
import Jolt.Field.Fr
import Jolt.Encoding.Bytes32
import Jolt.Util.ByteOrder

namespace Jolt.State

/-- Compare ByteArrays for equality. -/
private def byteArrayEq (a b : ByteArray) : Bool :=
  a.data == b.data

/-- A config tag entry (name bytes, value bytes). -/
structure ConfigTag where
  name : ByteArray
  value : ByteArray
  deriving Inhabited

namespace ConfigTag

instance : Repr ConfigTag where
  reprPrec t _ := s!"ConfigTag({t.name.size} bytes, {t.value.size} bytes)"

/-- Get name for sorting. -/
def nameBytes (t : ConfigTag) : ByteArray := t.name

instance : DecidableEq ConfigTag := fun a b =>
  if h : a.name.data = b.name.data ∧ a.value.data = b.value.data then
    isTrue (by
      cases a with | mk an av =>
      cases b with | mk bn bv =>
      simp only at h
      obtain ⟨hn, hv⟩ := h
      congr
      · cases an; cases bn; simp_all
      · cases av; cases bv; simp_all)
  else
    isFalse (by intro heq; cases heq; simp_all)

end ConfigTag

/-- RISC-V VM state (version 1).

Contains all state needed for state digest computation. -/
structure VMStateV1 where
  /-- Program counter -/
  pc : UInt64
  /-- 32 general-purpose registers -/
  regs : Array UInt64
  /-- Step counter -/
  stepCounter : UInt64
  /-- Read-write memory Merkle root -/
  rwMemRoot : Bytes32
  /-- I/O Merkle root -/
  ioRoot : Bytes32
  /-- Halted flag (0 = running, 1 = halted) -/
  halted : UInt64
  /-- Exit code (valid only when halted) -/
  exitCode : UInt64
  /-- Config tags (prover's claim, must match registry projection) -/
  configTags : Array ConfigTag

namespace VMStateV1

instance : Inhabited VMStateV1 := ⟨{
  pc := 0
  regs := Array.replicate 32 0
  stepCounter := 0
  rwMemRoot := Bytes32.zero
  ioRoot := Bytes32.zero
  halted := 0
  exitCode := 0
  configTags := #[]
}⟩

instance : Repr VMStateV1 where
  reprPrec s _ := s!"VMStateV1(pc={s.pc}, halted={s.halted}, exitCode={s.exitCode})"

/-- Validate that regs array has exactly 32 elements. -/
def hasValidRegCount (s : VMStateV1) : Bool := s.regs.size == 32

/-- Validate RegisterX0Zero invariant: regs[0] must be 0. -/
def validateRegisterX0 (s : VMStateV1) : OracleResult Unit := do
  if s.regs.size == 0 then
    throw (ErrorCode.E104_WrongLength 32 0)
  if s.regs[0]! != 0 then
    throw (ErrorCode.E407_RegisterX0NonZero s.regs[0]!)

/-- Validate halted flag is 0 or 1. -/
def validateHalted (s : VMStateV1) : OracleResult Unit := do
  if s.halted != 0 && s.halted != 1 then
    throw ErrorCode.E404_InvalidHalted

/-- Validate termination invariants.

- halted = 0 → exit_code = 0
- halted = 1 → exit_code ≤ 255 -/
def validateTermination (s : VMStateV1) : OracleResult Unit := do
  if s.halted == 0 then
    if s.exitCode != 0 then
      throw (ErrorCode.E405_TerminationInvariant "running state must have exit_code=0")
  else -- halted == 1
    if s.exitCode > 255 then
      throw (ErrorCode.E405_TerminationInvariant "exit_code must be ≤ 255")

/-- Validate config_tags are sorted by name bytes. -/
def validateConfigTagsOrder (s : VMStateV1) : OracleResult Unit := do
  if !isSortedByBytes ConfigTag.nameBytes s.configTags then
    throw (ErrorCode.E401_OrderingViolation "config_tags must be sorted by name bytes")

/-- Full validation of VM state. -/
def validate (s : VMStateV1) : OracleResult Unit := do
  if s.regs.size != 32 then
    throw (ErrorCode.E104_WrongLength 32 s.regs.size)
  validateRegisterX0 s
  validateHalted s
  validateTermination s
  validateConfigTagsOrder s

/-- Create initial state (all zeros except regs array size). -/
def initial : VMStateV1 where
  pc := 0
  regs := Array.replicate 32 0
  stepCounter := 0
  rwMemRoot := Bytes32.zero
  ioRoot := Bytes32.zero
  halted := 0
  exitCode := 0
  configTags := #[]

end VMStateV1

end Jolt.State
