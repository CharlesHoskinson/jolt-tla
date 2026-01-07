import Jolt.Oracle

/-!
# Jolt Oracle Tests

Test suite for the Jolt Oracle.
-/

open Jolt

/-- Test Fr arithmetic. -/
def testFrArithmetic : IO Bool := do
  -- Test basic operations
  let a := Fr.ofNat 5
  let b := Fr.ofNat 3
  let sum := a + b
  if sum.val != 8 then
    IO.println "FAIL: Fr addition"
    return false

  let prod := a * b
  if prod.val != 15 then
    IO.println "FAIL: Fr multiplication"
    return false

  let neg := -a
  if neg.val != Fr.modulus - 5 then
    IO.println "FAIL: Fr negation"
    return false

  IO.println "PASS: Fr arithmetic"
  return true

/-- Test Bytes32 construction. -/
def testBytes32 : IO Bool := do
  -- Test zero
  let z := Bytes32.zero
  if z.data.size != 32 then
    IO.println "FAIL: Bytes32.zero size"
    return false

  -- Test ofByteArray
  let ba := ByteArray.mk (Array.replicate 32 0x42)
  match Bytes32.ofByteArray ba with
  | .ok b32 =>
    if b32.data.size != 32 then
      IO.println "FAIL: Bytes32.ofByteArray size"
      return false
  | .error _ =>
    IO.println "FAIL: Bytes32.ofByteArray should succeed"
    return false

  -- Test wrong length rejection
  let badBa := ByteArray.mk (Array.replicate 16 0x42)
  match Bytes32.ofByteArray badBa with
  | .ok _ =>
    IO.println "FAIL: Bytes32.ofByteArray should reject wrong length"
    return false
  | .error _ =>
    pure ()  -- Expected

  IO.println "PASS: Bytes32"
  return true

/-- Compare ByteArrays for equality. -/
private def byteArrayEq (a b : ByteArray) : Bool :=
  a.data == b.data

/-- Test Fr2 encoding. -/
def testFr2 : IO Bool := do
  -- Test roundtrip
  let b32 := Bytes32.zero
  let fr2 := bytes32ToFr2 b32
  match fr2ToBytes32 fr2 with
  | .ok b32' =>
    if !byteArrayEq b32.data b32'.data then
      IO.println "FAIL: Fr2 roundtrip"
      return false
  | .error _ =>
    IO.println "FAIL: Fr2 decode should succeed for valid input"
    return false

  IO.println "PASS: Fr2"
  return true

/-- Test ASCII utilities. -/
def testASCII : IO Bool := do
  -- Test isUpperASCII
  if !ASCII.isUpperASCII 'A' then
    IO.println "FAIL: isUpperASCII 'A'"
    return false
  if ASCII.isUpperASCII 'a' then
    IO.println "FAIL: isUpperASCII 'a' should be false"
    return false

  -- Test isDigitASCII
  if !ASCII.isDigitASCII '5' then
    IO.println "FAIL: isDigitASCII '5'"
    return false

  -- Test isASCII
  if !ASCII.isASCII "HELLO" then
    IO.println "FAIL: isASCII 'HELLO'"
    return false

  IO.println "PASS: ASCII"
  return true

/-- Test registry key validation. -/
def testRegistryKeys : IO Bool := do
  -- Valid keys
  if !Registry.isValidKeyFormat "JOLT_FOO_V1" then
    IO.println "FAIL: JOLT_FOO_V1 should be valid"
    return false
  if !Registry.isValidKeyFormat "JOLT_WRAPPER_VK_HASH_V1" then
    IO.println "FAIL: JOLT_WRAPPER_VK_HASH_V1 should be valid"
    return false
  if !Registry.isValidKeyFormat "JOLT_A_V123" then
    IO.println "FAIL: JOLT_A_V123 should be valid"
    return false

  -- Invalid keys
  if Registry.isValidKeyFormat "JOLT_V1" then
    IO.println "FAIL: JOLT_V1 should be invalid (no middle part)"
    return false
  if Registry.isValidKeyFormat "JOLT_FOO" then
    IO.println "FAIL: JOLT_FOO should be invalid (no version)"
    return false
  if Registry.isValidKeyFormat "FOO_BAR_V1" then
    IO.println "FAIL: FOO_BAR_V1 should be invalid (no JOLT_ prefix)"
    return false

  IO.println "PASS: Registry keys"
  return true

/-- Test transcript tag validation. -/
def testTranscriptTags : IO Bool := do
  -- Valid tags
  match Transcript.validateTag "JOLT/STATE/V1" with
  | .ok _ => pure ()
  | .error _ =>
    IO.println "FAIL: JOLT/STATE/V1 should be valid"
    return false

  match Transcript.validateTag "JOLT/CONFIG_TAGS/V1" with
  | .ok _ => pure ()
  | .error _ =>
    IO.println "FAIL: JOLT/CONFIG_TAGS/V1 should be valid"
    return false

  -- Invalid tags
  match Transcript.validateTag "STATE/V1" with
  | .ok _ =>
    IO.println "FAIL: STATE/V1 should be invalid (no JOLT/ prefix)"
    return false
  | .error _ => pure ()

  match Transcript.validateTag "JOLT/STATE" with
  | .ok _ =>
    IO.println "FAIL: JOLT/STATE should be invalid (no version)"
    return false
  | .error _ => pure ()

  IO.println "PASS: Transcript tags"
  return true

/-- Test VM state validation. -/
def testVMState : IO Bool := do
  -- Valid initial state
  let initial := State.VMStateV1.initial
  match initial.validate with
  | .ok _ => pure ()
  | .error _ =>
    IO.println "FAIL: Initial state should be valid"
    return false

  -- Invalid: regs[0] != 0
  let badRegs := { initial with regs := initial.regs.set! 0 42 }
  match badRegs.validate with
  | .ok _ =>
    IO.println "FAIL: State with regs[0] != 0 should be invalid"
    return false
  | .error _ => pure ()

  -- Invalid: halted = 2
  let badHalted := { initial with halted := 2 }
  match badHalted.validate with
  | .ok _ =>
    IO.println "FAIL: State with halted = 2 should be invalid"
    return false
  | .error _ => pure ()

  IO.println "PASS: VM state"
  return true

/-- Run all tests. -/
def runTests : IO UInt32 := do
  IO.println "Running Jolt Oracle tests..."
  IO.println ""

  let mut passed := 0
  let mut failed := 0

  if ← testFrArithmetic then passed := passed + 1 else failed := failed + 1
  if ← testBytes32 then passed := passed + 1 else failed := failed + 1
  if ← testFr2 then passed := passed + 1 else failed := failed + 1
  if ← testASCII then passed := passed + 1 else failed := failed + 1
  if ← testRegistryKeys then passed := passed + 1 else failed := failed + 1
  if ← testTranscriptTags then passed := passed + 1 else failed := failed + 1
  if ← testVMState then passed := passed + 1 else failed := failed + 1

  IO.println ""
  IO.println s!"Results: {passed} passed, {failed} failed"

  return if failed > 0 then 1 else 0

/-- Main entry point. -/
def main : IO UInt32 := runTests
