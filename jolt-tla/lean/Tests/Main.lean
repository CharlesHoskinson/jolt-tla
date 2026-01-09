import Jolt.Oracle
import Jolt.Poseidon.Constants
import Tests.JSONParserTests
import Tests.CLITerminalTests
import Tests.REPLTests

/-!
# Jolt Oracle Tests

Test suite for the Jolt Oracle.
-/

open Jolt
open Jolt.Poseidon.Constants

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
  let ba := ByteArray.mk (List.replicate 32 0x42).toArray
  match Bytes32.ofByteArray ba with
  | .ok b32 =>
    if b32.data.size != 32 then
      IO.println "FAIL: Bytes32.ofByteArray size"
      return false
  | .error _ =>
    IO.println "FAIL: Bytes32.ofByteArray should succeed"
    return false

  -- Test wrong length rejection
  let badBa := ByteArray.mk (List.replicate 16 0x42).toArray
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

/-- Test transcript tag validation per §8.6. -/
def testTranscriptTags : IO Bool := do
  -- Valid tags (per §8.6: ASCII, [A-Z0-9/_], starts with JOLT/, length ≥ 5)
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

  -- NOTE: Per §8.6, version suffix is NOT required for transcript tags!
  -- (Version suffix is only required for registry keys per §3.3)
  match Transcript.validateTag "JOLT/STATE" with
  | .ok _ => pure ()  -- This IS valid per §8.6
  | .error _ =>
    IO.println "FAIL: JOLT/STATE should be valid (§8.6 does not require version)"
    return false

  -- Invalid tags
  match Transcript.validateTag "STATE/V1" with
  | .ok _ =>
    IO.println "FAIL: STATE/V1 should be invalid (no JOLT/ prefix)"
    return false
  | .error _ => pure ()

  match Transcript.validateTag "JOLT/bad" with
  | .ok _ =>
    IO.println "FAIL: JOLT/bad should be invalid (lowercase letters)"
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

/-- Test Poseidon MDS matrix constants per §3.4.1. -/
def testPoseidonMDS : IO Bool := do
  -- Test MDS matrix dimensions
  if mdsMatrix.size != 3 then
    IO.println s!"FAIL: MDS matrix should have 3 rows, got {mdsMatrix.size}"
    return false

  for i in [:3] do
    if mdsMatrix[i]!.size != 3 then
      IO.println s!"FAIL: MDS row {i} should have 3 columns"
      return false

  -- Test MDS matrix values match expected hex (roundtrip test)
  if !validateMdsMatrix then
    IO.println "FAIL: MDS matrix values don't match expected hex"
    return false

  -- Test specific values (spot check)
  let m00 := Fr.toHex64LE (mdsMatrix[0]![0]!)
  if m00 != MDS_0_0_HEX then
    IO.println s!"FAIL: M[0][0] mismatch: expected {MDS_0_0_HEX}, got {m00}"
    return false

  IO.println "PASS: Poseidon MDS matrix"
  return true

/-- Test Poseidon round constants structure. -/
def testPoseidonRoundConstants : IO Bool := do
  -- Test round constants dimensions (68 rounds × 3 = 204)
  let expected := Poseidon.POSEIDON_TOTAL_ROUNDS * Poseidon.POSEIDON_WIDTH
  if roundConstants.size != expected then
    IO.println s!"FAIL: Round constants should have {expected} elements, got {roundConstants.size}"
    return false

  -- Check if constants are still placeholder (warning, not failure)
  if roundConstantsArePlaceholder then
    IO.println "WARN: Round constants are placeholder (all zeros) - must extract from midnight-circuits v6.0.0"

  IO.println "PASS: Poseidon round constants structure"
  return true

/-- Test Poseidon config validation. -/
def testPoseidonConfig : IO Bool := do
  -- Test that config has correct dimensions
  if !validateConstants then
    IO.println "FAIL: Poseidon constants have incorrect dimensions"
    return false

  -- Test config matches JOLT_POSEIDON_FR_V1 parameters
  let cfg := joltPoseidonConfig
  if cfg.width != 3 then
    IO.println s!"FAIL: Config width should be 3, got {cfg.width}"
    return false
  if cfg.fullRounds != 8 then
    IO.println s!"FAIL: Config fullRounds should be 8, got {cfg.fullRounds}"
    return false
  if cfg.partialRounds != 60 then
    IO.println s!"FAIL: Config partialRounds should be 60, got {cfg.partialRounds}"
    return false
  if cfg.sboxExponent != 5 then
    IO.println s!"FAIL: Config sboxExponent should be 5, got {cfg.sboxExponent}"
    return false

  IO.println "PASS: Poseidon config"
  return true

/-- Test Fr hex encoding/decoding roundtrip. -/
def testFrHexRoundtrip : IO Bool := do
  -- Test roundtrip with known value
  let original := Fr.ofNat 12345678901234567890
  let hex := Fr.toHex64LE original
  match Fr.fromHex64LE hex with
  | .ok decoded =>
    if decoded != original then
      IO.println s!"FAIL: Fr hex roundtrip mismatch"
      return false
  | .error e =>
    IO.println s!"FAIL: Fr hex decode error: {repr e}"
    return false

  -- Test with MDS constant
  match Fr.fromHex64LE MDS_0_0_HEX with
  | .ok fr =>
    let rehex := Fr.toHex64LE fr
    if rehex != MDS_0_0_HEX then
      IO.println s!"FAIL: MDS constant roundtrip mismatch"
      return false
  | .error e =>
    IO.println s!"FAIL: MDS constant parse error: {repr e}"
    return false

  IO.println "PASS: Fr hex roundtrip"
  return true

/-- Run all tests. -/
def runTests : IO UInt32 := do
  IO.println "Running Jolt Oracle tests..."
  IO.println ""

  let mut passed := 0
  let mut failed := 0

  IO.println "=== Core Module Tests ==="
  IO.println ""
  if ← testFrArithmetic then passed := passed + 1 else failed := failed + 1
  if ← testBytes32 then passed := passed + 1 else failed := failed + 1
  if ← testFr2 then passed := passed + 1 else failed := failed + 1
  if ← testASCII then passed := passed + 1 else failed := failed + 1
  if ← testRegistryKeys then passed := passed + 1 else failed := failed + 1
  if ← testTranscriptTags then passed := passed + 1 else failed := failed + 1
  if ← testVMState then passed := passed + 1 else failed := failed + 1

  IO.println ""
  IO.println "=== Poseidon Constants Tests ==="
  IO.println ""
  if ← testFrHexRoundtrip then passed := passed + 1 else failed := failed + 1
  if ← testPoseidonMDS then passed := passed + 1 else failed := failed + 1
  if ← testPoseidonRoundConstants then passed := passed + 1 else failed := failed + 1
  if ← testPoseidonConfig then passed := passed + 1 else failed := failed + 1

  IO.println ""

  -- JSON Parser tests
  let (jsonPassed, jsonFailed) ← Jolt.Tests.JSON.runJSONTests
  passed := passed + jsonPassed
  failed := failed + jsonFailed

  -- CLI Terminal tests
  let (cliPassed, cliFailed) ← CLI.Tests.Terminal.runAllCLITerminalTests
  passed := passed + cliPassed
  failed := failed + cliFailed

  -- REPL Feature tests
  let (replPassed, replFailed) ← Tests.REPL.runAllREPLTests
  passed := passed + replPassed
  failed := failed + replFailed

  IO.println ""
  IO.println "==========================================="
  IO.println s!"Total Results: {passed} passed, {failed} failed"

  return if failed > 0 then 1 else 0

/-- Main entry point. -/
def main : IO UInt32 := runTests
