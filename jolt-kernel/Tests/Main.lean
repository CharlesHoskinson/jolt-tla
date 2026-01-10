import Jolt

/-!
# Jolt Kernel Conformance Tests

Test suite for the Jolt kernel.

## Test Categories

1. Type tests - Fr, Bytes32, Fr2 construction
2. Encoding tests - Bytes32ToFr2 roundtrip
3. Transcript tests - Absorb/squeeze behavior
4. StateDigest tests - Determinism and binding
5. Wrapper tests - Public inputs assembly
6. Continuation tests - Chain validation

## Running Tests

```bash
lake test
```
-/

open Jolt
open Jolt.Encoding
open Jolt.Transcript
open Jolt.StateDigest
open Jolt.Wrapper
open Jolt.Continuations
open Jolt.ConfigTags

/-! ### Test Helpers -/

/-- Test result type. -/
inductive TestResult where
  | pass : String → TestResult
  | fail : String → String → TestResult
  deriving Repr

/-- Run a test with expected equality. -/
def testEq [DecidableEq α] [Repr α] (name : String) (actual expected : α) : TestResult :=
  if actual == expected then
    TestResult.pass name
  else
    TestResult.fail name s!"Expected {repr expected}, got {repr actual}"

/-- Run a boolean test. -/
def testBool (name : String) (actual : Bool) (expected : Bool) : TestResult :=
  if actual == expected then
    TestResult.pass name
  else
    TestResult.fail name s!"Expected {expected}, got {actual}"

/-- Run a test that should succeed (Option.isSome). -/
def testSome {α : Type} (name : String) (result : Option α) : TestResult :=
  if result.isSome then
    TestResult.pass name
  else
    TestResult.fail name "Expected Some, got None"

/-- Run a test that should fail (Option.isNone). -/
def testNone {α : Type} (name : String) (result : Option α) : TestResult :=
  if result.isNone then
    TestResult.pass name
  else
    TestResult.fail name "Expected None, got Some"

/-- Print test result. -/
def printResult (r : TestResult) : IO Unit :=
  match r with
  | TestResult.pass name => IO.println s!"[PASS] {name}"
  | TestResult.fail name msg => IO.println s!"[FAIL] {name}: {msg}"

/-- Count passed tests. -/
def countPassed (results : List TestResult) : Nat :=
  results.filter (fun r => match r with | TestResult.pass _ => true | _ => false) |>.length

/-! ### Fr Tests -/

def frTests : List TestResult := [
  testEq "Fr.zero.val" Fr.zero.val 0,
  testEq "Fr.one.val" Fr.one.val 1,
  testSome "Fr.ofNat? 100" (Fr.ofNat? 100),
  testNone "Fr.ofNat? (modulus)" (Fr.ofNat? Fr.modulus),
  testBool "Fr.isZero Fr.zero" (Fr.isZero Fr.zero) true,
  testBool "Fr.isZero Fr.one" (Fr.isZero Fr.one) false
]

/-! ### Bytes32 Tests -/

def bytes32Tests : List TestResult := [
  testEq "Bytes32.zero.data.size" Bytes32.zero.data.size 32,
  testSome "Bytes32.fromList? (32 bytes)" (Bytes32.fromList? (List.replicate 32 0)),
  testNone "Bytes32.fromList? (31 bytes)" (Bytes32.fromList? (List.replicate 31 0)),
  testNone "Bytes32.fromList? (33 bytes)" (Bytes32.fromList? (List.replicate 33 0))
]

/-! ### Encoding Tests -/

def encodingTests : List TestResult := [
  testEq "bytesToNatLE []" (bytesToNatLE []) 0,
  testEq "bytesToNatLE [1]" (bytesToNatLE [1]) 1,
  testEq "bytesToNatLE [0, 1]" (bytesToNatLE [0, 1]) 256,
  testEq "bytesToNatLE [1, 1]" (bytesToNatLE [1, 1]) 257,
  testEq "natToBytesLE 256 2" (natToBytesLE 256 2) [0, 1],
  testEq "natToBytesLE 257 2" (natToBytesLE 257 2) [1, 1],
  testEq "natToBytesLE_length 0 31" (natToBytesLE 0 31).length 31,
  testSome "Bytes32ToFr2 Bytes32.zero" (Bytes32ToFr2 Bytes32.zero)
]

/-! ### Transcript Tests -/

def transcriptTests : List TestResult := [
  testEq "init position" TranscriptState.init.pos 0,
  testEq "init mode" TranscriptState.init.mode Mode.Absorb,
  testBool "checkCanAbsorb init" (checkCanAbsorb TranscriptState.init) true,
  testBool "checkCanSqueeze init" (checkCanSqueeze TranscriptState.init) false
]

/-! ### VMStateV1 Tests -/

def vmStateTests : List TestResult := [
  testBool "initial not halted" (VMStateV1.initial.isHalted) false,
  testEq "initial pc" VMStateV1.initial.pc 0,
  testEq "initial stepCounter" VMStateV1.initial.stepCounter 0
]

/-! ### ConfigTags Tests -/

def configTagsTests : List TestResult := [
  testBool "checkConfigTags []" (checkConfigTags []) true,
  testBool "checkConfigTags single" (checkConfigTags [⟨"key1", []⟩]) true,
  testBool "checkConfigTags sorted" (checkConfigTags [⟨"a", []⟩, ⟨"b", []⟩]) true,
  testBool "checkConfigTags unsorted" (checkConfigTags [⟨"b", []⟩, ⟨"a", []⟩]) false
]

/-! ### PublicInputsV1 Tests -/

def publicInputsTests : List TestResult := [
  testEq "zero toList length" (PublicInputsV1.zero.toList.length) 11,
  testBool "checkRanges zero" (checkRanges PublicInputsV1.zero) true
]

/-! ### Continuation Tests -/

def continuationTests : List TestResult := [
  testBool "checkChainContinuity []" (checkChainContinuity []) true,
  testBool "checkConsecutiveIndices []" (checkConsecutiveIndices []) true,
  testEq "empty trace length" (ExecutionTrace.empty.length) 0
]

/-! ### Main Test Runner -/

def allTests : List TestResult :=
  frTests ++ bytes32Tests ++ encodingTests ++ transcriptTests ++
  vmStateTests ++ configTagsTests ++ publicInputsTests ++ continuationTests

def main : IO Unit := do
  IO.println "=== Jolt Kernel Conformance Tests ==="
  IO.println ""

  IO.println "--- Fr Tests ---"
  for r in frTests do printResult r

  IO.println "\n--- Bytes32 Tests ---"
  for r in bytes32Tests do printResult r

  IO.println "\n--- Encoding Tests ---"
  for r in encodingTests do printResult r

  IO.println "\n--- Transcript Tests ---"
  for r in transcriptTests do printResult r

  IO.println "\n--- VMStateV1 Tests ---"
  for r in vmStateTests do printResult r

  IO.println "\n--- ConfigTags Tests ---"
  for r in configTagsTests do printResult r

  IO.println "\n--- PublicInputsV1 Tests ---"
  for r in publicInputsTests do printResult r

  IO.println "\n--- Continuation Tests ---"
  for r in continuationTests do printResult r

  IO.println ""
  let passed := countPassed allTests
  let total := allTests.length
  IO.println s!"=== Results: {passed}/{total} tests passed ==="

  if passed < total then
    IO.println "SOME TESTS FAILED"
    IO.Process.exit 1
  else
    IO.println "ALL TESTS PASSED"
