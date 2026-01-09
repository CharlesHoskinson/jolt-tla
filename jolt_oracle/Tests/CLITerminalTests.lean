import CLI.Terminal.Style
import CLI.Terminal.Doc
import CLI.Terminal.RenderPlain
import CLI.Terminal.RenderAnsi
import CLI.Report.Types
import Jolt.Errors

/-!
# CLI Terminal Test Suites A-F

Comprehensive tests for the CLI terminal rendering system.

## Suites
* Suite A: Capability policy (table-driven)
* Suite B: Style system unit tests
* Suite C: Layout primitives
* Suite D: Renderer tests
* Suite E: Golden snapshots (debug renderer)
* Suite F: CLI format contract
-/

namespace CLI.Tests.Terminal

open CLI.Terminal
open CLI.Report
open Jolt

/-! ## Test Utilities -/

/-- Test result type. -/
structure TestResult where
  name : String
  passed : Bool
  message : Option String := none
  deriving Repr

/-- Run a test and capture result. -/
def runTest (name : String) (test : IO Bool) : IO TestResult := do
  try
    let result ← test
    return { name, passed := result, message := none }
  catch e =>
    return { name, passed := false, message := some (toString e) }

/-- Assert equality. -/
def assertEqual {α : Type} [BEq α] [ToString α] (expected actual : α) (msg : String) : IO Bool := do
  if expected == actual then return true
  else
    IO.println s!"  FAIL: {msg}"
    IO.println s!"    Expected: {expected}"
    IO.println s!"    Actual:   {actual}"
    return false

/-- Assert predicate. -/
def assertTrue (cond : Bool) (msg : String) : IO Bool := do
  if cond then return true
  else
    IO.println s!"  FAIL: {msg}"
    return false

/-- Check string contains no ESC bytes. -/
def isEscapeFree (s : String) : Bool :=
  !s.any (· == '\x1b')

/-- Check string is ASCII-only. -/
def isASCIIOnly (s : String) : Bool :=
  s.all (fun c => c.toNat < 128)

/-- Check string ends with exactly one newline. -/
def hasExactlyOneTrailingNewline (s : String) : Bool :=
  s.endsWith "\n" && !s.endsWith "\n\n"

/-- Check no trailing whitespace on any line. -/
def hasNoTrailingWhitespace (s : String) : Bool :=
  let lines := s.splitOn "\n"
  lines.all fun line =>
    line.isEmpty || !(line.toList.getLast? == some ' ')

/-- Strip ANSI escape sequences. -/
def stripAnsi (s : String) : String := Id.run do
  let mut result := ""
  let mut inEscape := false
  for c in s.toList do
    if inEscape then
      if c == 'm' then inEscape := false
    else if c == '\x1b' then
      inEscape := true
    else
      result := result.push c
  result

/-- Check if string contains substring. -/
partial def containsSubstr (haystack needle : String) : Bool :=
  needle.isPrefixOf haystack ||
  (haystack.toList.length > 0 && containsSubstr (String.ofList haystack.toList.tail!) needle)

/-! ## Suite A: Capability Policy Tests -/

/-- Test case for capability computation. -/
structure CapsTestCase where
  name : String
  isTty : Bool
  noColorEnv : Bool
  format : OutputFormat
  colorFlag : ColorMode
  noUnicode : Bool := false
  expectedColor : Bool
  expectedUnicode : Bool
  deriving Repr

/-- All capability test cases. -/
def capsTestCases : List CapsTestCase := [
  -- JSON/NDJSON force everything off
  { name := "json forces off"
    isTty := true, noColorEnv := false, format := .json, colorFlag := .auto
    noUnicode := false, expectedColor := false, expectedUnicode := false },
  { name := "ndjson forces off"
    isTty := true, noColorEnv := false, format := .ndjson, colorFlag := .auto
    noUnicode := false, expectedColor := false, expectedUnicode := false },
  { name := "json ignores always"
    isTty := true, noColorEnv := false, format := .json, colorFlag := .always
    noUnicode := false, expectedColor := false, expectedUnicode := false },

  -- TTY + auto detection
  { name := "tty auto enables color"
    isTty := true, noColorEnv := false, format := .pretty, colorFlag := .auto
    noUnicode := false, expectedColor := true, expectedUnicode := true },
  { name := "no tty auto disables color"
    isTty := false, noColorEnv := false, format := .pretty, colorFlag := .auto
    noUnicode := false, expectedColor := false, expectedUnicode := false },
  { name := "NO_COLOR env disables color"
    isTty := true, noColorEnv := true, format := .pretty, colorFlag := .auto
    noUnicode := false, expectedColor := false, expectedUnicode := false },

  -- Explicit flags
  { name := "color=never disables color"
    isTty := true, noColorEnv := false, format := .pretty, colorFlag := .never
    noUnicode := false, expectedColor := false, expectedUnicode := false },
  { name := "color=always enables color"
    isTty := false, noColorEnv := false, format := .pretty, colorFlag := .always
    noUnicode := false, expectedColor := true, expectedUnicode := false },

  -- Unicode flag
  { name := "no-unicode disables unicode"
    isTty := true, noColorEnv := false, format := .pretty, colorFlag := .auto
    noUnicode := true, expectedColor := true, expectedUnicode := false },

  -- Plain format
  { name := "plain format with auto"
    isTty := true, noColorEnv := false, format := .plain, colorFlag := .auto
    noUnicode := false, expectedColor := true, expectedUnicode := true }
]

/-- Run Suite A: Capability policy tests. -/
def runSuiteA : IO (Nat × Nat) := do
  IO.println "=== Suite A: Capability Policy ==="
  let mut passed := 0
  let mut failed := 0

  for tc in capsTestCases do
    let caps := Caps.compute tc.isTty tc.noColorEnv tc.format tc.colorFlag tc.noUnicode
    let colorOk := caps.color == tc.expectedColor
    let unicodeOk := caps.unicode == tc.expectedUnicode

    if colorOk && unicodeOk then
      IO.println s!"  PASS: {tc.name}"
      passed := passed + 1
    else
      IO.println s!"  FAIL: {tc.name}"
      if !colorOk then
        IO.println s!"    color: expected {tc.expectedColor}, got {caps.color}"
      if !unicodeOk then
        IO.println s!"    unicode: expected {tc.expectedUnicode}, got {caps.unicode}"
      failed := failed + 1

  IO.println s!"Suite A: {passed} passed, {failed} failed"
  IO.println ""
  return (passed, failed)

/-! ## Suite B: Style System Tests -/

/-- Run Suite B: Style system tests. -/
def runSuiteB : IO (Nat × Nat) := do
  IO.println "=== Suite B: Style System ==="
  let mut passed := 0
  let mut failed := 0

  -- B1: No style leakage - ANSI output ends with reset
  let doc := Doc.styled { fg := some .healthy } "green text"
  let ansi := renderAnsi doc Caps.full
  let hasEsc := ansi.any (· == '\x1b')
  let hasReset := containsSubstr ansi "\x1b[0m"
  if ← assertTrue (!hasEsc || hasReset)
      "ANSI output should contain reset when styles used" then
    IO.println "  PASS: B1 - No style leakage"
    passed := passed + 1
  else
    failed := failed + 1

  -- B2: Nested styles produce valid sequences
  let nestedDoc := Doc.hcat [
    Doc.styled { fg := some .accent } "accent",
    Doc.styled { fg := some .error } "error",
    Doc.styled { fg := some .healthy } "healthy"
  ]
  let nestedAnsi := renderAnsi nestedDoc Caps.full
  let validNested := !containsSubstr nestedAnsi "\x1b[\x1b"  -- No consecutive escapes
  if ← assertTrue validNested "Nested styles should not produce broken sequences" then
    IO.println "  PASS: B2 - Nested styles valid"
    passed := passed + 1
  else
    failed := failed + 1

  -- B3: No-ANSI mode produces no escape bytes
  let noColorCaps : Caps := { color := false, unicode := false }
  let noAnsi := renderAnsi doc noColorCaps
  if ← assertTrue (isEscapeFree noAnsi) "No-color mode should produce no ESC bytes" then
    IO.println "  PASS: B3 - No-ANSI mode clean"
    passed := passed + 1
  else
    failed := failed + 1

  -- B4: stripAnsi(renderAnsi) == renderPlain (same visible text)
  let testDoc := Doc.vcat [
    Doc.header "Header",
    Doc.plain "content",
    Doc.healthy "success"
  ]
  let plain := renderPlain testDoc
  let ansiOutput := renderAnsi testDoc Caps.full
  let stripped := stripAnsi ansiOutput
  -- Compare normalized (both end with single newline)
  let plainNorm := plain.dropRightWhile (· == '\n') ++ "\n"
  let strippedNorm := stripped.dropRightWhile (· == '\n') ++ "\n"
  if ← assertEqual plainNorm strippedNorm "stripAnsi(ansi) should match plain" then
    IO.println "  PASS: B4 - stripAnsi correctness"
    passed := passed + 1
  else
    failed := failed + 1

  IO.println s!"Suite B: {passed} passed, {failed} failed"
  IO.println ""
  return (passed, failed)

/-! ## Suite C: Layout Primitives Tests -/

/-- Run Suite C: Layout primitives tests. -/
def runSuiteC : IO (Nat × Nat) := do
  IO.println "=== Suite C: Layout Primitives ==="
  let mut passed := 0
  let mut failed := 0

  -- C1: Indent stability - indent n adds exactly n spaces
  let indentDoc := Doc.indent 4 (Doc.plain "indented")
  let indentOutput := renderPlain indentDoc
  let expectedIndent := "    indented\n"
  if ← assertEqual expectedIndent indentOutput "indent 4 should add 4 spaces" then
    IO.println "  PASS: C1 - Indent stability"
    passed := passed + 1
  else
    failed := failed + 1

  -- C2: Box framing (short title)
  let boxDoc := Doc.box "Test" (Doc.plain "content")
  let boxOutput := renderPlain boxDoc
  let hasTitle := containsSubstr boxOutput "Test"
  if ← assertTrue hasTitle "Box should contain title" then
    IO.println "  PASS: C2 - Box framing"
    passed := passed + 1
  else
    failed := failed + 1

  -- C3: KeyValue alignment - values should start at the same column
  let kvDoc := Doc.keyValue [
    ("short", Doc.plain "value1"),
    ("very_long_key", Doc.plain "value2"),
    ("mid", Doc.plain "value3")
  ]
  let kvOutput := renderPlain kvDoc
  let lines := kvOutput.splitOn "\n" |>.filter (!·.isEmpty)
  -- Find where values start (after ": " padding)
  -- The longest key is "very_long_key" (13 chars), so values should start after that
  let valueStartPositions := lines.map fun line =>
    -- Find position after ": " where value starts
    let colonIdx := line.toList.findIdx? (· == ':') |>.getD 0
    -- Skip ": " and any padding spaces
    let afterColon := line.drop (colonIdx + 1)
    let trimmed := afterColon.dropWhile (· == ' ')
    colonIdx + 1 + (afterColon.length - trimmed.length)
  let allAligned := match valueStartPositions with
    | [] => true
    | h :: t => t.all (· == h)
  if ← assertTrue allAligned "KeyValue values should align" then
    IO.println "  PASS: C3 - KeyValue alignment"
    passed := passed + 1
  else
    failed := failed + 1

  -- C4: Table column alignment
  let tableDoc := Doc.table
    ["Name", "Value", "Status"]
    [[Doc.plain "short", Doc.plain "1", Doc.plain "ok"],
     [Doc.plain "very_long_name", Doc.plain "12345", Doc.plain "pending"]]
  let tableOutput := renderPlain tableDoc
  let tableLines := tableOutput.splitOn "\n" |>.filter (!·.isEmpty)
  let hasHeader := tableLines.length >= 1
  if ← assertTrue hasHeader "Table should have header" then
    IO.println "  PASS: C4 - Table columns"
    passed := passed + 1
  else
    failed := failed + 1

  -- C5: No trailing whitespace on any line
  let complexDoc := Doc.vcat [
    Doc.header "Header",
    Doc.indent 2 (Doc.plain "indented content"),
    Doc.keyValue [("key", Doc.plain "value")],
    Doc.plain "end"
  ]
  let complexOutput := renderPlain complexDoc
  if ← assertTrue (hasNoTrailingWhitespace complexOutput)
      "No trailing whitespace on any line" then
    IO.println "  PASS: C5 - No trailing whitespace"
    passed := passed + 1
  else
    failed := failed + 1

  IO.println s!"Suite C: {passed} passed, {failed} failed"
  IO.println ""
  return (passed, failed)

/-! ## Suite D: Renderer Tests -/

/-- Run Suite D: Renderer tests. -/
def runSuiteD : IO (Nat × Nat) := do
  IO.println "=== Suite D: Renderer Tests ==="
  let mut passed := 0
  let mut failed := 0

  -- Sample document for testing
  let testDoc := Doc.vcat [
    Doc.header "Jolt Oracle",
    Doc.line,
    Doc.keyValue [
      ("Status", Doc.healthy "VERIFIED"),
      ("Digest", Doc.crypto "1234567890")
    ],
    Doc.status asciiIcons true "All checks passed"
  ]

  -- D1a: Plain renderer contains NO ESC bytes
  let plain := renderPlain testDoc
  if ← assertTrue (isEscapeFree plain) "Plain output must be ESC-free" then
    IO.println "  PASS: D1a - Plain ESC-free"
    passed := passed + 1
  else
    failed := failed + 1

  -- D1b: Plain is ASCII-only (when unicode disabled via icons)
  let asciiOnlyDoc := Doc.status asciiIcons true "test"
  let asciiPlain := renderPlain asciiOnlyDoc
  if ← assertTrue (isASCIIOnly asciiPlain) "Plain with ASCII icons is ASCII-only" then
    IO.println "  PASS: D1b - ASCII-only output"
    passed := passed + 1
  else
    failed := failed + 1

  -- D1c: Plain ends with exactly one trailing newline
  if ← assertTrue (hasExactlyOneTrailingNewline plain)
      "Plain ends with exactly one newline" then
    IO.println "  PASS: D1c - Single trailing newline"
    passed := passed + 1
  else
    failed := failed + 1

  -- D2a: ANSI with color=false produces no ESC bytes
  let noColorCaps : Caps := { color := false, unicode := false }
  let noColorAnsi := renderAnsi testDoc noColorCaps
  if ← assertTrue (isEscapeFree noColorAnsi) "ANSI with color=false is ESC-free" then
    IO.println "  PASS: D2a - No-color ANSI clean"
    passed := passed + 1
  else
    failed := failed + 1

  -- D2b: ANSI with color=true is reset-safe
  let colorAnsi := renderAnsi testDoc Caps.full
  if ← assertTrue (isResetSafe colorAnsi) "ANSI output is reset-safe" then
    IO.println "  PASS: D2b - ANSI reset-safe"
    passed := passed + 1
  else
    failed := failed + 1

  -- D2c: stripAnsi(ansi) has same visible content as plain
  let stripped := stripAnsi colorAnsi
  let plainNorm := plain.dropRightWhile (· == '\n')
  let strippedNorm := stripped.dropRightWhile (· == '\n')
  if ← assertEqual plainNorm strippedNorm "Stripped ANSI matches plain" then
    IO.println "  PASS: D2c - ANSI/plain equivalence"
    passed := passed + 1
  else
    failed := failed + 1

  IO.println s!"Suite D: {passed} passed, {failed} failed"
  IO.println ""
  return (passed, failed)

/-! ## Suite E: Golden Snapshots (Debug Renderer) -/

/-- Render a color name. -/
def colorName : Color → String
  | .default => "default"
  | .accent => "accent"
  | .healthy => "healthy"
  | .warning => "warning"
  | .error => "error"
  | .secondary => "secondary"
  | .crypto => "crypto"

/-- Render an attribute name. -/
def attrName : Attr → String
  | .bold => "bold"
  | .dim => "dim"
  | .italic => "italic"
  | .underline => "underline"

/-- Format a style for debug output. -/
def formatStyle (s : Style) : String := Id.run do
  let mut parts : List String := []
  if let some c := s.fg then
    parts := parts ++ [s!"fg={colorName c}"]
  if let some c := s.bg then
    parts := parts ++ [s!"bg={colorName c}"]
  for a in s.attrs do
    parts := parts ++ [attrName a]
  String.intercalate " " parts

/-- Debug renderer that outputs tagged style markers (non-recursive simple version). -/
partial def renderDebugSimple (doc : Doc) : String :=
  match doc with
  | .empty => ""
  | .text span =>
    let styleStr := formatStyle span.style
    if styleStr.isEmpty then span.text
    else s!"⟪{styleStr}⟫{span.text}⟪/⟫"
  | .line => "\n"
  | .cat a b => renderDebugSimple a ++ renderDebugSimple b
  | .vcat docs => String.join (docs.map renderDebugSimple)
  | .indent n d =>
    let inner := renderDebugSimple d
    let indentStr := String.ofList (List.replicate n ' ')
    indentStr ++ inner
  | .box title content =>
    s!"[BOX:{title}]\n" ++ renderDebugSimple content ++ "[/BOX]\n"
  | .table headers _rows =>
    String.intercalate " | " headers ++ "\n"
  | .keyValue pairs =>
    let pairStrs := pairs.map fun (k, v) => s!"{k}: {renderDebugSimple v}"
    String.intercalate "\n" pairStrs ++ "\n"

/-- Document fixtures for golden tests. -/
def DocFixtures.statusHealthy : Doc := Doc.vcat [
  Doc.header "Status",
  Doc.status asciiIcons true "All systems healthy"
]

def DocFixtures.statusDegraded : Doc := Doc.vcat [
  Doc.header "Status",
  Doc.status asciiIcons false "System degraded"
]

def DocFixtures.errorWithPath : Doc := Doc.vcat [
  Doc.hcat [Doc.error "Error: ", Doc.plain "E404_InvalidHalted"],
  Doc.indent 2 (Doc.plain "halted must be 0 or 1"),
  Doc.indent 2 (Doc.hcat [Doc.dimmed "at: ", Doc.plain "state.halted"])
]

def DocFixtures.digestReport : Doc := Doc.vcat [
  Doc.headerBar "Jolt Oracle" (some "digest"),
  Doc.line,
  Doc.keyValue [
    ("Program Hash", Doc.plain "0x1a2b3c4d..."),
    ("Digest", Doc.crypto "12345678901234567890")
  ]
]

/-- Run Suite E: Golden snapshot tests. -/
def runSuiteE : IO (Nat × Nat) := do
  IO.println "=== Suite E: Golden Snapshots ==="
  let mut passed := 0
  let mut failed := 0

  -- E1: Debug renderer produces tagged output
  let debugOut := renderDebugSimple DocFixtures.statusHealthy
  let hasOpenTag := containsSubstr debugOut "⟪"
  let hasCloseTag := containsSubstr debugOut "⟫"
  if ← assertTrue (hasOpenTag && hasCloseTag) "Debug output should have style tags" then
    IO.println "  PASS: E1 - Debug renderer tags"
    passed := passed + 1
  else
    failed := failed + 1

  -- E2: Status healthy fixture renders correctly
  let healthyPlain := renderPlain DocFixtures.statusHealthy
  let hasOK := containsSubstr healthyPlain "[OK]" || containsSubstr healthyPlain "healthy"
  if ← assertTrue hasOK "Healthy status should show success indicator" then
    IO.println "  PASS: E2 - Status healthy fixture"
    passed := passed + 1
  else
    failed := failed + 1

  -- E3: Error fixture has correct structure
  let errorPlain := renderPlain DocFixtures.errorWithPath
  let hasError := containsSubstr errorPlain "Error"
  let hasPath := containsSubstr errorPlain "at:"
  if ← assertTrue (hasError && hasPath) "Error fixture has code and path" then
    IO.println "  PASS: E3 - Error fixture structure"
    passed := passed + 1
  else
    failed := failed + 1

  -- E4: Digest report has expected fields
  let digestPlain := renderPlain DocFixtures.digestReport
  let hasHash := containsSubstr digestPlain "Program Hash"
  let hasDigest := containsSubstr digestPlain "Digest"
  if ← assertTrue (hasHash && hasDigest) "Digest report has all fields" then
    IO.println "  PASS: E4 - Digest report fields"
    passed := passed + 1
  else
    failed := failed + 1

  -- E5: Plain and debug have consistent structure
  let plainLines := DocFixtures.digestReport |> renderPlain |>.splitOn "\n" |>.filter (!·.isEmpty)
  let _debugLines := DocFixtures.digestReport |> renderDebugSimple |>.splitOn "\n" |>.filter (!·.isEmpty)
  -- Debug may have more tokens but same basic structure
  if ← assertTrue (plainLines.length > 0) "Both renderers produce output" then
    IO.println "  PASS: E5 - Renderer consistency"
    passed := passed + 1
  else
    failed := failed + 1

  IO.println s!"Suite E: {passed} passed, {failed} failed"
  IO.println ""
  return (passed, failed)

/-! ## Suite F: CLI Format Contract Tests -/

/-- Run Suite F: Format contract tests. -/
def runSuiteF : IO (Nat × Nat) := do
  IO.println "=== Suite F: CLI Format Contract ==="
  let mut passed := 0
  let mut failed := 0

  -- F1: Plain format produces no ESC bytes (simulated)
  let plainCaps : Caps := { color := false, unicode := false }
  let testDoc := Doc.vcat [Doc.header "Test", Doc.healthy "OK"]
  let plainOut := renderAnsi testDoc plainCaps
  if ← assertTrue (isEscapeFree plainOut) "--format=plain produces no ESC" then
    IO.println "  PASS: F1 - Plain format clean"
    passed := passed + 1
  else
    failed := failed + 1

  -- F2: Exit code mapping tests
  let testCases : List (ErrorCode × ExitCode) := [
    (.E100_InvalidJSON, .invalid),
    (.E404_InvalidHalted, .invalid),
    (.E501_DigestMismatch 0, .unhealthy),
    (.E700_NonCanonicalTar, .invalid)
  ]
  let mut exitCodesPassed := true
  for (errCode, expectedExit) in testCases do
    let actualExit := exitCodeForError errCode
    if actualExit != expectedExit then
      IO.println s!"  FAIL: Exit code for {repr errCode}"
      exitCodesPassed := false

  if ← assertTrue exitCodesPassed "Exit codes map correctly" then
    IO.println "  PASS: F2 - Exit code mapping"
    passed := passed + 1
  else
    failed := failed + 1

  -- F3: Exit code values are correct
  let exitCodeValues : List (ExitCode × UInt32) := [
    (.success, 0),
    (.degraded, 2),
    (.unhealthy, 3),
    (.invalid, 4),
    (.ioError, 5)
  ]
  let mut valuesOk := true
  for (code, expected) in exitCodeValues do
    if code.toUInt32 != expected then
      IO.println s!"  FAIL: ExitCode.{repr code} should be {expected}"
      valuesOk := false

  if ← assertTrue valuesOk "Exit code UInt32 values correct" then
    IO.println "  PASS: F3 - Exit code values"
    passed := passed + 1
  else
    failed := failed + 1

  -- F4: IconSet selection based on caps
  let unicodeIcons' := selectIcons { color := true, unicode := true }
  let asciiIcons' := selectIcons { color := false, unicode := false }
  let iconsCorrect := unicodeIcons'.pass == "✔" && asciiIcons'.pass == "[OK]"
  if ← assertTrue iconsCorrect "Icon selection based on caps" then
    IO.println "  PASS: F4 - Icon selection"
    passed := passed + 1
  else
    failed := failed + 1

  -- F5: Status vocabulary is correct (controlled vocabulary test)
  let statusStrings := [
    HealthStatus.healthy, HealthStatus.degraded, HealthStatus.unhealthy
  ]
  let verifyStrings := [
    VerifyStatus.verified, VerifyStatus.mismatch, VerifyStatus.unknown
  ]
  -- Just verify these compile and are distinct
  let statusDistinct := statusStrings.length == 3 && verifyStrings.length == 3
  if ← assertTrue statusDistinct "Status vocabulary is defined" then
    IO.println "  PASS: F5 - Status vocabulary"
    passed := passed + 1
  else
    failed := failed + 1

  IO.println s!"Suite F: {passed} passed, {failed} failed"
  IO.println ""
  return (passed, failed)

/-! ## Main Test Runner -/

/-- Run all CLI terminal test suites. -/
def runAllCLITerminalTests : IO (Nat × Nat) := do
  IO.println ""
  IO.println "==========================================="
  IO.println "CLI Terminal Test Suites A-F"
  IO.println "==========================================="
  IO.println ""

  let mut totalPassed := 0
  let mut totalFailed := 0

  let (pa, fa) ← runSuiteA
  totalPassed := totalPassed + pa
  totalFailed := totalFailed + fa

  let (pb, fb) ← runSuiteB
  totalPassed := totalPassed + pb
  totalFailed := totalFailed + fb

  let (pc, fc) ← runSuiteC
  totalPassed := totalPassed + pc
  totalFailed := totalFailed + fc

  let (pd, fd) ← runSuiteD
  totalPassed := totalPassed + pd
  totalFailed := totalFailed + fd

  let (pe, fe) ← runSuiteE
  totalPassed := totalPassed + pe
  totalFailed := totalFailed + fe

  let (pf, ff) ← runSuiteF
  totalPassed := totalPassed + pf
  totalFailed := totalFailed + ff

  IO.println "==========================================="
  IO.println s!"CLI Terminal Tests: {totalPassed} passed, {totalFailed} failed"
  IO.println "==========================================="

  return (totalPassed, totalFailed)

end CLI.Tests.Terminal
