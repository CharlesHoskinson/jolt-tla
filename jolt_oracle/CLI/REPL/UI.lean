import CLI.REPL.Types
import CLI.Terminal.Style
import CLI.Report.Types

/-!
# REPL UI Foundation

Terminal capability detection, theming, ANSI helpers, and prompt building.

## Main Definitions
* `UiCaps` - Extended UI capabilities beyond basic Caps
* `Theme` - Color theme for REPL elements
* `detectCaps` - Detect capabilities from environment
* `buildPrompt` - Generate the REPL prompt string
-/

namespace CLI.REPL

open CLI.Terminal
open CLI.Report

/-- Extended UI capabilities for REPL. -/
structure UiCaps where
  color : Bool        -- ANSI color sequences allowed
  unicode : Bool      -- Unicode glyphs allowed
  isInteractive : Bool -- Connected to a TTY
  termWidth : Nat := 80  -- Terminal width for wrapping
  termHeight : Nat := 24 -- Terminal height for paging
  deriving Repr, BEq

instance : Inhabited UiCaps where
  default := { color := false, unicode := false, isInteractive := false }

/-- REPL-specific theme colors as ANSI escape sequences. -/
structure Theme where
  ok : String := "\x1b[32m"       -- green
  err : String := "\x1b[31m"      -- red
  warn : String := "\x1b[33m"     -- yellow
  info : String := "\x1b[36m"     -- cyan
  dim : String := "\x1b[2m"       -- dim
  bold : String := "\x1b[1m"      -- bold
  crypto : String := "\x1b[35m"   -- magenta
  reset : String := "\x1b[0m"
  deriving Repr

/-- Default theme. -/
def defaultTheme : Theme := {}

/-- No-color theme (all empty strings). -/
def noColorTheme : Theme :=
  { ok := "", err := "", warn := "", info := "", dim := "",
    bold := "", crypto := "", reset := "" }

/-- Get theme based on color capability. -/
def getTheme (caps : UiCaps) : Theme :=
  if caps.color then defaultTheme else noColorTheme

/-- ANSI escape: clear screen. -/
def clearScreen : String := "\x1b[2J\x1b[H"

/-- ANSI escape: clear to end of line. -/
def clearToEol : String := "\x1b[K"

/-- ANSI escape: move cursor up N lines. -/
def cursorUp (n : Nat) : String := s!"\x1b[{n}A"

/-- ANSI escape: move cursor to column N. -/
def cursorCol (n : Nat) : String := s!"\x1b[{n}G"

/-- Detect UI capabilities from environment.
    This is an IO function that queries the environment. -/
def detectCaps (mode : ColorMode) : IO UiCaps := do
  -- Check if stdin/stderr are TTYs
  let stdinTty ← IO.FS.Stream.isTty (← IO.getStdin)
  let stderrTty ← IO.FS.Stream.isTty (← IO.getStderr)
  let isInteractive := stdinTty && stderrTty

  -- Check NO_COLOR environment variable
  let noColor := (← IO.getEnv "NO_COLOR").isSome

  -- Check TERM environment variable
  let term := (← IO.getEnv "TERM").getD ""
  let isDumb := term == "dumb" || term == ""

  -- Determine color support
  let colorEnabled := match mode with
    | .always => true
    | .never => false
    | .auto => isInteractive && !noColor && !isDumb

  -- Unicode support (follows color + interactive)
  let unicodeEnabled := colorEnabled && isInteractive

  -- Terminal dimensions (default if can't detect)
  -- In a real implementation, we'd query TIOCGWINSZ or COLUMNS/LINES
  let termWidth := (← IO.getEnv "COLUMNS").bind String.toNat? |>.getD 80
  let termHeight := (← IO.getEnv "LINES").bind String.toNat? |>.getD 24

  pure { color := colorEnabled, unicode := unicodeEnabled,
         isInteractive, termWidth, termHeight }

/-- Convert UiCaps to basic Caps for compatibility. -/
def UiCaps.toCaps (ui : UiCaps) : Caps :=
  { color := ui.color, unicode := ui.unicode }

/-- REPL prompt icons. -/
structure PromptIcons where
  success : String
  failure : String
  continuation : String
  deriving Repr

/-- Unicode prompt icons. -/
def unicodePromptIcons : PromptIcons :=
  { success := "✔", failure := "✖", continuation := "..." }

/-- ASCII prompt icons. -/
def asciiPromptIcons : PromptIcons :=
  { success := "+", failure := "!", continuation := "..." }

/-- Get prompt icons based on capabilities. -/
def getPromptIcons (caps : UiCaps) : PromptIcons :=
  if caps.unicode then unicodePromptIcons else asciiPromptIcons

/-- Build the REPL prompt string.

    Format:
    - `jolt ✔ > ` for success
    - `jolt ✖(3) > ` for failure with exit code 3
    - `jolt [file.json] ✔ > ` with context file
    - `...> ` for continuation (dim) -/
def buildPrompt (state : ReplState) (caps : UiCaps) : String :=
  let theme := getTheme caps
  let icons := getPromptIcons caps

  if state.inMultiLine then
    -- Continuation prompt (dim)
    s!"{theme.dim}{icons.continuation}> {theme.reset}"
  else
    let promptPrefix := "jolt"

    -- Context file indicator
    let context := match state.contextFile with
      | some f =>
        -- Truncate long filenames
        let display := if f.length > 20 then
          s!"{f.take 8}...{f.drop (f.length - 8)}"
        else f
        s!" [{display}]"
      | none => ""

    -- Status indicator
    let (statusIcon, statusColor) := if state.lastExitCode == .success then
      (icons.success, theme.ok)
    else
      let code := state.lastExitCode.toUInt32
      (s!"{icons.failure}({code})", theme.err)

    s!"{promptPrefix}{context} {statusColor}{statusIcon}{theme.reset} > "

/-- Build prompt for non-interactive (testing) mode.
    No colors, minimal formatting. -/
def buildPlainPrompt (state : ReplState) : String :=
  if state.inMultiLine then
    "...> "
  else
    let context := match state.contextFile with
      | some f => s!" [{f}]"
      | none => ""
    let status := if state.lastExitCode == .success then "+" else "!"
    s!"jolt{context} {status} > "

/-- Format a value with potential redaction.
    If redactMode is on and value is a secret, show [REDACTED]. -/
def formatValue (state : ReplState) (v : Variable) : String :=
  if state.redactMode && v.isSecret then
    "[REDACTED]"
  else if v.isSecret then
    "[REDACTED]"
  else
    match v.value with
    | .str s =>
      if s.length > 50 then s!"\"{s.take 20}...{s.drop (s.length - 20)}\""
      else s!"\"{s}\""
    | .digest d => s!"{d}"
    | .bytes32 _ => "<bytes32>"
    | .state _ => "<vmstate>"
    | .exitCode c => s!"{c}"
    | .json j =>
      if j.length > 50 then s!"{j.take 20}...{j.drop (j.length - 20)}"
      else j
    | .none => "(none)"


/-- Write to stderr (for prompts and diagnostics). -/
def writeStderr (s : String) : IO Unit := do
  let stderr ← IO.getStderr
  stderr.putStr s
  stderr.flush

/-- Write a line to stderr. -/
def writelnStderr (s : String) : IO Unit := do
  let stderr ← IO.getStderr
  stderr.putStrLn s
  stderr.flush

end CLI.REPL
