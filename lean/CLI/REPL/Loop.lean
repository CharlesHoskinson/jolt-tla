import CLI.REPL.Eval

/-!
# REPL Main Loop

The main read-eval-print loop with proper stdout/stderr discipline.

## Design
- Prompts and diagnostics go to stderr
- Command output goes to stdout
- Supports multi-line input for JSON
- Handles EOF (Ctrl+D) gracefully
-/

namespace CLI.REPL

open CLI.Terminal

/-- Print the startup banner to stderr. -/
def printBanner (caps : UiCaps) : IO Unit := do
  let theme := getTheme caps
  writelnStderr s!"{theme.bold}{replVersion}{theme.reset}"
  writelnStderr "Type ':help' for commands, ':quit' to exit."
  writelnStderr ""

/-- Print output with proper stdout/stderr discipline. -/
def printOutput (output : ReplOutput) : IO Unit := do
  -- Diagnostics to stderr
  if !output.err.isEmpty then
    writeStderr output.err
  -- Data to stdout
  if !output.out.isEmpty then
    IO.print output.out

/-- Read a line from stdin, returning None on EOF. -/
def readLine : IO (Option String) := do
  let stdin ← IO.getStdin
  try
    let line ← stdin.getLine
    if line.isEmpty then
      return none  -- EOF
    else
      -- Strip trailing newline
      let trimmed := if line.endsWith "\n" then line.dropRight 1 else line
      let trimmed := if trimmed.endsWith "\r" then trimmed.dropRight 1 else trimmed
      return some trimmed
  catch _ =>
    return none

/-- Check if a line should be recorded in history.
    Lines starting with space are not recorded (secrets convention). -/
def shouldRecordHistory (line : String) : Bool :=
  !line.isEmpty && line.toList[0]? != some ' '

/-- Handle multi-line input for JSON. -/
partial def readMultiLine (state : ReplState) (caps : UiCaps) (buffer : String)
    : IO (Option String × ReplState) := do
  -- Check if buffer is balanced
  if isBalanced buffer then
    return (some buffer, { state with inMultiLine := false, lineBuffer := #[] })

  -- Print continuation prompt
  let state' := { state with inMultiLine := true }
  writeStderr (buildPrompt state' caps)

  match ← readLine with
  | none =>
    -- EOF during multi-line - return what we have
    return (some buffer, { state with inMultiLine := false, lineBuffer := #[] })
  | some line =>
    let newBuffer := buffer ++ "\n" ++ line
    readMultiLine state' caps newBuffer

/-- Main REPL loop. -/
partial def replLoop (state : ReplState) (caps : UiCaps) : IO UInt32 := do
  -- Print prompt to stderr
  writeStderr (buildPrompt state caps)

  match ← readLine with
  | none =>
    -- EOF (Ctrl+D)
    writelnStderr ""  -- New line after prompt
    return 0
  | some line =>
    -- Skip empty lines
    if line.trim.isEmpty then
      replLoop state caps
    else
      -- Check for multi-line input
      let (fullInput, state') ← if startsMultiLine line then
        readMultiLine state caps line
      else
        pure (some line, state)

      match fullInput with
      | none =>
        -- EOF during multi-line
        return 0
      | some input =>
        -- Record in history (unless starts with space)
        let state'' := if shouldRecordHistory input then
          state'.addHistory input
        else
          state'

        -- Evaluate the line
        match ← evalLine input state'' with
        | .exit code =>
          return code
        | .continue newState output =>
          printOutput output
          replLoop newState caps

/-- Run the REPL with the given options. -/
def runRepl (colorMode : ColorMode := .auto)
    (nonInteractive : Bool := false) : IO UInt32 := do
  -- Detect capabilities
  let caps ← detectCaps colorMode

  -- Force non-interactive settings if requested
  let caps := if nonInteractive then
    { caps with color := false, unicode := false, isInteractive := false }
  else
    caps

  -- Print banner (only in interactive mode)
  if caps.isInteractive && !nonInteractive then
    printBanner caps

  -- Initialize state
  let state : ReplState := {}

  -- Run the loop
  replLoop state caps

/-- Entry point for 'oracle repl' command. -/
def replMain (args : List String) : IO UInt32 := do
  -- Parse arguments
  let mut colorMode := ColorMode.auto
  let mut nonInteractive := false

  for arg in args do
    if arg == "--color=always" then
      colorMode := .always
    else if arg == "--color=never" || arg == "--no-color" then
      colorMode := .never
    else if arg == "--non-interactive" || arg == "-n" then
      nonInteractive := true

  runRepl colorMode nonInteractive

end CLI.REPL
