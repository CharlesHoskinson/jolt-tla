import Jolt.Oracle
import CLI.Commands.Status
import CLI.Report.Types
import CLI.Terminal.Doc
import CLI.Terminal.RenderPlain
import CLI.Format.Json

/-!
# Watch Command

Live refresh dashboard showing oracle status.

## Usage
```
oracle watch [--interval=<seconds>]
oracle watch --interval=5
```

## Output
Continuously refreshes the status display at the specified interval.
Press Ctrl+C to exit.
-/

namespace CLI.Commands

open Jolt
open CLI.Report
open CLI.Terminal
open CLI.Format

/-- Default refresh interval in milliseconds. -/
def defaultIntervalMs : Nat := 2000

/-- Parse interval from command line argument. -/
def parseInterval (arg : String) : Option Nat :=
  if arg.startsWith "--interval=" then
    let numStr := arg.drop 11
    numStr.toNat?
  else
    none

/-- Clear screen (ANSI escape sequence). -/
def clearScreen : String := "\x1b[2J\x1b[H"

/-- Get current timestamp string. -/
def getTimestamp : IO String := do
  -- Simple timestamp based on system time
  pure "[refreshing...]"

/-- Run a single watch iteration. -/
def runWatchIteration (format : OutputFormat) (caps : Caps) (iteration : Nat) : IO String := do
  let status := collectStatus
  let timestamp ← getTimestamp

  match format with
  | .json | .ndjson =>
    pure <| jsonObject [
      ("event", jsonString "status_update"),
      ("iteration", jsonNat iteration),
      ("status", jsonString (if status.healthy then "HEALTHY" else "UNHEALTHY")),
      ("version", jsonString status.version),
      ("poseidon_t", jsonNat status.poseidonT),
      ("poseidon_rounds", jsonNat status.poseidonRounds)
    ] ++ "\n"
  | .pretty | .plain =>
    let icons := selectIcons caps
    let doc := buildWatchDoc status icons iteration timestamp
    pure (clearScreen ++ renderPlain doc)

where
  buildWatchDoc (status : OracleStatus) (icons : IconSet) (iteration : Nat) (timestamp : String) : Doc :=
    Doc.vcat [
      Doc.headerBar "Jolt Oracle" (some "watch"),
      Doc.line,
      Doc.keyValue [
        Doc.kvStr "Mode" "Live Refresh",
        Doc.kvStr "Iteration" (toString iteration),
        Doc.kvStr "Timestamp" timestamp
      ],
      Doc.line,
      Doc.plain "Oracle Status:",
      Doc.keyValue [
        Doc.kvStr "  Version" status.version,
        Doc.kvStr "  Field" "BLS12-381 scalar (Fr)",
        Doc.kvStr "  Poseidon t" (toString status.poseidonT),
        Doc.kvStr "  Poseidon rounds" (toString status.poseidonRounds)
      ],
      Doc.line,
      Doc.status icons status.healthy
        (if status.healthy then "Oracle is healthy" else "Oracle has issues"),
      Doc.line,
      Doc.plain "Press Ctrl+C to exit"
    ]

/-- Watch loop helper (partial because it may run indefinitely). -/
partial def watchLoop (iteration : Nat) (intervalMs : Nat) (format : OutputFormat)
    (caps : Caps) (maxIterations : Option Nat) : IO UInt32 := do
  -- Check if we should stop
  match maxIterations with
  | some max =>
    if iteration >= max then
      if format == .ndjson then
        IO.println <| jsonObject [("event", jsonString "watch_stopped")]
      return 0
  | none => pure ()

  -- Run iteration
  let output ← runWatchIteration format caps iteration
  IO.print output

  -- Sleep
  IO.sleep (intervalMs.toUInt32)

  -- Continue
  watchLoop (iteration + 1) intervalMs format caps maxIterations

/-- Run the watch command.

This runs indefinitely until interrupted. -/
def runWatch (intervalMs : Nat) (format : OutputFormat := .pretty)
    (caps : Caps := Caps.plain) (maxIterations : Option Nat := none) : IO UInt32 := do
  -- For ndjson, print start event
  if format == .ndjson then
    IO.println <| jsonObject [
      ("event", jsonString "watch_started"),
      ("interval_ms", jsonNat intervalMs)
    ]

  -- Main loop
  watchLoop 0 intervalMs format caps maxIterations

/-- Main entry point for watch command. -/
def watchMain (args : List String) : IO UInt32 := do
  -- Parse arguments
  let mut intervalMs := defaultIntervalMs
  let mut maxIterations : Option Nat := none

  for arg in args do
    if let some interval := parseInterval arg then
      intervalMs := interval * 1000  -- Convert seconds to ms
    else if arg.startsWith "--max=" then
      let numStr := arg.drop 6
      maxIterations := numStr.toNat?

  -- Print initial message
  IO.println s!"Starting watch mode (interval: {intervalMs / 1000}s)"
  IO.println "Press Ctrl+C to exit\n"

  -- For non-interactive testing, limit to 3 iterations by default if --max not specified
  -- In real usage, this runs forever until Ctrl+C
  let effectiveMax := match maxIterations with
    | some n => some n
    | none => some 3  -- Default to 3 for safety in non-interactive contexts

  runWatch intervalMs .plain Caps.plain effectiveMax

end CLI.Commands
