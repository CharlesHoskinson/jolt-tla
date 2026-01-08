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

/-- Default iteration count. -/
def defaultIterationCount : Nat := 30

/-- Watch options. -/
structure WatchOpts where
  intervalMs : Nat := defaultIntervalMs
  count : Nat := defaultIterationCount
  quiet : Bool := false
  deriving Repr

/-- Parse watch options from command line arguments. -/
def parseWatchOpts (args : List String) : WatchOpts := Id.run do
  let mut opts : WatchOpts := {}

  for arg in args do
    if arg.startsWith "--interval=" then
      if let some n := (arg.drop 11).toNat? then
        opts := { opts with intervalMs := n * 1000 }  -- Convert seconds to ms
    else if arg.startsWith "--count=" then
      if let some n := (arg.drop 8).toNat? then
        opts := { opts with count := n }
    else if arg.startsWith "--max=" then  -- Backwards compatibility
      if let some n := (arg.drop 6).toNat? then
        opts := { opts with count := n }
    else if arg == "--quiet" || arg == "-q" then
      opts := { opts with quiet := true }
    else if let some n := arg.toNat? then
      -- Bare number = interval in seconds
      opts := { opts with intervalMs := n * 1000 }

  opts

/-- Parse interval from command line argument (backwards compatibility). -/
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
def runWatchIteration (format : OutputFormat) (caps : Caps) (iteration : Nat)
    (maxIterations : Option Nat := none) : IO String := do
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
    let doc := buildWatchDoc status icons iteration maxIterations timestamp
    pure (clearScreen ++ renderPlain doc)

where
  buildWatchDoc (status : OracleStatus) (icons : IconSet) (iteration : Nat)
      (maxIterations : Option Nat) (timestamp : String) : Doc :=
    let iterStr := match maxIterations with
      | some max => s!"[{iteration + 1}/{max}]"
      | none => s!"[{iteration + 1}]"
    Doc.vcat [
      Doc.headerBar "Jolt Oracle" (some "watch"),
      Doc.line,
      Doc.keyValue [
        Doc.kvStr "Mode" "Live Refresh",
        Doc.kvStr "Iteration" iterStr,
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

  -- Run iteration (pass maxIterations for display)
  let output ← runWatchIteration format caps iteration maxIterations
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
  -- Parse arguments with new WatchOpts structure
  let opts := parseWatchOpts args

  -- Print initial message (unless quiet)
  if !opts.quiet then
    IO.eprintln s!"Starting watch mode (interval: {opts.intervalMs / 1000}s, count: {opts.count})"
    IO.eprintln "Press Ctrl+C to exit\n"

  runWatch opts.intervalMs .plain Caps.plain (some opts.count)

end CLI.Commands
