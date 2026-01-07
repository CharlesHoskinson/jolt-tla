/-!
# Jolt Oracle CLI

Command-line interface for the Jolt Oracle.

## Commands
- `digest` - Compute state digest
- `verify` - Verify chain
- `test` - Run test vectors
-/

import Jolt.Oracle

open Jolt

/-- Print usage information. -/
def printUsage : IO Unit := do
  IO.println "Jolt Oracle CLI"
  IO.println ""
  IO.println "Usage: oracle <command> [args]"
  IO.println ""
  IO.println "Commands:"
  IO.println "  digest <state.json>       Compute state digest"
  IO.println "  verify <chain.json>       Verify continuation chain"
  IO.println "  test <vectors.json>       Run conformance test vectors"
  IO.println "  version                   Show version"
  IO.println ""

/-- Print version. -/
def printVersion : IO Unit := do
  IO.println "Jolt Oracle v0.1.0"
  IO.println "Lean 4 Executable Specification"

/-- Main entry point. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["version"] =>
    printVersion
    return 0
  | ["help"] | ["-h"] | ["--help"] =>
    printUsage
    return 0
  | ["digest", _path] =>
    IO.println "TODO: Implement digest command"
    return 0
  | ["verify", _path] =>
    IO.println "TODO: Implement verify command"
    return 0
  | ["test", _path] =>
    IO.println "TODO: Implement test command"
    return 0
  | [] =>
    printUsage
    return 0
  | _ =>
    IO.println "Unknown command"
    printUsage
    return 1
