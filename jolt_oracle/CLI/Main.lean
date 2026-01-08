import Jolt.Oracle
import CLI.Commands.Digest
import CLI.Commands.Verify
import CLI.Commands.VerifyVectors
import CLI.Commands.Generate
import CLI.Commands.Status
import CLI.Commands.Explain
import CLI.Commands.Diff
import CLI.Commands.Watch
import CLI.REPL.Loop

/-!
# Jolt Oracle CLI

Command-line interface for the Jolt Oracle.

## Commands
- `digest <state.json>` - Compute state digest
- `verify <chain.json>` - Verify chain
- `test <vectors.json>` - Run test vectors
-/

open Jolt
open CLI.Commands
open CLI.REPL

/-- Print usage information. -/
def printUsage : IO Unit := do
  IO.println "Jolt Oracle CLI v0.1.0"
  IO.println ""
  IO.println "Usage: oracle [command] [args]"
  IO.println ""
  IO.println "Commands:"
  IO.println "  (no command)                  Enter interactive REPL"
  IO.println "  repl                          Enter interactive REPL"
  IO.println "  status                        Show oracle status dashboard"
  IO.println "  digest <state.json>           Compute state digest"
  IO.println "  verify chain <chain.json>     Verify continuation chain"
  IO.println "  verify vectors <vectors.json> Run conformance test vectors"
  IO.println "  generate <type> <input.json>  Generate test vector"
  IO.println "  diff <expected> <actual>      Compare two state files"
  IO.println "  explain <error_code>          Explain error and remediation"
  IO.println "  watch [--interval=N]          Live refresh dashboard"
  IO.println "  version                       Show version"
  IO.println ""
  IO.println "Options:"
  IO.println "  --format=pretty|plain|json    Output format (default: plain)"
  IO.println "  --help, -h                    Show this help"
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
  | ["digest", path] =>
    digestMain [path]
  | ["verify", "chain", path] =>
    verifyChainMain [path]
  | ["verify", path] =>
    -- For backwards compatibility, treat `verify <file>` as `verify chain <file>`
    verifyChainMain [path]
  | ["verify", "vectors", path] =>
    verifyVectorsMain [path]
  | ["generate", vectorType, inputPath] =>
    generateMain [vectorType, inputPath]
  | ["generate", vectorType, inputPath, "-o", outputPath] =>
    generateMain [vectorType, inputPath, "-o", outputPath]
  | ["status"] =>
    statusMain []
  | ["diff", expected, actual] =>
    diffMain [expected, actual]
  | ["explain", code] =>
    explainMain [code]
  | ["watch"] =>
    watchMain []
  | "watch" :: rest =>
    watchMain rest
  | ["repl"] =>
    replMain []
  | "repl" :: rest =>
    replMain rest
  | [] =>
    -- No args: enter REPL (interactive mode)
    replMain []
  | _ =>
    IO.println "Unknown command"
    printUsage
    return 1
