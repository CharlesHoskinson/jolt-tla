import Jolt.Oracle
import CLI.Commands.Digest
import CLI.Commands.Verify
import CLI.Commands.VerifyVectors
import CLI.Commands.Generate
import CLI.Commands.Status
import CLI.Commands.Explain
import CLI.Commands.Diff
import CLI.Commands.Watch
import CLI.Commands.ExportMetadata
import CLI.Commands.GenerateCorpus
import CLI.REPL.Loop
import CLI.REPL.Eval

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
  IO.println "  watch [options]               Live refresh dashboard"
  IO.println "    --interval=N                Refresh interval in seconds (default: 2)"
  IO.println "    --count=N                   Number of iterations (default: 30)"
  IO.println "    --quiet, -q                 Suppress startup message"
  IO.println "  export-metadata               Export metadata JSON for Rust codegen"
  IO.println "  generate-corpus               Generate conformance test corpus"
  IO.println "  version                       Show version"
  IO.println ""
  IO.println "REPL Batch Mode:"
  IO.println "  repl --batch <file>           Run script non-interactively"
  IO.println "    --strict                    Stop on first error (default)"
  IO.println "    --continue                  Continue after errors"
  IO.println "    --quiet, -q                 Suppress command echo"
  IO.println ""
  IO.println "Options:"
  IO.println "  --format=pretty|plain|json    Output format (default: plain)"
  IO.println "  --help, -h                    Show this help"
  IO.println ""

/-- Print version. -/
def printVersion : IO Unit := do
  IO.println "Jolt Oracle v0.1.0"
  IO.println "Lean 4 Executable Specification"

/-- Batch mode options. -/
structure BatchOpts where
  scriptPath : String
  strict : Bool := true
  quiet : Bool := false
  deriving Repr

/-- Parse batch mode arguments.
    Returns None if --batch or -b not found or file path missing. -/
def parseBatchArgs (args : List String) : Option BatchOpts := do
  let mut foundBatch := false
  let mut scriptPath : Option String := none
  let mut strict := true
  let mut quiet := false

  let mut i := 0
  while i < args.length do
    match args[i]? with
    | some "--batch" | some "-b" =>
      foundBatch := true
      scriptPath := args[i + 1]?
      i := i + 2
    | some "--strict" =>
      strict := true
      i := i + 1
    | some "--continue" =>
      strict := false
      i := i + 1
    | some "--quiet" | some "-q" =>
      quiet := true
      i := i + 1
    | _ =>
      i := i + 1

  if foundBatch then
    scriptPath.map fun p => { scriptPath := p, strict, quiet }
  else
    none

/-- Run in batch mode - execute a script file with no interactivity. -/
def batchMain (opts : BatchOpts) : IO UInt32 := do
  -- Initialize state with batch settings (no banner, no color)
  let state : ReplState := {
    config := {
      banner := .never
      color := .never
      pretty := false
    }
  }

  -- Use evalSource with appropriate flags
  let continueOnError := !opts.strict
  let echo := !opts.quiet

  let (_, output) ← evalSource opts.scriptPath continueOnError echo state

  -- Output any stdout content
  if !output.out.isEmpty then
    IO.print output.out

  -- Output any stderr content (unless quiet and no errors)
  if !output.err.isEmpty && (!opts.quiet || output.code != .success) then
    IO.eprint output.err

  return output.code.toUInt32

/-- Main entry point. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["export-metadata"] =>
    exportMetadataMain []
  | ["generate-corpus"] =>
    generateCorpusMain []
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
    -- Check for batch mode
    if rest.any (fun x => x == "--batch" || x == "-b") then
      match parseBatchArgs rest with
      | some opts => batchMain opts
      | none =>
        IO.println "Usage: oracle repl --batch <file> [--strict|--continue] [--quiet]"
        return 1
    else
      replMain rest
  | [] =>
    -- No args: enter REPL (interactive mode)
    replMain []
  | _ =>
    IO.println "Unknown command"
    printUsage
    return 1

