import Jolt.Oracle
import CLI.Report.Types
import CLI.Terminal.Doc
import CLI.Terminal.RenderPlain
import CLI.Format.Json

/-!
# Status Command

Display a one-screen dashboard showing oracle status and configuration.

## Usage
```
oracle status
```

## Output
Shows:
- Oracle version and configuration
- Poseidon parameters summary
- Field modulus info
- Health status
-/

namespace CLI.Commands

open Jolt
open CLI.Report
open CLI.Terminal
open CLI.Format

/-- Oracle status information. -/
structure OracleStatus where
  version : String
  poseidonT : Nat
  poseidonRounds : Nat
  frModulusBits : Nat
  healthy : Bool
  deriving Repr

/-- Collect oracle status. -/
def collectStatus : OracleStatus :=
  let cfg := Oracle.init
  OracleStatus.mk
    "0.1.0"
    cfg.poseidon.width
    (cfg.poseidon.fullRounds + cfg.poseidon.partialRounds)
    255  -- BLS12-381 scalar field
    true

/-- Run the status command.

Returns (ExitCode, output string). -/
def runStatus (format : OutputFormat := .pretty)
    (caps : Caps := Caps.plain) : IO (ExitCode × String) := do
  let status := collectStatus

  let output := match format with
    | .json | .ndjson =>
      jsonObject [
        ("status", jsonString (if status.healthy then "HEALTHY" else "UNHEALTHY")),
        ("version", jsonString status.version),
        ("poseidon_t", jsonNat status.poseidonT),
        ("poseidon_rounds", jsonNat status.poseidonRounds),
        ("fr_modulus_bits", jsonNat status.frModulusBits)
      ] ++ "\n"
    | .pretty | .plain =>
      let icons := selectIcons caps
      let doc := buildStatusDoc status icons
      renderPlain doc

  let exitCode := if status.healthy then ExitCode.success else ExitCode.unhealthy
  pure (exitCode, output)

where
  buildStatusDoc (status : OracleStatus) (icons : IconSet) : Doc :=
    Doc.vcat [
      Doc.headerBar "Jolt Oracle" (some "status"),
      Doc.line,
      Doc.keyValue [
        Doc.kvStr "Version" status.version,
        Doc.kvStr "Field" "BLS12-381 scalar (Fr)",
        Doc.kvStr "Modulus Bits" (toString status.frModulusBits)
      ],
      Doc.line,
      Doc.plain "Poseidon Configuration:",
      Doc.keyValue [
        Doc.kvStr "  State Width (t)" (toString status.poseidonT),
        Doc.kvStr "  Total Rounds" (toString status.poseidonRounds)
      ],
      Doc.line,
      Doc.status icons status.healthy
        (if status.healthy then "Oracle is healthy" else "Oracle has issues")
    ]

/-- Main entry point for status command. -/
def statusMain (_args : List String) : IO UInt32 := do
  let (code, output) ← runStatus .plain Caps.plain
  IO.print output
  return code.toUInt32

end CLI.Commands
