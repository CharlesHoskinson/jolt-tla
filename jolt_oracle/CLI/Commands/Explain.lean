import Jolt.Errors
import CLI.Report.Types
import CLI.Terminal.Doc
import CLI.Terminal.RenderPlain
import CLI.Format.Json

/-!
# Explain Command

Provide human-readable remediation guidance for error codes.

## Usage
```
oracle explain <error_code>
oracle explain E501
oracle explain E501_DigestMismatch
```

## Output
Shows:
- Error code and name
- Description of what went wrong
- Possible causes
- Remediation steps
-/

namespace CLI.Commands

open Jolt
open CLI.Report
open CLI.Terminal
open CLI.Format

/-- Detailed error explanation. -/
structure ErrorExplanation where
  code : String
  name : String
  description : String
  causes : List String
  remediation : List String
  deriving Repr

/-- Get explanation for an error code. -/
def getExplanation (code : String) : Option ErrorExplanation :=
  -- Normalize: strip prefix if present, match on number
  let normalized := code.replace "E" "" |>.takeWhile (·.isDigit)
  match normalized with
  | "101" => some {
      code := "E101"
      name := "DuplicateKey"
      description := "JSON object contains duplicate keys"
      causes := [
        "The input JSON has the same key appearing multiple times in an object",
        "This violates RFC 8259 strict mode requirements"
      ]
      remediation := [
        "Remove duplicate keys from the JSON object",
        "Ensure each key appears exactly once",
        "Use a JSON validator to check for duplicates"
      ]
    }
  | "103" => some {
      code := "E103"
      name := "InvalidHex"
      description := "Invalid hexadecimal string format"
      causes := [
        "Hex string missing '0x' prefix",
        "Contains non-hex characters (must be 0-9, a-f lowercase)",
        "Uppercase hex letters used (must be lowercase)"
      ]
      remediation := [
        "Ensure hex strings start with '0x'",
        "Use only lowercase letters a-f",
        "Check for typos in hex digits"
      ]
    }
  | "104" => some {
      code := "E104"
      name := "WrongLength"
      description := "Value has incorrect length"
      causes := [
        "Bytes32 must be exactly 66 characters (0x + 64 hex)",
        "Register array must have exactly 32 elements",
        "Field element string has wrong number of digits"
      ]
      remediation := [
        "For Bytes32: ensure 64 hex characters after '0x'",
        "For registers: provide exactly 32 values",
        "Check that no values were accidentally omitted"
      ]
    }
  | "106" => some {
      code := "E106"
      name := "UnexpectedType"
      description := "JSON value has unexpected type"
      causes := [
        "Expected string but got number (or vice versa)",
        "Expected array but got object",
        "Expected object but got primitive"
      ]
      remediation := [
        "Check the schema for expected types",
        "Strings must be quoted",
        "Arrays use [], objects use {}"
      ]
    }
  | "107" => some {
      code := "E107"
      name := "FloatNotAllowed"
      description := "Floating-point numbers are not allowed"
      causes := [
        "JSON number contains a decimal point",
        "Attempting to use fractional values"
      ]
      remediation := [
        "Use only integer values",
        "Remove decimal points from numbers",
        "For Fr values, use decimal string representation"
      ]
    }
  | "108" => some {
      code := "E108"
      name := "ExponentNotAllowed"
      description := "Scientific notation is not allowed"
      causes := [
        "JSON number uses 'e' or 'E' notation",
        "Large numbers written in scientific form"
      ]
      remediation := [
        "Write numbers in full decimal form",
        "For large values, use string representation",
        "Example: use \"123456789\" not 1.23e8"
      ]
    }
  | "109" => some {
      code := "E109"
      name := "IntegerOutOfRange"
      description := "Integer exceeds safe JSON range"
      causes := [
        "Value exceeds ±(2^53 - 1)",
        "Large field elements encoded as integers"
      ]
      remediation := [
        "Use string representation for large numbers",
        "Fr values should be decimal strings",
        "Example: \"12345678901234567890\" not 12345678901234567890"
      ]
    }
  | "115" => some {
      code := "E115"
      name := "NonAsciiString"
      description := "String contains non-ASCII characters"
      causes := [
        "Unicode characters in keys or values",
        "Emoji or special characters",
        "Non-English text"
      ]
      remediation := [
        "Use only ASCII characters (0x00-0x7F)",
        "Escape non-ASCII as \\uXXXX if needed",
        "Check for hidden Unicode characters"
      ]
    }
  | "202" => some {
      code := "E202"
      name := "MissingRequiredKey"
      description := "Required JSON field is missing"
      causes := [
        "Mandatory field not present in object",
        "Typo in field name",
        "Using wrong schema version"
      ]
      remediation := [
        "Check the schema for required fields",
        "Verify field name spelling",
        "Common required: program_hash, state, pc, regs"
      ]
    }
  | "300" => some {
      code := "E300"
      name := "NonCanonicalFr"
      description := "Field element is not in canonical form"
      causes := [
        "Leading zeros in decimal representation",
        "Value exceeds field modulus",
        "Hex format used instead of decimal"
      ]
      remediation := [
        "Use decimal string without leading zeros",
        "Ensure value < field modulus",
        "\"0\" is valid, \"00\" is not"
      ]
    }
  | "402" => some {
      code := "E402"
      name := "OutOfRange"
      description := "Value is outside valid range"
      causes := [
        "Negative value where unsigned expected",
        "Value exceeds maximum for type",
        "Index out of bounds"
      ]
      remediation := [
        "Check valid ranges for each field",
        "pc, step_counter: 0 to 2^64-1",
        "halted: 0 or 1",
        "exit_code: 0 to 2^64-1"
      ]
    }
  | "500" => some {
      code := "E500"
      name := "ChainBreak"
      description := "Continuation chain has a break"
      causes := [
        "End state of chunk N doesn't match start state of chunk N+1",
        "Chunks are out of order",
        "Missing chunk in sequence"
      ]
      remediation := [
        "Verify chunk ordering by index",
        "Check that end_state[i] == start_state[i+1]",
        "Ensure no chunks are missing"
      ]
    }
  | "501" => some {
      code := "E501"
      name := "DigestMismatch"
      description := "Computed digest doesn't match claimed digest"
      causes := [
        "State was modified after digest computation",
        "Wrong program_hash used",
        "Digest computed with different parameters"
      ]
      remediation := [
        "Recompute digest with oracle digest command",
        "Verify program_hash is correct",
        "Check all state fields match exactly"
      ]
    }
  | "900" => some {
      code := "E900"
      name := "FileNotFound"
      description := "Input file could not be read"
      causes := [
        "File does not exist",
        "Path is incorrect",
        "Permission denied"
      ]
      remediation := [
        "Check file path is correct",
        "Verify file exists",
        "Check read permissions"
      ]
    }
  | _ => none

/-- Run the explain command.

Returns (ExitCode, output string). -/
def runExplain (errorCode : String) (format : OutputFormat := .pretty)
    (caps : Caps := Caps.plain) : IO (ExitCode × String) := do
  match getExplanation errorCode with
  | some explanation =>
    let output := match format with
      | .json | .ndjson =>
        let causesJson := "[" ++ String.intercalate ", " (explanation.causes.map jsonString) ++ "]"
        let remediationJson := "[" ++ String.intercalate ", " (explanation.remediation.map jsonString) ++ "]"
        jsonObject [
          ("code", jsonString explanation.code),
          ("name", jsonString explanation.name),
          ("description", jsonString explanation.description),
          ("causes", causesJson),
          ("remediation", remediationJson)
        ] ++ "\n"
      | .pretty | .plain =>
        let icons := selectIcons caps
        let doc := buildExplainDoc explanation icons
        renderPlain doc
    pure (.success, output)
  | none =>
    let output := match format with
      | .json | .ndjson =>
        jsonObject [
          ("status", jsonString "ERROR"),
          ("error", jsonString "UnknownErrorCode"),
          ("message", jsonString s!"Unknown error code: {errorCode}")
        ] ++ "\n"
      | .pretty | .plain =>
        s!"Unknown error code: {errorCode}\n\nUse 'oracle explain E<number>' for known codes.\nExample: oracle explain E501\n"
    pure (.invalid, output)

where
  buildExplainDoc (exp : ErrorExplanation) (_icons : IconSet) : Doc :=
    let causeDocs := exp.causes.map fun c => Doc.plain s!"  - {c}"
    let remDocs := exp.remediation.map fun r => Doc.plain s!"  - {r}"
    Doc.vcat ([
      Doc.headerBar "Jolt Oracle" (some "explain"),
      Doc.line,
      Doc.keyValue [
        Doc.kvStr "Code" exp.code,
        Doc.kvStr "Name" exp.name
      ],
      Doc.line,
      Doc.plain "Description:",
      Doc.plain s!"  {exp.description}",
      Doc.line,
      Doc.plain "Possible Causes:"
    ] ++ causeDocs ++ [
      Doc.line,
      Doc.plain "Remediation:"
    ] ++ remDocs ++ [
      Doc.line
    ])

/-- Main entry point for explain command. -/
def explainMain (args : List String) : IO UInt32 := do
  match args with
  | [code] =>
    let (exitCode, output) ← runExplain code .plain Caps.plain
    IO.print output
    return exitCode.toUInt32
  | _ =>
    IO.println "Usage: oracle explain <error_code>"
    IO.println ""
    IO.println "Examples:"
    IO.println "  oracle explain E501"
    IO.println "  oracle explain E501_DigestMismatch"
    IO.println "  oracle explain 501"
    return 4

end CLI.Commands
