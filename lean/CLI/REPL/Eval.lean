import CLI.REPL.Parser
import CLI.Commands.Digest
import CLI.Commands.Verify
import CLI.Commands.VerifyVectors
import CLI.Commands.Generate
import CLI.Commands.Status
import CLI.Commands.Explain
import CLI.Commands.Diff
import CLI.Commands.Watch

/-!
# REPL Command Evaluation

Execute parsed commands and return results.

## Main Definitions
* `evalCmd` - Evaluate a single command
* `evalLine` - Evaluate a full line (with pipes/redirects)
-/

namespace CLI.REPL

open CLI.Commands
open CLI.Report

/-- Version string for the REPL. -/
def replVersion : String := "Jolt Oracle REPL v0.1.0"

/-- Convert ReplConfig to Caps. -/
def ReplConfig.toCaps (c : ReplConfig) : CLI.Terminal.Caps :=
  { color := c.color != .never, unicode := c.color != .never }

/-- ToString instance for ColorMode. -/
instance : ToString CLI.Terminal.ColorMode where
  toString m := match m with
    | .auto => "auto"
    | .always => "always"
    | .never => "never"

/-- ToString instance for OutputFormat. -/
instance : ToString CLI.Terminal.OutputFormat where
  toString f := match f with
    | .plain => "plain"
    | .pretty => "pretty"
    | .json => "json"
    | .ndjson => "ndjson"

/-- ToString instance for VarValue. -/
instance : ToString VarValue where
  toString v := match v with
    | .str s => s
    | .digest d => s!"{d}"
    | .bytes32 _ => "<bytes32>"
    | .state _ => "<vmstate>"
    | .exitCode c => s!"{c}"
    | .json j => j
    | .none => "(none)"

/-- Evaluate an oracle command by dispatching to existing run* functions. -/
def evalOracleCmd (name : String) (args : Array String)
    (state : ReplState) : IO (ReplState × ReplOutput) := do
  let argList := args.toList

  -- Dispatch to appropriate command
  let (exitCode, output) ← match name with
    | "digest" =>
      match argList with
      | [path] =>
        let (code, out) ← runDigest path .plain state.config.toCaps
        pure (code, out)
      | _ =>
        pure (.invalid, "Usage: digest <state.json>\n")

    | "verify" =>
      match argList with
      | ["chain", path] =>
        let (code, out) ← runVerifyChain path .plain state.config.toCaps
        pure (code, out)
      | [path] =>
        -- Backwards compatibility
        let (code, out) ← runVerifyChain path .plain state.config.toCaps
        pure (code, out)
      | ["vectors", path] =>
        let code ← verifyVectorsMain [path]
        pure (ExitCode.fromUInt32 code, "")
      | _ =>
        pure (.invalid, "Usage: verify chain <file> | verify vectors <file>\n")

    | "generate" =>
      match argList with
      | [vectorType, inputPath] =>
        let code ← generateMain [vectorType, inputPath]
        pure (ExitCode.fromUInt32 code, "")
      | [vectorType, inputPath, "-o", outputPath] =>
        let code ← generateMain [vectorType, inputPath, "-o", outputPath]
        pure (ExitCode.fromUInt32 code, "")
      | _ =>
        pure (.invalid, "Usage: generate <type> <input.json> [-o output.json]\n")

    | "status" =>
      let (code, out) ← runStatus .plain state.config.toCaps
      pure (code, out)

    | "diff" =>
      match argList with
      | [expected, actual] =>
        let (code, out) ← runDiff expected actual .plain state.config.toCaps
        pure (code, out)
      | _ =>
        pure (.invalid, "Usage: diff <expected.json> <actual.json>\n")

    | "explain" =>
      match argList with
      | [code] =>
        let (exitCode, out) ← runExplain code .plain state.config.toCaps
        pure (exitCode, out)
      | _ =>
        pure (.invalid, "Usage: explain <error_code>\n")

    | "watch" =>
      -- Watch is special - runs in a loop
      -- For REPL, just do one iteration
      let out ← runWatchIteration .plain state.config.toCaps 0
      pure (.success, out)

    | _ =>
      pure (.invalid, s!"Unknown command: {name}\nType ':help' for available commands.\n")

  -- Update state with result
  let newState := { state with
    lastExitCode := exitCode
    lastResult := .text output
  }

  pure (newState, { out := output, err := "", code := exitCode, pipeValue := .text output })

where
  /-- Convert UInt32 to ExitCode. -/
  ExitCode.fromUInt32 (n : UInt32) : ExitCode :=
    match n with
    | 0 => .success
    | 2 => .degraded
    | 3 => .unhealthy
    | 4 => .invalid
    | _ => .ioError

/-- Evaluate a builtin command. -/
def evalBuiltin (cmd : ReplCmd) (state : ReplState) : IO (ReplState × ReplOutput) := do
  match cmd with
  | .help topic =>
    let out := formatHelp topic
    pure (state, ReplOutput.stdout out)

  | .quit =>
    -- Return special exit result - handled by caller
    pure (state, { out := "", err := "", code := .success, pipeValue := .text "" })

  | .clear =>
    -- Just return clear screen sequence
    pure (state, ReplOutput.stdout clearScreen)

  | .history filter =>
    let out := formatHistory state.history filter
    pure (state, ReplOutput.stdout out)

  | .env =>
    let out := formatEnv state
    pure (state, ReplOutput.stdout out)

  | .set key value =>
    let isSecret := key.startsWith "secret."
    let state' := state.setVar key (.str value) isSecret
    let display := if isSecret then "[REDACTED]" else value
    pure (state', ReplOutput.stdout s!"Set {key} = {display}\n")

  | .unset name =>
    let state' := state.unsetVar name
    pure (state', ReplOutput.stdout s!"Unset {name}\n")

  | .alias_ name expansion =>
    let state' := state.setAlias name expansion
    pure (state', ReplOutput.stdout s!"Alias '{name}' defined\n")

  | .unalias name =>
    let state' := state.unsetAlias name
    pure (state', ReplOutput.stdout s!"Alias '{name}' removed\n")

  | .load path varName =>
    -- Load file contents into a variable
    try
      let content ← IO.FS.readFile path
      let name := varName.getD (extractFileName path)
      let state' := state.setVar name (.str content)
      let state'' := { state' with contextFile := some path }
      pure (state'', ReplOutput.stdout s!"Loaded {path} as ${name}\n")
    catch _ =>
      pure (state, ReplOutput.stderr s!"Error: Cannot read file: {path}\n")

  | .save varName path =>
    match state.getVar varName with
    | some v =>
      let content := match v.value with
        | .str s => s
        | .json j => j
        | _ => s!"{v.value}"
      try
        IO.FS.writeFile path content
        pure (state, ReplOutput.stdout s!"Saved ${varName} to {path}\n")
      catch _ =>
        pure (state, ReplOutput.stderr s!"Error: Cannot write file: {path}\n")
    | none =>
      pure (state, ReplOutput.stderr s!"Error: Variable not found: ${varName}\n")

  | .source _path _continueOnError =>
    -- TODO: Implement script sourcing
    pure (state, ReplOutput.stderr "Script sourcing not yet implemented\n")

  | .show_ varName full =>
    let out := formatShow state varName full
    pure (state, ReplOutput.stdout out)

  | .type_ expr =>
    let out := formatType state expr
    pure (state, ReplOutput.stdout out)

  | .push =>
    if state.sessionStackDepth >= maxSessionStackDepth then
      pure (state, ReplOutput.stderr "Error: Session stack full (max 10)\n")
    else
      let state' := { state with sessionStackDepth := state.sessionStackDepth + 1 }
      pure (state', ReplOutput.stdout s!"Session marked (depth: {state'.sessionStackDepth})\n")

  | .pop =>
    if state.sessionStackDepth == 0 then
      pure (state, ReplOutput.stderr "Error: Session stack empty\n")
    else
      -- Note: For a full implementation, we'd need to store snapshots
      -- For now, just decrement depth as a simplified version
      let state' := { state with sessionStackDepth := state.sessionStackDepth - 1 }
      pure (state', ReplOutput.stdout "Session pop (note: full state restoration not implemented)\n")

  | .reset =>
    let state' := { state with
      variables := #[]
      aliases := #[]
      contextFile := none
      lastResult := .text ""
      lastExitCode := .success
    }
    pure (state', ReplOutput.stdout "Session reset\n")

  | .config subCmd =>
    let out := match subCmd with
      | "path" => s!"Config path: {configPath}\n"
      | "show" => formatConfig state.config
      | _ => s!"Unknown config command: {subCmd}\n"
    pure (state, ReplOutput.stdout out)

  | .redact enable =>
    let newMode := match enable with
      | some b => b
      | none => !state.redactMode
    let state' := { state with redactMode := newMode }
    let status := if newMode then "on" else "off"
    pure (state', ReplOutput.stdout s!"Redact mode: {status}\n")

  | .examples cmdName =>
    let out := formatExamples cmdName
    pure (state, ReplOutput.stdout out)

  | .cheatsheet =>
    let out := formatCheatsheet
    pure (state, ReplOutput.stdout out)

  | .version =>
    pure (state, ReplOutput.stdout s!"{replVersion}\n")

  | _ =>
    pure (state, ReplOutput.stderr "Internal error: unexpected command\n")

where
  extractFileName (path : String) : String :=
    -- Simple extraction: take last component, remove extension
    let parts := path.splitOn "/"
    let parts := if parts.length == 1 then path.splitOn "\\" else parts
    let name := parts.getLast!
    -- Find first dot by splitting
    match name.splitOn "." with
    | [] => name
    | [n] => n
    | h :: _ => h

  configPath : String :=
    -- Platform-specific config path
    if System.Platform.isWindows then
      "%APPDATA%\\jolt\\repl.json"
    else
      "~/.config/jolt/repl.json"

  formatHelp (topic : Option String) : String :=
    match topic with
    | none => helpText
    | some t => helpForTopic t

  helpText : String :=
"Jolt Oracle REPL - Commands

ORACLE
  digest <file>           Compute state digest
  verify chain <file>     Verify continuation chain
  verify vectors <file>   Run conformance test vectors
  generate <type> <file>  Generate test vector
  status                  Show oracle status
  diff <a> <b>            Compare state files
  explain <code>          Explain error code

VARIABLES
  :load <file> [as <var>] Load file into variable
  :save <var> <file>      Save variable to file
  :env                    Show all variables
  :show <var> [--full]    Display variable value
  :type <expr>            Show expression type
  :set <key> <value>      Set config option
  :unset <var>            Remove variable

SCRIPTING
  :alias <n> = <cmd>      Define command alias
  :unalias <name>         Remove alias
  :source <file>          Run script file
  :history [filter]       Show command history

SESSION
  :push                   Save session to stack
  :pop                    Restore from stack
  :reset                  Clear all variables/aliases
  :config save|load|path  Manage config file
  :redact [on|off]        Toggle secret redaction

DISPLAY
  :clear                  Clear screen
  :help [topic]           Show this help
  :examples <cmd>         Show command examples
  :cheatsheet             Quick reference card
  :version                Show version info
  :quit                   Exit REPL

Special variables: $_ (last output), $? (exit code)
Quoting: \"...\" expands $vars, '...' is literal
"

  helpForTopic (topic : String) : String :=
    match topic with
    | "digest" => "digest <file>\n  Compute Poseidon state digest from JSON file.\n"
    | "verify" => "verify chain <file>\n  Verify a continuation chain.\nverify vectors <file>\n  Run conformance test vectors.\n"
    | "set" => ":set <key> <value>\n  Set a config option or variable.\n  Use :set secret.<name> for secrets (redacted in output).\n"
    | "alias" => ":alias <name> = <expansion>\n  Define a command alias.\n  Example: :alias d = digest\n"
    | "load" => ":load <file> [as <var>]\n  Load file contents into a variable.\n  Example: :load state.json as s1\n"
    | _ => s!"No help available for '{topic}'\n"

  formatHistory (history : Array String) (filter : Option String) : String :=
    let containsSubstr (haystack needle : String) : Bool :=
      -- Simple substring check using splitOn
      if needle.isEmpty then true
      else (haystack.splitOn needle).length > 1
    let filtered := match filter with
      | some f => history.filter (fun s => containsSubstr s f)
      | none => history
    if filtered.isEmpty then
      "(no history)\n"
    else
      let lines := filtered.mapIdx fun i line => s!"  {i + 1}  {line}"
      String.intercalate "\n" lines.toList ++ "\n"

  formatEnv (state : ReplState) : String :=
    if state.variables.isEmpty then
      "(no variables)\n"
    else
      let header := "NAME          TYPE        VALUE\n"
      let lines := state.variables.map fun v =>
        let typeName := varTypeName v.value
        let value := formatValue state v
        let name := v.name.take 12
        let padding1 := String.ofList (List.replicate (14 - name.length) ' ')
        let padding2 := String.ofList (List.replicate (12 - typeName.length) ' ')
        s!"{name}{padding1}{typeName}{padding2}{value}"
      header ++ String.intercalate "\n" lines.toList ++ "\n"

  formatShow (state : ReplState) (varName : String) (full : Bool) : String :=
    -- Handle special variables
    if varName == "_" || varName == "$_" then
      s!"$_ : {state.lastResult.toString}\n"
    else if varName == "?" || varName == "$?" then
      s!"$? : {state.lastExitCode.toUInt32}\n"
    else
      let name := if varName.startsWith "$" then varName.drop 1 else varName
      match state.getVar name with
      | some v =>
        let typeName := varTypeName v.value
        let value := if full then
          match v.value with
          | .str s => s
          | .json j => j
          | _ => formatValue state v
        else
          formatValue state v
        s!"${name} : {typeName}\n  {value}\n"
      | none =>
        s!"Variable not found: ${name}\n"

  formatType (state : ReplState) (expr : String) : String :=
    let name := if expr.startsWith "$" then expr.drop 1 else expr
    if name == "_" then
      s!"$_ : PipeValue\n"
    else if name == "?" then
      s!"$? : ExitCode\n"
    else
      match state.getVar name with
      | some v => s!"${name} : {varTypeName v.value}\n"
      | none => s!"Unknown: {expr}\n"

  formatConfig (config : ReplConfig) : String :=
    s!"Configuration:
  color: {config.color}
  pager: {config.pager}
  out_format: {config.outFormat}
  max_preview_bytes: {config.maxPreviewBytes}
  timeout: {config.timeout}s
  pretty: {config.pretty}
"

  formatExamples (cmdName : String) : String :=
    match cmdName with
    | "digest" =>
      "Examples for 'digest':
  digest state.json
  digest $s1
  digest { \"program_hash\": \"0x...\", \"state\": {...} }
"
    | "verify" =>
      "Examples for 'verify':
  verify chain continuation.json
  verify vectors test_vectors.json
"
    | "alias" =>
      "Examples for ':alias':
  :alias d = digest
  :alias vc = verify chain
"
    | _ => s!"No examples available for '{cmdName}'\n"

  formatCheatsheet : String :=
"QUICK REFERENCE

Commands:     digest, verify, status, diff, explain
Variables:    $_, $?, $varname, ${varname}
Quoting:      \"...\" (expand vars), '...' (literal)
Piping:       cmd1 | cmd2
Redirect:     cmd > file, cmd >> file
Builtins:     :help, :env, :set, :load, :save, :quit

Session:      :push, :pop, :reset
Secrets:      :set secret.key \"value\", :redact on

Examples:
  digest state.json
  :load state.json as s1
  digest $s1 | :show
  :alias d = digest
"

/-- Evaluate a command (dispatch to builtin or oracle). -/
def evalCmd (cmd : ReplCmd) (state : ReplState) : IO EvalResult := do
  match cmd with
  | .quit =>
    return .exit 0

  | .noop =>
    return .continue state ReplOutput.empty

  | .oracle name args =>
    let args' := expandVariables state args
    let (state', output) ← evalOracleCmd name args' state
    return .continue state' output

  | .pipe left right =>
    -- Evaluate left, capture output, pass to right
    let result ← evalCmd left state
    match result with
    | .exit code => return .exit code
    | .continue state' output =>
      -- Set $_ to the pipe value
      let state'' := { state' with lastResult := output.pipeValue }
      evalCmd right state''

  | .redirect inner target =>
    let result ← evalCmd inner state
    match result with
    | .exit code => return .exit code
    | .continue state' output =>
      match target with
      | .stdout =>
        return .continue state' output
      | .file path =>
        try
          IO.FS.writeFile path output.out
          let msg := s!"(output written to {path})\n"
          return .continue state' { output with out := "", err := msg }
        catch _ =>
          return .continue state' (ReplOutput.stderr s!"Error: Cannot write to {path}\n")
      | .append path =>
        try
          let existing ← IO.FS.readFile path <|> pure ""
          IO.FS.writeFile path (existing ++ output.out)
          let msg := s!"(output appended to {path})\n"
          return .continue state' { output with out := "", err := msg }
        catch _ =>
          return .continue state' (ReplOutput.stderr s!"Error: Cannot append to {path}\n")
      | .variable name =>
        let state'' := state'.setVar name (.str output.out)
        return .continue state'' { output with out := "" }

  | .varRef name =>
    -- Just output the variable value
    match state.getVar name with
    | some v =>
      let out := formatValue state v
      return .continue state (ReplOutput.stdout out)
    | none =>
      return .continue state (ReplOutput.stderr s!"Variable not found: ${name}\n")

  | _ =>
    -- Builtin commands
    let (state', output) ← evalBuiltin cmd state
    return .continue state' output

/-- Evaluate a line of input (with parsing). -/
def evalLine (input : String) (state : ReplState) : IO EvalResult := do
  -- Parse the line
  match parse input with
  | .error e =>
    let errMsg := renderErrorPlain e input
    return .continue state (ReplOutput.stderr errMsg)
  | .ok cmd =>
    -- Expand aliases
    match expandAliases state cmd with
    | .error e =>
      let errMsg := e.message ++ "\n"
      return .continue state (ReplOutput.stderr errMsg)
    | .ok expandedCmd =>
      evalCmd expandedCmd state

end CLI.REPL
