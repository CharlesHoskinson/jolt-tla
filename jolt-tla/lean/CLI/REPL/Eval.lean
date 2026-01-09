import CLI.REPL.Parser
import CLI.REPL.UI
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

/-- Version string for the REPL (full). -/
def replVersionString : String := "Jolt Oracle REPL v0.1.0"

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
      | [arg] =>
        -- Detect JSON content vs file path
        let trimmed := arg.trim
        if trimmed.startsWith "{" then
          let (code, out) ← runDigestFromContent trimmed .plain state.config.toCaps
          pure (code, out)
        else
          let (code, out) ← runDigest arg .plain state.config.toCaps
          pure (code, out)
      | _ =>
        pure (.invalid, "Usage: digest <state.json>\n")

    | "verify" =>
      match argList with
      | ["chain", arg] =>
        -- Detect JSON content vs file path
        let trimmed := arg.trim
        if trimmed.startsWith "{" then
          let (code, out) ← runVerifyChainFromContent trimmed .plain state.config.toCaps
          pure (code, out)
        else
          let (code, out) ← runVerifyChain arg .plain state.config.toCaps
          pure (code, out)
      | [arg] =>
        -- Backwards compatibility - also detect JSON content
        let trimmed := arg.trim
        if trimmed.startsWith "{" then
          let (code, out) ← runVerifyChainFromContent trimmed .plain state.config.toCaps
          pure (code, out)
        else
          let (code, out) ← runVerifyChain arg .plain state.config.toCaps
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
        -- Use runDiffMixed to support both file paths and JSON content (from variables)
        let (code, out) ← runDiffMixed expected actual .plain state.config.toCaps
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

/-- Get the configuration directory path.
    Unix:    ~/.jolt
    Windows: %APPDATA%/jolt (fallback: %USERPROFILE%/.jolt) -/
def getConfigDir : IO System.FilePath := do
  if System.Platform.isWindows then
    match ← IO.getEnv "APPDATA" with
    | some appdata => return appdata / "jolt"
    | none =>
      match ← IO.getEnv "USERPROFILE" with
      | some home => return home / ".jolt"
      | none => return ".jolt"
  else
    let home := (← IO.getEnv "HOME").getD "~"
    return home / ".jolt"

/-- Get the config file path. -/
def getConfigPath : IO System.FilePath := do
  let dir ← getConfigDir
  return dir / "repl.json"

/-- Convert ColorMode to string for JSON. -/
private def colorModeToString : CLI.Terminal.ColorMode → String
  | .auto => "auto"
  | .always => "always"
  | .never => "never"

/-- Parse ColorMode from string. -/
private def parseColorMode (s : String) : Option CLI.Terminal.ColorMode :=
  match s with
  | "auto" => some .auto
  | "always" => some .always
  | "never" => some .never
  | _ => none

/-- Convert OutputFormat to string for JSON. -/
private def outputFormatToString : CLI.Terminal.OutputFormat → String
  | .plain => "plain"
  | .pretty => "pretty"
  | .json => "json"
  | .ndjson => "ndjson"

/-- Parse OutputFormat from string. -/
private def parseOutputFormat (s : String) : Option CLI.Terminal.OutputFormat :=
  match s with
  | "plain" => some .plain
  | "pretty" => some .pretty
  | "json" => some .json
  | "ndjson" => some .ndjson
  | _ => none

/-- Build config JSON string. -/
private def configToJson (config : ReplConfig) (aliases : Array Alias) : String :=
  let aliasLines := aliases.map fun a =>
    s!"    \"{a.name}\": \"{a.expansion}\""
  let aliasStr := if aliases.isEmpty then "{}" else
    "{\n" ++ String.intercalate ",\n" aliasLines.toList ++ "\n  }"
  s!"\{
  \"version\": 1,
  \"banner\": \"{config.banner}\",
  \"color\": \"{colorModeToString config.color}\",
  \"pretty\": {config.pretty},
  \"outFormat\": \"{outputFormatToString config.outFormat}\",
  \"maxPreviewBytes\": {config.maxPreviewBytes},
  \"aliases\": {aliasStr}
}"

/-- Save configuration to file (atomic write). -/
def saveConfig (state : ReplState) : IO (ExitCode × String) := do
  let configPath ← getConfigPath
  let configDir ← getConfigDir
  let tmpPath := configPath.toString ++ ".tmp"

  try
    -- Ensure directory exists
    IO.FS.createDirAll configDir

    -- Build JSON
    let json := configToJson state.config state.aliases

    -- Atomic write: write to tmp, then rename
    IO.FS.writeFile tmpPath json

    -- On Windows: remove dest first if exists (rename can fail otherwise)
    if System.Platform.isWindows then
      try IO.FS.removeFile configPath catch _ => pure ()

    IO.FS.rename tmpPath configPath

    return (.success, s!"Config saved to {configPath}\n")
  catch e =>
    -- Clean up tmp file if it exists
    try IO.FS.removeFile tmpPath catch _ => pure ()
    return (.ioError, s!"Error saving config: {e}\n")

/-- Simple JSON value extraction (minimal parser for config). -/
private def extractJsonString (content : String) (key : String) : Option String := do
  let pattern := s!"\"{key}\": \""
  let parts := content.splitOn pattern
  if parts.length < 2 then none
  else
    let rest := parts[1]!
    let endIdx := rest.toList.findIdx (· == '"')
    some (rest.take endIdx)

/-- Extract JSON boolean. -/
private def extractJsonBool (content : String) (key : String) : Option Bool := do
  let pattern := s!"\"{key}\": "
  let parts := content.splitOn pattern
  if parts.length < 2 then none
  else
    let rest := parts[1]!
    if rest.startsWith "true" then some true
    else if rest.startsWith "false" then some false
    else none

/-- Extract JSON number. -/
private def extractJsonNat (content : String) (key : String) : Option Nat := do
  let pattern := s!"\"{key}\": "
  let parts := content.splitOn pattern
  if parts.length < 2 then none
  else
    let rest := parts[1]!
    let numStr := rest.takeWhile (fun c => c.isDigit)
    numStr.toNat?

/-- Extract aliases from JSON config. -/
private def extractAliases (content : String) : Array Alias := Id.run do
  -- Find "aliases": { ... }
  let parts := content.splitOn "\"aliases\": {"
  if parts.length < 2 then return #[]

  let rest := parts[1]!
  let endIdx := rest.toList.findIdx (· == '}')
  let aliasContent := rest.take endIdx

  -- Parse individual aliases
  let mut aliases : Array Alias := #[]
  let lines := aliasContent.splitOn "\n"
  for line in lines do
    let trimmed := line.trim
    if trimmed.isEmpty || trimmed == "," then continue
    -- Parse "name": "expansion"
    let keyParts := trimmed.splitOn "\": \""
    if keyParts.length >= 2 then
      let name := (keyParts[0]!.dropWhile (· != '"')).drop 1
      let expansion := keyParts[1]!.dropRightWhile (· != '"') |>.dropRight 1
      if !name.isEmpty && !expansion.isEmpty then
        aliases := aliases.push { name, expansion }
  aliases

/-- Load configuration from file. -/
def loadConfig (state : ReplState) : IO (ReplState × String) := do
  let configPath ← getConfigPath

  -- Check if file exists
  if !(← configPath.pathExists) then
    return (state, s!"No config file at {configPath}\n")

  try
    let content ← IO.FS.readFile configPath

    -- Check version
    let version := extractJsonNat content "version" |>.getD 0
    if version != 1 then
      return (state, s!"Warning: Unknown config version {version}, ignoring\n")

    -- Parse fields with fallbacks to current values
    let banner := extractJsonString content "banner"
      |>.bind (fun s => parseBannerMode (some s))
      |>.getD state.config.banner
    let color := extractJsonString content "color"
      |>.bind parseColorMode
      |>.getD state.config.color
    let pretty := extractJsonBool content "pretty"
      |>.getD state.config.pretty
    let outFormat := extractJsonString content "outFormat"
      |>.bind parseOutputFormat
      |>.getD state.config.outFormat
    let maxPreviewBytes := extractJsonNat content "maxPreviewBytes"
      |>.getD state.config.maxPreviewBytes

    let aliases := extractAliases content

    let newConfig : ReplConfig := {
      banner, color, pretty, outFormat, maxPreviewBytes,
      pager := state.config.pager,
      timeout := state.config.timeout
    }

    let newState := { state with
      config := newConfig
      aliases := if aliases.isEmpty then state.aliases else aliases
    }

    return (newState, s!"Config loaded from {configPath}\n")
  catch e =>
    return (state, s!"Error loading config: {e}\n")

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
    match subCmd with
    | "path" =>
      let path ← getConfigPath
      pure (state, ReplOutput.stdout s!"Config path: {path}\n")
    | "show" =>
      let out := formatConfig state.config
      pure (state, ReplOutput.stdout out)
    | "save" =>
      let (code, msg) ← saveConfig state
      if code == .success then
        pure (state, ReplOutput.stdout msg)
      else
        pure (state, ReplOutput.stderr msg)
    | "load" =>
      let (newState, msg) ← loadConfig state
      pure (newState, ReplOutput.stdout msg)
    | "reset" =>
      let defaultConfig : ReplConfig := {}
      let state' := { state with config := defaultConfig }
      pure (state', ReplOutput.stdout "Config reset to defaults (not saved)\n")
    | _ =>
      pure (state, ReplOutput.stderr s!"Unknown config command: {subCmd}\nUsage: :config [show|save|load|path|reset]\n")

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
    pure (state, ReplOutput.stdout s!"{replVersionString}\n")

  -- Beauty layer builtins (P0½)
  | .banner subCmd =>
    match subCmd with
    | "show" =>
      -- Replay the banner
      let caps : UiCaps := default  -- Will be updated when we have caps in state
      let theme := getTheme caps
      let out := renderBanner caps theme
      pure (state, ReplOutput.stdout out)
    | "on" =>
      let state' := { state with config := { state.config with banner := .always } }
      pure (state', ReplOutput.stdout "Banner mode: always\n")
    | "off" =>
      let state' := { state with config := { state.config with banner := .never } }
      pure (state', ReplOutput.stdout "Banner mode: never\n")
    | "auto" =>
      let state' := { state with config := { state.config with banner := .auto } }
      pure (state', ReplOutput.stdout "Banner mode: auto\n")
    | _ =>
      pure (state, ReplOutput.stderr s!"Unknown banner subcommand: {subCmd}\nUsage: :banner [show|on|off|auto]\n")

  | .theme =>
    let caps : UiCaps := default
    let colorStr := if caps.color then "enabled" else "disabled"
    let unicodeStr := if caps.unicode then "enabled" else "disabled"
    let interactiveStr := if caps.isInteractive then "yes" else "no"
    let out := s!"Terminal Capabilities:
  Color:       {colorStr}
  Unicode:     {unicodeStr}
  Interactive: {interactiveStr}
  Width:       {caps.termWidth}
  Height:      {caps.termHeight}
"
    pure (state, ReplOutput.stdout out)

  | .doctor =>
    -- Sanity check: TTY? Colors? Config path? History path?
    let stdinTty ← IO.FS.Stream.isTty (← IO.getStdin)
    let stderrTty ← IO.FS.Stream.isTty (← IO.getStderr)
    let noColor := (← IO.getEnv "NO_COLOR").isSome
    let term := (← IO.getEnv "TERM").getD "(not set)"
    let cfgPath ← getConfigPath

    let checkMark := "+"
    let crossMark := "!"
    let stdin := if stdinTty then s!"{checkMark} stdin is TTY" else s!"{crossMark} stdin is not TTY"
    let stderr := if stderrTty then s!"{checkMark} stderr is TTY" else s!"{crossMark} stderr is not TTY"
    let noColorLine := if noColor then s!"{crossMark} NO_COLOR is set" else s!"{checkMark} NO_COLOR not set"
    let termLine := s!"  TERM={term}"

    let out := s!"Doctor Report:
  {stdin}
  {stderr}
  {noColorLine}
{termLine}
  Config path: {cfgPath}
  Banner mode: {state.config.banner}
  Color mode:  {state.config.color}
  Variables:   {state.variables.size}
  Aliases:     {state.aliases.size}
  History:     {state.history.size} entries
"
    pure (state, ReplOutput.stdout out)

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
  :source <file> [opts]   Run script file
     --continue           Continue after errors
     --echo               Print commands as executed
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
  :banner [show|on|off|auto]  Manage startup banner
  :theme                  Show terminal capabilities
  :doctor                 System diagnostics
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
    | "source" => ":source <file> [--continue] [--echo]\n  Execute commands from a script file.\n  Uses full REPL parsing (multi-line JSON, aliases, variables).\n  --continue  Continue execution after errors\n  --echo      Print each command to stderr before execution\n  Example: :source setup.oracle --echo\n"
    | "banner" => ":banner [show|on|off|auto]\n  Manage the startup banner.\n  show  - Display the banner now\n  on    - Always show banner on startup\n  off   - Never show banner on startup\n  auto  - Show banner when stderr is a TTY (default)\n"
    | "theme" => ":theme\n  Display terminal capabilities:\n  - Color support\n  - Unicode support\n  - Interactive mode\n  - Terminal dimensions\n"
    | "doctor" => ":doctor\n  Run system diagnostics:\n  - TTY detection (stdin, stderr)\n  - NO_COLOR environment variable\n  - TERM environment variable\n  - Config path and current settings\n  - Session stats (variables, aliases, history)\n"
    | "config" => ":config [show|save|load|path|reset]\n  Manage REPL configuration.\n  show   - Display current settings\n  save   - Save settings to config file (atomic)\n  load   - Reload settings from config file\n  path   - Show config file path\n  reset  - Reset settings to defaults (not saved)\n"
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

/-- Helper: Check if multi-line JSON input needs more lines. -/
def needsMoreInput (s : String) : Bool :=
  let trimmed := s.trim
  (trimmed.startsWith "{" || trimmed.startsWith "[") && !isBalanced trimmed

mutual

/-- Evaluate a command (dispatch to builtin or oracle). -/
partial def evalCmd (cmd : ReplCmd) (state : ReplState) : IO EvalResult := do
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

  | .source path continueOnError echo =>
    -- Handle :source directly in evalCmd to avoid forward reference
    let (state', output) ← evalSourceInline path continueOnError echo state
    return .continue state' output

  | _ =>
    -- Builtin commands
    let (state', output) ← evalBuiltin cmd state
    return .continue state' output

/-- Evaluate a line of input (with parsing). -/
partial def evalLine (input : String) (state : ReplState) : IO EvalResult := do
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

/-- Execute commands from a script file (called after evalCmd to avoid forward reference). -/
partial def evalSourceInline (path : String) (continueOnError : Bool) (echo : Bool)
    (state : ReplState) : IO (ReplState × ReplOutput) := do
  -- Check recursion depth
  if state.sourceDepth >= maxSourceDepth then
    return (state, ReplOutput.stderr s!"Error: Source depth exceeded ({maxSourceDepth})\n")

  let state := { state with sourceDepth := state.sourceDepth + 1 }

  -- Read file
  let content ← try
    IO.FS.readFile path
  catch _ =>
    return ({ state with sourceDepth := state.sourceDepth - 1 },
            ReplOutput.stderr s!"Error: Cannot read file: {path}\n")

  -- Process lines
  let mut currentState := state
  let mut lineBuffer : Array String := #[]
  let mut lineNum : Nat := 0
  let mut lastCode := ExitCode.success
  let mut accOutput := ReplOutput.empty

  for rawLine in content.splitOn "\n" do
    lineNum := lineNum + 1
    let line := rawLine.dropRightWhile (· == '\r')  -- Handle CRLF

    -- Skip comments
    if line.trimLeft.startsWith "#" then
      continue

    -- Accumulate multi-line
    lineBuffer := lineBuffer.push line
    let fullLine := String.intercalate "\n" lineBuffer.toList

    if needsMoreInput fullLine then
      continue

    lineBuffer := #[]

    -- Skip empty accumulated input
    if fullLine.trim.isEmpty then
      continue

    -- Echo if requested
    if echo then
      accOutput := accOutput.append (ReplOutput.stderr s!"  {lineNum}: {fullLine.take 60}...\n")

    -- Parse with full REPL parser
    match parse fullLine with
    | .ok cmd =>
      -- Expand aliases
      match expandAliases currentState cmd with
      | .error e =>
        accOutput := accOutput.append (ReplOutput.stderr s!"Error at {path}:{lineNum}: {e.message}\n")
        if !continueOnError then
          return ({ currentState with sourceDepth := state.sourceDepth - 1 }, accOutput)
      | .ok expandedCmd =>
        let result ← evalCmd expandedCmd currentState
        match result with
        | .continue newState output =>
          currentState := newState
          lastCode := newState.lastExitCode
          accOutput := accOutput.append output

          if lastCode != .success && !continueOnError then
            accOutput := accOutput.append (ReplOutput.stderr s!"Error at {path}:{lineNum}\n")
            return ({ currentState with sourceDepth := state.sourceDepth - 1 }, accOutput)
        | .exit _ =>
          -- Ignore :quit in sourced scripts
          pure ()
    | .error e =>
      accOutput := accOutput.append (ReplOutput.stderr s!"Parse error at {path}:{lineNum}:\n  {e.msg}\n")
      if !continueOnError then
        return ({ currentState with sourceDepth := state.sourceDepth - 1 }, accOutput)

  return ({ currentState with sourceDepth := state.sourceDepth - 1 }, accOutput)

end  -- mutual

/-- Execute commands from a script file (external API). -/
def evalSource (path : String) (continueOnError : Bool) (echo : Bool)
    (state : ReplState) : IO (ReplState × ReplOutput) :=
  evalSourceInline path continueOnError echo state

end CLI.REPL
