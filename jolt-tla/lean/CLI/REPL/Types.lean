import CLI.Report.Types
import CLI.Terminal.Style
import Jolt.Field.Fr
import Jolt.Encoding.Bytes32
import Jolt.State.VMState

/-!
# REPL Core Types

Core data structures for the Jolt Oracle interactive REPL.

## Main Definitions
* `VarValue` - Variable value types
* `PipeValue` - Typed pipe values for command chaining
* `Variable` - Named variable with optional secret flag
* `Alias` - Command alias definition
* `OutputTarget` - Redirection targets
* `ReplCmd` - Command AST
* `ReplState` - Session state
* `ReplOutput` - Two-channel output (Unix discipline)
-/

namespace CLI.REPL

open Jolt
open Jolt.State
open CLI.Report
open CLI.Terminal

/-- REPL variable value types. -/
inductive VarValue where
  | str (s : String)
  | digest (d : Nat)  -- Store as Nat for simplicity
  | bytes32 (b : ByteArray)  -- Store as ByteArray
  | state (s : String)  -- Store VMState as serialized JSON
  | exitCode (c : UInt32)
  | json (j : String)  -- Stored as raw JSON string
  | none
  deriving Inhabited

/-- Check if two VarValues are equal (structural equality). -/
instance : BEq VarValue where
  beq a b := match a, b with
    | .str s1, .str s2 => s1 == s2
    | .digest d1, .digest d2 => d1 == d2
    | .bytes32 b1, .bytes32 b2 => b1.data == b2.data
    | .exitCode c1, .exitCode c2 => c1 == c2
    | .json j1, .json j2 => j1 == j2
    | .none, .none => true
    | _, _ => false

instance : Repr VarValue where
  reprPrec v _ := match v with
    | .str s => s!"VarValue.str \"{s}\""
    | .digest d => s!"VarValue.digest {d}"
    | .bytes32 b => s!"VarValue.bytes32 ({b.size} bytes)"
    | .state s => s!"VarValue.state \"{s.take 30}...\""
    | .exitCode c => s!"VarValue.exitCode {c}"
    | .json j => s!"VarValue.json \"{j.take 30}...\""
    | .none => "VarValue.none"

/-- Typed pipe value (preserves structure between commands). -/
inductive PipeValue where
  | text (s : String)        -- Plain text output
  | json (j : String)        -- Structured JSON (as string)
  | bytes (b : ByteArray)    -- Binary data
  | typed (v : VarValue)     -- Fully typed value
  deriving Inhabited

instance : Repr PipeValue where
  reprPrec v _ := match v with
    | .text s => s!"PipeValue.text \"{s.take 30}...\""
    | .json j => s!"PipeValue.json \"{j.take 30}...\""
    | .bytes b => s!"PipeValue.bytes ({b.size} bytes)"
    | .typed v => s!"PipeValue.typed {repr v}"

/-- Convert PipeValue to string for output. -/
def PipeValue.toString : PipeValue → String
  | .text s => s
  | .json j => j
  | .bytes b => s!"<{b.size} bytes>"
  | .typed v => match v with
    | .str s => s
    | .digest d => s!"{d}"
    | .bytes32 _ => "<bytes32>"
    | .state _ => "<vmstate>"
    | .exitCode c => s!"{c}"
    | .json j => j
    | .none => ""

/-- Variable metadata. -/
structure Variable where
  name : String
  value : VarValue
  isSecret : Bool := false  -- If true, value is redacted in :env/:show
  deriving Repr, Inhabited

/-- Command alias definition. -/
structure Alias where
  name : String
  expansion : String
  deriving Repr, BEq, Inhabited

/-- Output redirection target. -/
inductive OutputTarget where
  | stdout
  | file (path : String)
  | append (path : String)
  | variable (name : String)
  deriving Repr, Inhabited

/-- REPL command AST. -/
inductive ReplCmd where
  -- Oracle commands (dispatch to existing run* functions)
  | oracle (name : String) (args : Array String)
  -- Built-ins (: prefix)
  | help (topic : Option String)
  | quit
  | clear
  | history (filter : Option String)
  | env
  | set (key : String) (value : String)
  | unset (name : String)
  | alias_ (name : String) (expansion : String)
  | unalias (name : String)
  | load (file : String) (varName : Option String)
  | save (varName : String) (file : String)
  | source (path : String) (continueOnError : Bool) (echo : Bool)
  | show_ (varName : String) (full : Bool)
  | type_ (expr : String)
  | push
  | pop
  | reset
  | config (subCmd : String)
  | redact (enable : Option Bool)
  | examples (cmd : String)
  | cheatsheet
  | version
  -- Beauty layer builtins (P0½)
  | banner (subCmd : String)  -- show, on, off, auto
  | theme                      -- Show terminal capabilities
  | doctor                     -- Sanity check
  -- Composition
  | varRef (name : String)
  | pipe (left : ReplCmd) (right : ReplCmd)
  | redirect (cmd : ReplCmd) (target : OutputTarget)
  | noop
  deriving Repr, Inhabited

/-- Banner display mode (imported from UI). -/
inductive BannerMode where
  | auto   -- Show if stderr is TTY
  | always -- Always show
  | never  -- Never show
  deriving Repr, BEq, Inhabited

/-- REPL configuration options. -/
structure ReplConfig where
  color : ColorMode := .auto
  banner : BannerMode := .auto
  pager : ColorMode := .auto  -- auto, always, never for pager
  outFormat : OutputFormat := .plain
  maxPreviewBytes : Nat := 256
  timeout : Nat := 30  -- seconds
  pretty : Bool := true
  deriving Repr, Inhabited

/-- REPL session state. -/
structure ReplState where
  variables : Array Variable := #[]
  lastResult : PipeValue := .text ""  -- $_
  lastExitCode : ExitCode := .success -- $?
  aliases : Array Alias := #[]
  history : Array String := #[]
  contextFile : Option String := none
  config : ReplConfig := {}
  lineBuffer : Array String := #[]
  inMultiLine : Bool := false
  redactMode : Bool := false  -- :redact on/off
  sessionStackDepth : Nat := 0  -- Track depth instead of storing states
  sourceDepth : Nat := 0  -- Track :source recursion depth
  deriving Repr, Inhabited

/-- Maximum session stack depth. -/
def maxSessionStackDepth : Nat := 10

/-- Maximum :source recursion depth. -/
def maxSourceDepth : Nat := 10

/-- Maximum alias expansion depth. -/
def maxAliasDepth : Nat := 16

/-- Maximum history entries. -/
def maxHistoryEntries : Nat := 10000

/-- Two-channel output (Unix discipline).
    - `out` goes to stdout (data)
    - `err` goes to stderr (diagnostics) -/
structure ReplOutput where
  out : String           -- stdout payload (data)
  err : String           -- stderr payload (diagnostics)
  code : ExitCode
  pipeValue : PipeValue  -- Typed value for piping to next command
  deriving Repr, Inhabited

/-- Result of evaluating a command. -/
inductive EvalResult where
  | continue (state : ReplState) (output : ReplOutput)
  | exit (code : UInt32)
  deriving Repr

/-- Look up a variable by name. -/
def ReplState.getVar (state : ReplState) (name : String) : Option Variable :=
  state.variables.find? (·.name == name)

/-- Set or update a variable. -/
def ReplState.setVar (state : ReplState) (name : String) (value : VarValue)
    (isSecret : Bool := false) : ReplState :=
  let newVar : Variable := { name, value, isSecret }
  match state.variables.findIdx? (·.name == name) with
  | some idx => { state with variables := state.variables.set! idx newVar }
  | none => { state with variables := state.variables.push newVar }

/-- Remove a variable. -/
def ReplState.unsetVar (state : ReplState) (name : String) : ReplState :=
  { state with variables := state.variables.filter (·.name != name) }

/-- Look up an alias by name. -/
def ReplState.getAlias (state : ReplState) (name : String) : Option Alias :=
  state.aliases.find? (·.name == name)

/-- Add or update an alias. -/
def ReplState.setAlias (state : ReplState) (name : String) (expansion : String) : ReplState :=
  let newAlias : Alias := { name, expansion }
  match state.aliases.findIdx? (·.name == name) with
  | some idx => { state with aliases := state.aliases.set! idx newAlias }
  | none => { state with aliases := state.aliases.push newAlias }

/-- Remove an alias. -/
def ReplState.unsetAlias (state : ReplState) (name : String) : ReplState :=
  { state with aliases := state.aliases.filter (·.name != name) }

/-- Add a line to history (with deduplication and max cap). -/
def ReplState.addHistory (state : ReplState) (line : String) : ReplState :=
  -- Skip if identical to last entry
  if state.history.size > 0 && state.history.back? == some line then
    state
  else
    let newHistory := state.history.push line
    -- Cap at max entries
    let trimmed := if newHistory.size > maxHistoryEntries then
      newHistory.extract (newHistory.size - maxHistoryEntries) newHistory.size
    else
      newHistory
    { state with history := trimmed }

/-- Create output with just stdout content. -/
def ReplOutput.stdout (s : String) (code : ExitCode := .success) : ReplOutput :=
  { out := s, err := "", code, pipeValue := .text s }

/-- Create output with just stderr content. -/
def ReplOutput.stderr (s : String) (code : ExitCode := .invalid) : ReplOutput :=
  { out := "", err := s, code, pipeValue := .text "" }

/-- Create output with both channels. -/
def ReplOutput.both (out err : String) (code : ExitCode) : ReplOutput :=
  { out, err, code, pipeValue := .text out }

/-- Empty success output. -/
def ReplOutput.empty : ReplOutput :=
  { out := "", err := "", code := .success, pipeValue := .text "" }

/-- Append two ReplOutputs (concatenating stdout/stderr, keeping last code). -/
def ReplOutput.append (a b : ReplOutput) : ReplOutput :=
  { out := a.out ++ b.out
  , err := a.err ++ b.err
  , code := b.code
  , pipeValue := b.pipeValue }

/-- Get the type name of a variable value. -/
def varTypeName : VarValue → String
  | .str _ => "string"
  | .digest _ => "digest"
  | .bytes32 _ => "bytes32"
  | .state _ => "vmstate"
  | .exitCode _ => "exitCode"
  | .json _ => "json"
  | .none => "none"

end CLI.REPL
