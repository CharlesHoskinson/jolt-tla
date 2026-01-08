import CLI.REPL.UI

/-!
# REPL Error Handling

Span tracking, parse errors, and diagnostic rendering with caret display.

## Main Definitions
* `Span` - Character range in input
* `TokenKind` - Lexer token types
* `Token` - Token with span
* `ParseError` - Error with location and hint
* `renderError` - Format error with caret for display
-/

namespace CLI.REPL

/-- A character range in input (0-indexed). -/
structure Span where
  start : Nat
  stop : Nat  -- exclusive
  deriving Repr, BEq

namespace Span

/-- Empty span at position 0. -/
def empty : Span := { start := 0, stop := 0 }

/-- Span covering a single character. -/
def single (pos : Nat) : Span := { start := pos, stop := pos + 1 }

/-- Length of the span. -/
def length (s : Span) : Nat := s.stop - s.start

/-- Merge two spans to cover both. -/
def merge (a b : Span) : Span :=
  { start := min a.start b.start, stop := max a.stop b.stop }

/-- Check if span is empty (zero length). -/
def isEmpty (s : Span) : Bool := s.start >= s.stop

end Span

/-- Token kinds for REPL lexer. -/
inductive TokenKind where
  | word       -- unquoted word
  | string     -- double-quoted string
  | rawString  -- single-quoted string (no escapes)
  | variable   -- $name or ${name}
  | pipe       -- |
  | redirect   -- > or >>
  | colon      -- : (builtin prefix)
  | equals     -- =
  | lbrace     -- {
  | rbrace     -- }
  | lbracket   -- [
  | rbracket   -- ]
  | eof        -- end of input
  | error      -- lexer error
  deriving Repr, BEq

/-- A token with its text and source location. -/
structure Token where
  kind : TokenKind
  text : String
  span : Span
  deriving Repr

/-- Parse error with location and optional hint. -/
structure ParseError where
  msg : String
  span : Span
  hint : Option String := none
  deriving Repr

/-- Create a parse error at a position. -/
def ParseError.at (pos : Nat) (msg : String) (hint : Option String := none) : ParseError :=
  { msg, span := Span.single pos, hint }

/-- Create a parse error for a span. -/
def ParseError.forSpan (span : Span) (msg : String) (hint : Option String := none) : ParseError :=
  { msg, span, hint }

/-- Create an error for an unknown command. -/
def ParseError.unknownCommand (name : String) (span : Span) : ParseError :=
  { msg := s!"unknown command '{name}'"
  , span
  , hint := some "Type ':help' for available commands" }

/-- Create an error for unexpected token. -/
def ParseError.unexpectedToken (tok : Token) : ParseError :=
  { msg := s!"unexpected token '{tok.text}'"
  , span := tok.span
  , hint := none }

/-- Create an error for missing argument. -/
def ParseError.missingArg (cmd : String) (argName : String) (pos : Nat) : ParseError :=
  { msg := s!"'{cmd}' requires {argName}"
  , span := Span.single pos
  , hint := some s!"Usage: {cmd} <{argName}>" }

/-- Render error with caret and hint.

    Example output:
    ```
    Parse error: unexpected token '|'
      digest state.json | verify
                        ^
    Hint: 'verify' requires a mode (e.g., verify chain state.json)
    ``` -/
def renderError (e : ParseError) (input : String) (caps : UiCaps) : String :=
  let theme := getTheme caps

  -- Error header
  let header := s!"{theme.err}Parse error:{theme.reset} {e.msg}\n"

  -- Source line with caret
  let sourceLine := s!"  {input}\n"

  -- Caret line: spaces for indent + prefix, then caret(s)
  let caretPadding := String.mk (List.replicate (2 + e.span.start) ' ')
  let caretLength := max 1 e.span.length
  let carets := if caretLength == 1 then "^"
    else "^" ++ String.mk (List.replicate (caretLength - 1) '~')
  let caretLine := s!"{caretPadding}{theme.err}{carets}{theme.reset}\n"

  -- Optional hint
  let hintLine := match e.hint with
    | some h => s!"{theme.dim}Hint: {h}{theme.reset}\n"
    | none => ""

  header ++ sourceLine ++ caretLine ++ hintLine

/-- Render error for non-interactive mode (no colors). -/
def renderErrorPlain (e : ParseError) (input : String) : String :=
  let header := s!"Parse error: {e.msg}\n"
  let sourceLine := s!"  {input}\n"
  let caretPadding := String.mk (List.replicate (2 + e.span.start) ' ')
  let caretLength := max 1 e.span.length
  let carets := if caretLength == 1 then "^"
    else "^" ++ String.mk (List.replicate (caretLength - 1) '~')
  let caretLine := s!"{caretPadding}{carets}\n"
  let hintLine := match e.hint with
    | some h => s!"Hint: {h}\n"
    | none => ""
  header ++ sourceLine ++ caretLine ++ hintLine

/-- Result type for operations that can fail with ParseError. -/
abbrev ParseResult (α : Type) := Except ParseError α

/-- REPL-specific error kinds for richer errors. -/
inductive ReplError where
  | parse (e : ParseError)
  | aliasLoop (name : String)
  | varNotFound (name : String)
  | fileNotFound (path : String)
  | commandFailed (cmd : String) (code : UInt32)
  | internal (msg : String)
  deriving Repr

/-- Convert ReplError to a displayable message. -/
def ReplError.message : ReplError → String
  | .parse e => e.msg
  | .aliasLoop name => s!"Alias expansion limit reached (possible cycle in '{name}')"
  | .varNotFound name => s!"Variable not found: ${name}"
  | .fileNotFound path => s!"File not found: {path}"
  | .commandFailed cmd code => s!"Command '{cmd}' failed with exit code {code}"
  | .internal msg => s!"Internal error: {msg}"

/-- Convert ReplError to ParseError for display. -/
def ReplError.toParseError (e : ReplError) (inputLen : Nat := 0) : ParseError :=
  match e with
  | .parse pe => pe
  | .aliasLoop name =>
    { msg := s!"Alias expansion limit reached"
    , span := Span.empty
    , hint := some s!"Possible cycle involving alias '{name}'" }
  | .varNotFound name =>
    { msg := s!"Variable not found: ${name}"
    , span := Span.empty
    , hint := some "Use ':env' to see defined variables" }
  | .fileNotFound path =>
    { msg := s!"File not found: {path}"
    , span := Span.empty
    , hint := some "Check file path and permissions" }
  | .commandFailed cmd code =>
    { msg := s!"Command '{cmd}' failed"
    , span := Span.empty
    , hint := some s!"Exit code: {code}" }
  | .internal msg =>
    { msg := s!"Internal error: {msg}"
    , span := Span.empty
    , hint := none }

end CLI.REPL
