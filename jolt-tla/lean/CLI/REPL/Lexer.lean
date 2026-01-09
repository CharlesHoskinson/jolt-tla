import CLI.REPL.Errors

/-!
# REPL Lexer

Tokenizer for REPL input with span tracking and proper quoting support.

## Quoting Rules
- `$var` / `${var}` - Variable expansion
- `"..."` - Double quotes: expand $vars, support \n \t \\ \"
- `'...'` - Single quotes: literal, no expansion, no escapes
- `\$` - Literal dollar sign (outside quotes)
- `\\` - Literal backslash (outside quotes)

## Main Definitions
* `Lexer` - Lexer state
* `tokenize` - Tokenize input string
-/

namespace CLI.REPL

instance : Inhabited Token where
  default := { kind := .eof, text := "", span := Span.empty }

/-- Lexer state. -/
structure Lexer where
  input : String
  pos : Nat
  tokens : Array Token
  errors : Array ParseError
  deriving Repr, Inhabited

namespace Lexer

/-- Create a new lexer for the given input. -/
def new (input : String) : Lexer :=
  { input, pos := 0, tokens := #[], errors := #[] }

/-- Check if we've reached the end of input. -/
def atEnd (l : Lexer) : Bool := l.pos >= l.input.length

/-- Peek at the current character without consuming. -/
def peek (l : Lexer) : Option Char :=
  l.input.toList[l.pos]?

/-- Peek at the next character (pos + 1). -/
def peekNext (l : Lexer) : Option Char :=
  l.input.toList[l.pos + 1]?

/-- Advance position by n characters. -/
def advance (l : Lexer) (n : Nat := 1) : Lexer :=
  { l with pos := l.pos + n }

/-- Add a token. -/
def addToken (l : Lexer) (tok : Token) : Lexer :=
  { l with tokens := l.tokens.push tok }

/-- Add an error. -/
def addError (l : Lexer) (e : ParseError) : Lexer :=
  { l with errors := l.errors.push e }

/-- Check if character is whitespace. -/
def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n'

/-- Check if character is a word character. -/
def isWordChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '.' || c == '/' || c == '\\'

/-- Check if character starts a special token. -/
def isSpecialChar (c : Char) : Bool :=
  c == '|' || c == '>' || c == ':' || c == '=' ||
  c == '{' || c == '}' || c == '[' || c == ']' ||
  c == '"' || c == '\'' || c == '$'

/-- Skip whitespace. -/
partial def skipWhitespace (l : Lexer) : Lexer :=
  match l.peek with
  | some c => if isWhitespace c then skipWhitespace (l.advance) else l
  | none => l

end Lexer

/-- Scan a word (unquoted). Returns (new lexer, token). -/
partial def scanWord (l : Lexer) (start : Nat) (acc : String) : Lexer × Token :=
  match l.peek with
  | some c =>
    if Lexer.isWordChar c && !Lexer.isWhitespace c && !Lexer.isSpecialChar c then
      scanWord (l.advance) start (acc.push c)
    else
      let tok : Token := { kind := .word, text := acc, span := { start, stop := l.pos } }
      (l, tok)
  | none =>
    let tok : Token := { kind := .word, text := acc, span := { start, stop := l.pos } }
    (l, tok)

/-- Scan a double-quoted string with escape support. -/
partial def scanDoubleString (l : Lexer) (start : Nat) (acc : String) : Lexer × Token :=
  match l.peek with
  | none =>
    -- Unterminated string
    let err := ParseError.at start "unterminated string"
    let tok : Token := { kind := .error, text := acc, span := { start, stop := l.pos } }
    (l.addError err, tok)
  | some '"' =>
    -- End of string
    let tok : Token := { kind := .string, text := acc, span := { start, stop := l.pos + 1 } }
    (l.advance, tok)
  | some '\\' =>
    -- Escape sequence
    match l.peekNext with
    | some 'n' => scanDoubleString (l.advance 2) start (acc.push '\n')
    | some 't' => scanDoubleString (l.advance 2) start (acc.push '\t')
    | some 'r' => scanDoubleString (l.advance 2) start (acc.push '\r')
    | some '\\' => scanDoubleString (l.advance 2) start (acc.push '\\')
    | some '"' => scanDoubleString (l.advance 2) start (acc.push '"')
    | some '$' => scanDoubleString (l.advance 2) start (acc.push '$')
    | some c => scanDoubleString (l.advance 2) start (acc.push '\\' |>.push c)
    | none =>
      let err := ParseError.at l.pos "incomplete escape sequence"
      let tok : Token := { kind := .error, text := acc, span := { start, stop := l.pos } }
      (l.addError err, tok)
  | some c =>
    scanDoubleString (l.advance) start (acc.push c)

/-- Scan a single-quoted string (raw, no escapes). -/
partial def scanSingleString (l : Lexer) (start : Nat) (acc : String) : Lexer × Token :=
  match l.peek with
  | none =>
    let err := ParseError.at start "unterminated string"
    let tok : Token := { kind := .error, text := acc, span := { start, stop := l.pos } }
    (l.addError err, tok)
  | some '\'' =>
    let tok : Token := { kind := .rawString, text := acc, span := { start, stop := l.pos + 1 } }
    (l.advance, tok)
  | some c =>
    scanSingleString (l.advance) start (acc.push c)

/-- Scan a simple variable (alphanumeric name). -/
partial def scanSimpleVar (l : Lexer) (start : Nat) (acc : String) : Lexer × Token :=
  match l.peek with
  | some c =>
    if c.isAlphanum || c == '_' || c == '.' then
      scanSimpleVar (l.advance) start (acc.push c)
    else
      let tok : Token := { kind := .variable, text := acc, span := { start, stop := l.pos } }
      (l, tok)
  | none =>
    let tok : Token := { kind := .variable, text := acc, span := { start, stop := l.pos } }
    (l, tok)

/-- Scan a braced variable ${name}. -/
partial def scanBracedVar (l : Lexer) (start : Nat) (acc : String) : Lexer × Token :=
  match l.peek with
  | some '}' =>
    let tok : Token := { kind := .variable, text := acc, span := { start, stop := l.pos + 1 } }
    (l.advance, tok)
  | some c =>
    if c.isAlphanum || c == '_' || c == '.' then
      scanBracedVar (l.advance) start (acc.push c)
    else
      let err := ParseError.at l.pos s!"invalid character in variable name: '{c}'"
      let tok : Token := { kind := .error, text := acc, span := { start, stop := l.pos } }
      (l.addError err, tok)
  | none =>
    let err := ParseError.at start "unterminated variable reference"
    let tok : Token := { kind := .error, text := acc, span := { start, stop := l.pos } }
    (l.addError err, tok)

/-- Scan a variable reference ($name or ${name}). -/
def scanVariable (l : Lexer) (start : Nat) : Lexer × Token :=
  let l := l.advance  -- skip $
  match l.peek with
  | some '{' =>
    -- ${name} form
    scanBracedVar (l.advance) start ""
  | some c =>
    if c.isAlpha || c == '_' then
      scanSimpleVar l start ""
    else if c == '?' then
      -- $? special variable
      let tok : Token := { kind := .variable, text := "?", span := { start, stop := l.pos + 1 } }
      (l.advance, tok)
    else
      -- Just a literal $
      let tok : Token := { kind := .word, text := "$", span := { start, stop := l.pos } }
      (l, tok)
  | none =>
    let tok : Token := { kind := .word, text := "$", span := { start, stop := l.pos } }
    (l, tok)

/-- Scan the next token. -/
def Lexer.scanToken (l : Lexer) : Lexer :=
  let l := l.skipWhitespace
  if l.atEnd then
    let tok : Token := { kind := .eof, text := "", span := { start := l.pos, stop := l.pos } }
    l.addToken tok
  else
    let start := l.pos
    match l.peek with
    | some '|' =>
      let tok : Token := { kind := .pipe, text := "|", span := { start, stop := start + 1 } }
      (l.advance).addToken tok
    | some '>' =>
      if l.peekNext == some '>' then
        let tok : Token := { kind := .redirect, text := ">>", span := { start, stop := start + 2 } }
        (l.advance 2).addToken tok
      else
        let tok : Token := { kind := .redirect, text := ">", span := { start, stop := start + 1 } }
        (l.advance).addToken tok
    | some ':' =>
      let tok : Token := { kind := .colon, text := ":", span := { start, stop := start + 1 } }
      (l.advance).addToken tok
    | some '=' =>
      let tok : Token := { kind := .equals, text := "=", span := { start, stop := start + 1 } }
      (l.advance).addToken tok
    | some '{' =>
      let tok : Token := { kind := .lbrace, text := "{", span := { start, stop := start + 1 } }
      (l.advance).addToken tok
    | some '}' =>
      let tok : Token := { kind := .rbrace, text := "}", span := { start, stop := start + 1 } }
      (l.advance).addToken tok
    | some '[' =>
      let tok : Token := { kind := .lbracket, text := "[", span := { start, stop := start + 1 } }
      (l.advance).addToken tok
    | some ']' =>
      let tok : Token := { kind := .rbracket, text := "]", span := { start, stop := start + 1 } }
      (l.advance).addToken tok
    | some '"' =>
      let (l', tok) := scanDoubleString (l.advance) start ""
      l'.addToken tok
    | some '\'' =>
      let (l', tok) := scanSingleString (l.advance) start ""
      l'.addToken tok
    | some '$' =>
      let (l', tok) := scanVariable l start
      l'.addToken tok
    | some _ =>
      -- Word or unknown
      let (l', tok) := scanWord l start ""
      l'.addToken tok
    | none =>
      -- Should not reach here (atEnd check above)
      let tok : Token := { kind := .eof, text := "", span := { start, stop := start } }
      l.addToken tok

/-- Tokenize the entire input. -/
partial def Lexer.tokenizeAll (l : Lexer) : Lexer :=
  if l.atEnd then
    -- Add EOF token if not already present
    if l.tokens.isEmpty || l.tokens.back?.map (·.kind) != some .eof then
      let tok : Token := { kind := .eof, text := "", span := { start := l.pos, stop := l.pos } }
      l.addToken tok
    else
      l
  else
    let l' := l.scanToken
    if l'.pos == l.pos && !l'.atEnd then
      -- No progress, force advance to prevent infinite loop
      l'.advance.tokenizeAll
    else
      l'.tokenizeAll

/-- Tokenize an input string. Returns tokens and any errors. -/
def tokenize (input : String) : Array Token × Array ParseError :=
  let lexer := Lexer.new input
  let result := lexer.tokenizeAll
  (result.tokens, result.errors)

/-- Check if braces/brackets are balanced (for multi-line detection). -/
def isBalanced (input : String) : Bool := Id.run do
  let mut depth : Int := 0
  let mut inString := false
  let mut escape := false

  for c in input.toList do
    if escape then
      escape := false
      continue

    if c == '\\' && inString then
      escape := true
      continue

    if c == '"' && !inString then
      inString := true
    else if c == '"' && inString then
      inString := false
    else if !inString then
      if c == '{' || c == '[' then
        depth := depth + 1
      else if c == '}' || c == ']' then
        depth := depth - 1

  depth == 0

/-- Check if input starts an unbalanced JSON object/array. -/
def startsMultiLine (input : String) : Bool :=
  let trimmed := input.trim
  (trimmed.startsWith "{" || trimmed.startsWith "[") && !isBalanced trimmed

end CLI.REPL
