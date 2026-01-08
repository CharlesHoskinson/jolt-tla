import CLI.REPL.Lexer

/-!
# REPL Parser

Parse tokenized input into ReplCmd AST.

## Grammar (informal)
```
line     := command ("|" command)* (">" path | ">>" path)?
command  := builtin | oracle
builtin  := ":" name args*
oracle   := name args*
args     := word | string | variable
```
-/

namespace CLI.REPL

/-- Parser state. -/
structure Parser where
  tokens : Array Token
  pos : Nat
  deriving Repr, Inhabited

namespace Parser

/-- Create a new parser from tokens. -/
def new (tokens : Array Token) : Parser :=
  { tokens, pos := 0 }

/-- Check if at end of tokens. -/
def atEnd (p : Parser) : Bool :=
  p.pos >= p.tokens.size ||
  (p.tokens[p.pos]?.map (·.kind == .eof)).getD true

/-- Get current token. -/
def current (p : Parser) : Option Token :=
  p.tokens[p.pos]?

/-- Peek at current token kind. -/
def peekKind (p : Parser) : Option TokenKind :=
  p.current.map (·.kind)

/-- Advance to next token. -/
def advance (p : Parser) : Parser :=
  { p with pos := p.pos + 1 }

/-- Check if current token matches a kind. -/
def check (p : Parser) (k : TokenKind) : Bool :=
  p.peekKind == some k

/-- Consume token if it matches, otherwise return error. -/
def expect (p : Parser) (k : TokenKind) (msg : String) : ParseResult (Parser × Token) :=
  match p.current with
  | some tok =>
    if tok.kind == k then
      .ok (p.advance, tok)
    else
      .error { msg, span := tok.span, hint := none }
  | none =>
    .error { msg, span := Span.single p.pos, hint := none }

/-- Match current token if it has the given kind, advance if matched. -/
def matchKind (p : Parser) (k : TokenKind) : Option (Parser × Token) :=
  match p.current with
  | some tok => if tok.kind == k then some (p.advance, tok) else none
  | none => none

/-- Get the text of the current token. -/
def currentText (p : Parser) : Option String :=
  p.current.map (·.text)

/-- Collect arguments until we hit a special token (pipe, redirect, eof). -/
partial def collectArgs (p : Parser) (acc : Array String) : Parser × Array String :=
  match p.current with
  | some tok =>
    match tok.kind with
    | .word | .string | .rawString =>
      collectArgs p.advance (acc.push tok.text)
    | .variable =>
      -- Prepend $ so expandVariables can recognize variable references
      collectArgs p.advance (acc.push s!"${tok.text}")
    | .lbrace | .lbracket =>
      -- Start of JSON, collect everything
      collectJsonArg p acc
    | _ => (p, acc)
  | none => (p, acc)
where
  collectJsonArg (p : Parser) (acc : Array String) : Parser × Array String :=
    match p.current with
    | some tok =>
      match tok.kind with
      | .pipe | .redirect | .eof => (p, acc)
      | _ =>
        -- Accumulate into a single string argument
        let text := tok.text
        let newAcc := if acc.isEmpty then #[text]
          else
            let last := acc.back!
            acc.pop.push (last ++ " " ++ text)
        collectJsonArg p.advance newAcc
    | none => (p, acc)

end Parser

/-- Helper to get array element. -/
private def getArg (args : Array String) (i : Nat) : Option String :=
  args[i]?

/-- Check if args contain a value. -/
private def hasArg (args : Array String) (s : String) : Bool :=
  args.any (· == s)

/-- Parse a builtin command (starting with :). -/
def parseBuiltin (p : Parser) : ParseResult (Parser × ReplCmd) := do
  -- Skip the colon
  let (p, _) ← p.expect .colon "expected ':'"

  -- Get command name
  match p.current with
  | none => .error (ParseError.at p.pos "expected command name after ':'")
  | some nameTok =>
    if nameTok.kind != .word then
      .error (ParseError.unexpectedToken nameTok)
    else
      let name := nameTok.text
      let p := p.advance
      let (p, args) := p.collectArgs #[]

      let cmd ← match name with
        | "help" | "h" | "?" =>
          .ok <| ReplCmd.help (getArg args 0)
        | "quit" | "exit" | "q" =>
          .ok ReplCmd.quit
        | "clear" | "cls" =>
          .ok ReplCmd.clear
        | "history" =>
          .ok <| ReplCmd.history (getArg args 0)
        | "env" =>
          .ok ReplCmd.env
        | "set" =>
          match getArg args 0, getArg args 1 with
          | some k, some v => .ok <| ReplCmd.set k v
          | some k, none => .ok <| ReplCmd.set k ""
          | none, _ => .ok <| ReplCmd.help (some "set")
        | "unset" =>
          match getArg args 0 with
          | some n => .ok <| ReplCmd.unset n
          | none => .ok <| ReplCmd.help (some "unset")
        | "alias" =>
          -- :alias name = expansion
          match getArg args 0, getArg args 1 with
          | some n, some exp => .ok <| ReplCmd.alias_ n exp
          | some n, none => .ok <| ReplCmd.alias_ n ""
          | none, _ => .ok <| ReplCmd.help (some "alias")
        | "unalias" =>
          match getArg args 0 with
          | some n => .ok <| ReplCmd.unalias n
          | none => .ok <| ReplCmd.help (some "unalias")
        | "load" =>
          -- :load file [as var]
          match getArg args 0 with
          | some f =>
            let varName := if args.size >= 3 && getArg args 1 == some "as" then
              getArg args 2
            else
              none
            .ok <| ReplCmd.load f varName
          | none => .ok <| ReplCmd.help (some "load")
        | "save" =>
          match getArg args 0, getArg args 1 with
          | some v, some f => .ok <| ReplCmd.save v f
          | _, _ => .ok <| ReplCmd.help (some "save")
        | "source" =>
          match getArg args 0 with
          | some path =>
            let cont := hasArg args "--continue"
            .ok <| ReplCmd.source path cont
          | none => .ok <| ReplCmd.help (some "source")
        | "show" =>
          match getArg args 0 with
          | some v =>
            let full := hasArg args "--full" || hasArg args "-f"
            .ok <| ReplCmd.show_ v full
          | none => .ok <| ReplCmd.help (some "show")
        | "type" =>
          match getArg args 0 with
          | some e => .ok <| ReplCmd.type_ e
          | none => .ok <| ReplCmd.help (some "type")
        | "push" => .ok ReplCmd.push
        | "pop" => .ok ReplCmd.pop
        | "reset" => .ok ReplCmd.reset
        | "config" =>
          match getArg args 0 with
          | some sub => .ok <| ReplCmd.config sub
          | none => .ok <| ReplCmd.config "show"
        | "redact" =>
          let enable := match getArg args 0 with
            | some "on" => some true
            | some "off" => some false
            | _ => none
          .ok <| ReplCmd.redact enable
        | "examples" =>
          match getArg args 0 with
          | some c => .ok <| ReplCmd.examples c
          | none => .ok <| ReplCmd.help (some "examples")
        | "cheatsheet" => .ok ReplCmd.cheatsheet
        | "version" => .ok ReplCmd.version
        | _ =>
          -- Unknown builtin
          .error (ParseError.unknownCommand s!":{name}" nameTok.span)

      .ok (p, cmd)

/-- Parse an oracle command. -/
def parseOracle (p : Parser) : ParseResult (Parser × ReplCmd) := do
  match p.current with
  | none => .error (ParseError.at p.pos "expected command")
  | some nameTok =>
    if nameTok.kind != .word then
      .error (ParseError.unexpectedToken nameTok)
    else
      let name := nameTok.text
      let p := p.advance
      let (p, args) := p.collectArgs #[]

      -- Check for common aliases without :
      let cmd := match name with
        | "help" | "h" => ReplCmd.help (getArg args 0)
        | "quit" | "exit" | "q" => ReplCmd.quit
        | "clear" | "cls" => ReplCmd.clear
        | "version" => ReplCmd.version
        | _ => ReplCmd.oracle name args

      .ok (p, cmd)

/-- Parse a single command (builtin or oracle). -/
def parseCommand (p : Parser) : ParseResult (Parser × ReplCmd) :=
  if p.check .colon then
    parseBuiltin p
  else if p.check .variable then
    -- Variable reference as command
    match p.current with
    | some tok =>
      .ok (p.advance, ReplCmd.varRef tok.text)
    | none =>
      .error (ParseError.at p.pos "expected variable")
  else
    parseOracle p

/-- Parse redirect target. -/
def parseRedirect (p : Parser) : ParseResult (Parser × OutputTarget) := do
  match p.current with
  | some tok =>
    if tok.kind == .redirect then
      let isAppend := tok.text == ">>"
      let p := p.advance
      match p.current with
      | some pathTok =>
        if pathTok.kind == .word || pathTok.kind == .string then
          let target := if isAppend then
            OutputTarget.append pathTok.text
          else
            OutputTarget.file pathTok.text
          .ok (p.advance, target)
        else if pathTok.kind == .variable then
          .ok (p.advance, OutputTarget.variable pathTok.text)
        else
          .error { msg := "expected file path after redirect"
                 , span := pathTok.span
                 , hint := some "Use > file.txt or >> file.txt" }
      | none =>
        .error (ParseError.at p.pos "expected file path after redirect")
    else
      .ok (p, OutputTarget.stdout)
  | none => .ok (p, OutputTarget.stdout)

/-- Parse rest of line (pipes and redirects). -/
partial def parseRest (p : Parser) (left : ReplCmd) : ParseResult (Parser × ReplCmd) := do
  if p.check .pipe then
    let p := p.advance
    let (p, right) ← parseCommand p
    parseRest p (ReplCmd.pipe left right)
  else if p.check .redirect then
    let (p, target) ← parseRedirect p
    .ok (p, ReplCmd.redirect left target)
  else
    .ok (p, left)

/-- Parse a full line with pipes and redirects. -/
def parseLine (p : Parser) : ParseResult ReplCmd := do
  if p.atEnd then
    return ReplCmd.noop

  -- Parse first command
  let (p, cmd) ← parseCommand p

  -- Check for pipe/redirect
  let (_, cmd) ← parseRest p cmd

  return cmd

/-- Parse an input line into a command. -/
def parse (input : String) : ParseResult ReplCmd :=
  let (tokens, errors) := tokenize input

  -- If there were lexer errors, return the first one
  if h : errors.size > 0 then
    .error errors[0]
  else
    let parser := Parser.new tokens
    parseLine parser

/-- Expand aliases in a command.
    Returns error if max depth exceeded (possible cycle). -/
partial def expandAliases (state : ReplState) (cmd : ReplCmd)
    (depth : Nat := 0) : Except ReplError ReplCmd := do
  if depth >= maxAliasDepth then
    throw (.aliasLoop "unknown")

  match cmd with
  | .oracle name args =>
    -- Check if this is an alias
    match state.getAlias name with
    | some alias_ =>
      -- Parse and expand the alias expansion
      match parse alias_.expansion with
      | .ok expanded =>
        -- Append any additional args to the expanded command
        let expanded := appendArgs expanded args
        expandAliases state expanded (depth + 1)
      | .error e =>
        throw (.parse e)
    | none =>
      .ok cmd
  | .pipe left right =>
    let left' ← expandAliases state left depth
    let right' ← expandAliases state right depth
    .ok (.pipe left' right')
  | .redirect inner target =>
    let inner' ← expandAliases state inner depth
    .ok (.redirect inner' target)
  | _ => .ok cmd
where
  appendArgs (cmd : ReplCmd) (extra : Array String) : ReplCmd :=
    if extra.isEmpty then cmd
    else match cmd with
      | .oracle name args => .oracle name (args ++ extra)
      | _ => cmd

/-- Expand variables in arguments.
    $var -> value, ${var} -> value -/
def expandVariables (state : ReplState) (args : Array String) : Array String :=
  args.map fun arg =>
    -- Simple variable expansion (could be more sophisticated)
    if arg.startsWith "$" then
      let varName := if arg.startsWith "${" && arg.endsWith "}" then
        arg.drop 2 |>.dropRight 1
      else
        arg.drop 1

      -- Special variables
      if varName == "_" then
        state.lastResult.toString
      else if varName == "?" then
        s!"{state.lastExitCode.toUInt32}"
      else
        match state.getVar varName with
        | some v => match v.value with
          | .str s => s
          | .json j => j
          | .digest d => s!"{d}"
          | .exitCode c => s!"{c}"
          | _ => arg  -- Can't expand complex types to string
        | none => arg  -- Keep as-is if not found
    else
      arg

end CLI.REPL
