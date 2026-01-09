import CLI.Terminal.Doc

/-!
# ANSI Terminal Renderer

Renders Doc to ANSI-colored terminal output.
Follows semantic color palette from Style.lean.

## Invariants
* All ANSI sequences properly terminated
* Ends with reset sequence when colors used
* Falls back to plain when caps.color=false

## ANSI SGR Codes
* Reset: 0
* Bold: 1
* Dim: 2
* Italic: 3
* Underline: 4
* Foreground colors: 30-37 (or 90-97 for bright)
* Background colors: 40-47 (or 100-107 for bright)
-/

namespace CLI.Terminal

/-- ANSI escape sequence prefix. -/
def escPrefix : String := "\x1b["

/-- ANSI reset sequence. -/
def resetSeq : String := "\x1b[0m"

/-- Map semantic color to ANSI foreground code. -/
def colorToAnsi (c : Color) : Nat :=
  match c with
  | .default => 39     -- Default foreground
  | .accent => 36      -- Cyan
  | .healthy => 32     -- Green
  | .warning => 33     -- Yellow
  | .error => 31       -- Red
  | .secondary => 90   -- Bright black (gray)
  | .crypto => 35      -- Magenta

/-- Map attribute to ANSI code. -/
def attrToAnsi (a : Attr) : Nat :=
  match a with
  | .bold => 1
  | .dim => 2
  | .italic => 3
  | .underline => 4

/-- Build ANSI SGR sequence for a style. -/
def styleToAnsiSeq (style : Style) : String :=
  if style.fg.isNone && style.bg.isNone && style.attrs.isEmpty then
    ""
  else
    let codes : List Nat :=
      (match style.fg with
       | some c => [colorToAnsi c]
       | none => []) ++
      (match style.bg with
       | some c => [colorToAnsi c + 10]  -- BG = FG + 10
       | none => []) ++
      style.attrs.map attrToAnsi
    if codes.isEmpty then ""
    else escPrefix ++ String.intercalate ";" (codes.map toString) ++ "m"

/-- Render state for ANSI output. -/
structure AnsiRenderState where
  indent : Nat := 0
  atLineStart : Bool := true
  output : String := ""
  needsReset : Bool := false  -- Track if we need to emit reset at end
  deriving Repr

namespace AnsiRenderState

/-- Append styled text to output. -/
def appendStyled (s : AnsiRenderState) (style : Style) (text : String) (caps : Caps) : AnsiRenderState :=
  if text.isEmpty then s
  else
    let indentStr := if s.atLineStart then String.ofList (List.replicate s.indent ' ') else ""
    let (styledText, needsReset) :=
      if caps.color then
        let seq := styleToAnsiSeq style
        if seq.isEmpty then (text, s.needsReset)
        else (seq ++ text ++ resetSeq, true)
      else
        (text, s.needsReset)
    { s with
      output := s.output ++ indentStr ++ styledText
      atLineStart := false
      needsReset := needsReset }

/-- Append plain text to output. -/
def append (s : AnsiRenderState) (text : String) : AnsiRenderState :=
  if text.isEmpty then s
  else
    let indentStr := if s.atLineStart then String.ofList (List.replicate s.indent ' ') else ""
    { s with
      output := s.output ++ indentStr ++ text
      atLineStart := false }

/-- Add a newline. -/
def newline (s : AnsiRenderState) : AnsiRenderState :=
  { s with
    output := s.output ++ "\n"
    atLineStart := true }

/-- Increase indentation. -/
def pushIndent (s : AnsiRenderState) (n : Nat) : AnsiRenderState :=
  { s with indent := s.indent + n }

/-- Decrease indentation. -/
def popIndent (s : AnsiRenderState) (n : Nat) : AnsiRenderState :=
  { s with indent := s.indent - n }

end AnsiRenderState

/-- Render a Doc to ANSI-colored text. -/
partial def renderAnsiDoc (doc : Doc) (caps : Caps) (state : AnsiRenderState := {}) : AnsiRenderState :=
  match doc with
  | .empty => state
  | .text span =>
    state.appendStyled span.style span.text caps
  | .line => state.newline
  | .cat a b =>
    let s1 := renderAnsiDoc a caps state
    renderAnsiDoc b caps s1
  | .vcat docs =>
    docs.foldl (fun s d =>
      let s' := renderAnsiDoc d caps s
      if s'.atLineStart then s' else s'.newline
    ) state
  | .indent n d =>
    let s1 := state.pushIndent n
    let s2 := renderAnsiDoc d caps s1
    s2.popIndent n
  | .box title content =>
    let borderStyle : Style := { fg := some .accent }
    -- Top border with title
    let topBorder := if caps.unicode then "┌─ " else "=== "
    let midBorder := if caps.unicode then " ─" else " "
    let repeatChar := if caps.unicode then '─' else '='
    let borderLen := 50 - title.length - 4
    let endBorder := String.ofList (List.replicate (max borderLen 3) repeatChar)
    let s1 := state.appendStyled borderStyle (topBorder ++ title ++ midBorder ++ endBorder) caps
    let s2 := s1.newline
    -- Content with indent
    let s3 := s2.pushIndent 2
    let s4 := renderAnsiDoc content caps s3
    let s5 := if s4.atLineStart then s4 else s4.newline
    let s6 := s5.popIndent 2
    -- Bottom border (optional for plain)
    if caps.unicode then
      let bottomBorder := "└" ++ String.ofList (List.replicate 52 '─')
      s6.appendStyled borderStyle bottomBorder caps |>.newline
    else
      s6
  | .table headers rows =>
    -- Calculate column widths (same logic as plain)
    let headerWidths := headers.map String.length
    let rowWidths := rows.map fun row =>
      row.map fun cell =>
        let rendered := renderAnsiDoc cell caps {}
        -- Strip ANSI to get actual visible length
        stripAnsi rendered.output |>.length
    let allWidths := headerWidths :: rowWidths
    let colWidths := List.range headers.length |>.map fun i =>
      allWidths.foldl (fun maxW row =>
        match row[i]? with
        | some w => if w > maxW then w else maxW
        | none => maxW
      ) 0

    -- Render header with styling
    let headerStyle : Style := { fg := some .accent, attrs := [.bold] }
    let headerLine := headers.zip colWidths |>.map fun (h, w) =>
      h ++ String.ofList (List.replicate (w - h.length) ' ')
    let s1 := state.appendStyled headerStyle (String.intercalate "  " headerLine) caps
    let s2 := s1.newline

    -- Render separator
    let sepLine := colWidths.map fun w => String.ofList (List.replicate w '─')
    let s3 := s2.appendStyled { fg := some .secondary } (String.intercalate "  " sepLine) caps
    let s4 := s3.newline

    -- Render rows
    rows.foldl (fun s row =>
      let cells := row.zip colWidths |>.map fun (cell, w) =>
        let rendered := renderAnsiDoc cell caps {}
        let visLen := stripAnsi rendered.output |>.length
        rendered.output ++ String.ofList (List.replicate (w - visLen) ' ')
      let line := String.intercalate "  " cells
      let s' := s.append line
      s'.newline
    ) s4

  | .keyValue pairs =>
    -- Find max key length for alignment
    let maxKeyLen := pairs.foldl (fun maxK (k, _) =>
      if k.length > maxK then k.length else maxK
    ) 0

    let labelStyle : Style := { fg := some .secondary }
    pairs.foldl (fun s (key, value) =>
      let padding := String.ofList (List.replicate (maxKeyLen - key.length) ' ')
      let s1 := s.appendStyled labelStyle (key ++ ":" ++ padding ++ " ") caps
      let s2 := renderAnsiDoc value caps s1
      if s2.atLineStart then s2 else s2.newline
    ) state
where
  /-- Strip ANSI escape sequences from string. -/
  stripAnsi (s : String) : String := Id.run do
    let mut result := ""
    let mut inEscape := false
    for c in s.toList do
      if inEscape then
        if c == 'm' then inEscape := false
      else if c == '\x1b' then
        inEscape := true
      else
        result := result.push c
    result

/-- Render a Doc to an ANSI string with proper reset. -/
def renderAnsi (doc : Doc) (caps : Caps) : String :=
  let state := renderAnsiDoc doc caps {}
  let output := state.output
  -- Ensure exactly one trailing newline
  let trimmed := output.dropRightWhile (· == '\n')
  -- Remove trailing whitespace from each line
  let lines := trimmed.splitOn "\n"
  let cleanedLines := lines.map fun line => line.dropRightWhile (· == ' ')
  String.intercalate "\n" cleanedLines ++ "\n"

/-- Check that ANSI output is "reset-safe" (no dangling sequences). -/
def isResetSafe (s : String) : Bool := Id.run do
  let mut depth : Int := 0
  let mut i := 0
  let chars := s.toList
  while i < chars.length do
    if chars[i]! == '\x1b' && i + 1 < chars.length && chars[i+1]! == '[' then
      -- Count opening sequences
      let mut j := i + 2
      while j < chars.length && chars[j]! != 'm' do
        j := j + 1
      if j < chars.length then
        -- Check if it's a reset (0m) or setting (other)
        let seq := String.ofList (chars.drop (i + 2) |>.take (j - i - 2))
        if seq == "0" || seq.isEmpty then
          depth := depth - 1
        else
          depth := depth + 1
        i := j + 1
      else
        i := i + 1
    else
      i := i + 1
  -- Valid if depth is 0 or negative (more resets than opens is ok)
  decide (depth ≤ 0)

end CLI.Terminal
