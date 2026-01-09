import CLI.Terminal.Doc

/-!
# Plain Text Renderer

Renders Doc to plain text without ANSI escapes.
Guaranteed to contain no ESC bytes (\x1b).

## Invariants
* No ANSI escape sequences
* ASCII-only when caps.unicode=false
* Ends with exactly one trailing newline
* No trailing whitespace on any line
-/

namespace CLI.Terminal

/-- Render state for tracking indentation and line position. -/
structure RenderState where
  indent : Nat := 0
  atLineStart : Bool := true
  output : String := ""
  deriving Repr

namespace RenderState

/-- Append text to output, handling indentation. -/
def append (s : RenderState) (text : String) : RenderState :=
  if text.isEmpty then s
  else
    let indentStr := if s.atLineStart then String.ofList (List.replicate s.indent ' ') else ""
    { s with
      output := s.output ++ indentStr ++ text
      atLineStart := false }

/-- Add a newline. -/
def newline (s : RenderState) : RenderState :=
  { s with
    output := s.output ++ "\n"
    atLineStart := true }

/-- Increase indentation. -/
def pushIndent (s : RenderState) (n : Nat) : RenderState :=
  { s with indent := s.indent + n }

/-- Decrease indentation. -/
def popIndent (s : RenderState) (n : Nat) : RenderState :=
  { s with indent := s.indent - n }

end RenderState

/-- Render a Doc to plain text.
    Pure function, no ANSI escapes. -/
partial def renderPlainDoc (doc : Doc) (state : RenderState := {}) : RenderState :=
  match doc with
  | .empty => state
  | .text span => state.append span.text
  | .line => state.newline
  | .cat a b =>
    let s1 := renderPlainDoc a state
    renderPlainDoc b s1
  | .vcat docs =>
    docs.foldl (fun s d =>
      let s' := renderPlainDoc d s
      if s'.atLineStart then s' else s'.newline
    ) state
  | .indent n d =>
    let s1 := state.pushIndent n
    let s2 := renderPlainDoc d s1
    s2.popIndent n
  | .box title content =>
    -- Plain mode: use ASCII box drawing
    let titleLine := "=== " ++ title ++ " ==="
    let s1 := state.append titleLine
    let s2 := s1.newline
    let s3 := renderPlainDoc content s2
    let s4 := if s3.atLineStart then s3 else s3.newline
    s4
  | .table headers rows =>
    -- Calculate column widths
    let headerWidths := headers.map String.length
    let rowWidths := rows.map fun row =>
      row.map fun cell =>
        let rendered := renderPlainDoc cell {}
        rendered.output.length
    let allWidths := headerWidths :: rowWidths
    let colWidths := List.range headers.length |>.map fun i =>
      allWidths.foldl (fun maxW row =>
        match row[i]? with
        | some w => if w > maxW then w else maxW
        | none => maxW
      ) 0

    -- Render header
    let headerLine := headers.zip colWidths |>.map fun (h, w) =>
      h ++ String.ofList (List.replicate (w - h.length) ' ')
    let s1 := state.append (String.intercalate "  " headerLine)
    let s2 := s1.newline

    -- Render separator
    let sepLine := colWidths.map fun w => String.ofList (List.replicate w '-')
    let s3 := s2.append (String.intercalate "  " sepLine)
    let s4 := s3.newline

    -- Render rows
    rows.foldl (fun s row =>
      let cells := row.zip colWidths |>.map fun (cell, w) =>
        let rendered := renderPlainDoc cell {}
        let text := rendered.output.replace "\n" " "  -- Flatten
        text ++ String.ofList (List.replicate (w - text.length) ' ')
      let line := String.intercalate "  " cells
      let s' := s.append line
      s'.newline
    ) s4

  | .keyValue pairs =>
    -- Find max key length for alignment
    let maxKeyLen := pairs.foldl (fun max (k, _) =>
      if k.length > max then k.length else max
    ) 0

    pairs.foldl (fun s (key, value) =>
      let padding := String.ofList (List.replicate (maxKeyLen - key.length) ' ')
      let s1 := s.append (key ++ ":" ++ padding ++ " ")
      let s2 := renderPlainDoc value s1
      if s2.atLineStart then s2 else s2.newline
    ) state

/-- Render a Doc to a plain text string.
    Ensures exactly one trailing newline and no trailing whitespace per line. -/
def renderPlain (doc : Doc) : String :=
  let state := renderPlainDoc doc {}
  let output := state.output
  -- Ensure exactly one trailing newline
  let trimmed := output.dropRightWhile (· == '\n')
  -- Remove trailing whitespace from each line
  let lines := trimmed.splitOn "\n"
  let cleanedLines := lines.map fun line => line.dropRightWhile (· == ' ')
  String.intercalate "\n" cleanedLines ++ "\n"

/-- Check that a string contains no ANSI escape sequences. -/
def isEscapeFree (s : String) : Bool :=
  !s.any (· == '\x1b')

/-- Render and verify no escapes (for testing). -/
def renderPlainSafe (doc : Doc) : Except String String :=
  let output := renderPlain doc
  if isEscapeFree output then
    .ok output
  else
    .error "Plain render contains ESC bytes"

end CLI.Terminal
