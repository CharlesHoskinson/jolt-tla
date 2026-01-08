import CLI.Terminal.Style

/-!
# Document Layout AST

Layout primitives for building terminal output.
Separates structure from rendering for testability.

## Main Definitions
* `Doc` - Layout AST (text, lines, boxes, tables, etc.)
* Layout combinators (vcat, hcat, indent, etc.)
-/

namespace CLI.Terminal

/-- Document AST for terminal layout.
    Represents structure without committing to a specific renderer. -/
inductive Doc where
  | empty                                    -- Nothing
  | text (s : Span)                          -- Styled text span
  | line                                     -- Hard line break
  | cat (a b : Doc)                          -- Horizontal concatenation
  | vcat (docs : List Doc)                   -- Vertical stack
  | indent (n : Nat) (d : Doc)               -- Indent by n spaces
  | box (title : String) (content : Doc)     -- Titled box with border
  | table (headers : List String) (rows : List (List Doc))  -- Table
  | keyValue (pairs : List (String × Doc))   -- Key-value grid
  deriving Repr, Inhabited

namespace Doc

/-- Empty document. -/
def nil : Doc := .empty

/-- Plain unstyled text. -/
def plain (s : String) : Doc := .text (Span.plain s)

/-- Styled text. -/
def styled (style : Style) (s : String) : Doc := .text (Span.styled style s)

/-- Horizontal concatenation. -/
def hcat (docs : List Doc) : Doc :=
  docs.foldl .cat .empty

/-- Vertical concatenation with blank lines between. -/
def vsep (docs : List Doc) : Doc :=
  .vcat (docs.intersperse .line)

/-- Text with newline. -/
def textLn (s : String) : Doc := .cat (.text (Span.plain s)) .line

/-- Styled text with newline. -/
def styledLn (style : Style) (s : String) : Doc :=
  .cat (.text (Span.styled style s)) .line

/-- Header text (accent color, bold). -/
def header (s : String) : Doc := .text (Span.styled Styles.header s)

/-- Label text (secondary/dim). -/
def label (s : String) : Doc := .text (Span.styled Styles.label s)

/-- Success/healthy text. -/
def healthy (s : String) : Doc := .text (Span.styled Styles.healthy s)

/-- Warning text. -/
def warning (s : String) : Doc := .text (Span.styled Styles.warning s)

/-- Error text. -/
def error (s : String) : Doc := .text (Span.styled Styles.error s)

/-- Crypto value (hash, digest). -/
def crypto (s : String) : Doc := .text (Span.styled Styles.crypto s)

/-- Dimmed text. -/
def dimmed (s : String) : Doc := .text (Span.styled Styles.dimmed s)

/-- Status indicator with icon. -/
def status (icons : IconSet) (isOk : Bool) (msg : String) : Doc :=
  if isOk then
    hcat [healthy icons.pass, plain " ", plain msg]
  else
    hcat [error icons.fail, plain " ", plain msg]

/-- Key-value pair for grids. -/
def kv (key : String) (value : Doc) : (String × Doc) := (key, value)

/-- Simple key-value with string value. -/
def kvStr (key : String) (value : String) : (String × Doc) :=
  (key, plain value)

/-- Header bar for top of output. -/
def headerBar (title : String) (subtitle : Option String := none) : Doc :=
  match subtitle with
  | none => header title
  | some sub => hcat [header title, plain " ", dimmed sub]

/-- Section with title and content. -/
def titled (title : String) (content : Doc) : Doc :=
  .vcat [header title, .indent 2 content]

/-- Horizontal rule. -/
def rule (width : Nat) : Doc :=
  plain (String.ofList (List.replicate width '─'))

/-- Error display with code and message. -/
def errorBlock (code : String) (message : String) (path : Option String := none) : Doc :=
  let pathLine := match path with
    | none => .empty
    | some p => .vcat [.indent 2 (hcat [dimmed "at: ", plain p])]
  .vcat [
    hcat [error "Error: ", plain code],
    .indent 2 (plain message),
    pathLine
  ]

end Doc

end CLI.Terminal
