/-!
# Terminal Style System

Typed style layer for consensus-grade CLI output.
Provides semantic colors and attributes without scattering ANSI escapes.

## Main Definitions
* `Color` - Semantic color palette
* `Attr` - Text attributes (bold, dim, etc.)
* `Style` - Combined foreground, background, and attributes
* `Caps` - Terminal capabilities (color, unicode)
-/

namespace CLI.Terminal

/-- Semantic color palette per plan.
    Maps to ANSI 16-color codes for maximum compatibility. -/
inductive Color where
  | default    -- Reset to terminal default
  | accent     -- Cyan: headers, frames, section titles
  | healthy    -- Green: verified, valid, finalized
  | warning    -- Yellow: degraded, lagging, stale
  | error      -- Red: invalid, mismatch, unsafe
  | secondary  -- Dim gray: labels, timestamps
  | crypto     -- Magenta: hashes, digests, commitments
  deriving Repr, BEq, Inhabited

/-- Text attributes. -/
inductive Attr where
  | bold
  | dim
  | underline
  | italic
  deriving Repr, BEq

/-- Combined style with optional foreground, background, and attributes. -/
structure Style where
  fg : Option Color := none
  bg : Option Color := none
  attrs : List Attr := []
  deriving Repr, BEq, Inhabited

namespace Style

/-- No styling (default). -/
def none : Style := {}

/-- Foreground color only. -/
def withFg (c : Color) : Style := { fg := some c }

/-- Bold text. -/
def withBold : Style := { attrs := [.bold] }

/-- Dim text. -/
def withDim : Style := { attrs := [.dim] }

/-- Combine two styles (right takes precedence for fg/bg, attrs merge). -/
def merge (a b : Style) : Style :=
  { fg := b.fg.orElse fun () => a.fg
  , bg := b.bg.orElse fun () => a.bg
  , attrs := a.attrs ++ b.attrs }

instance : Append Style where
  append := merge

end Style

/-- Semantic style presets matching the plan's color system. -/
def Styles.header : Style := { fg := some .accent, attrs := [.bold] }
def Styles.label : Style := { fg := some .secondary }
def Styles.value : Style := Style.none
def Styles.healthy : Style := { fg := some .healthy }
def Styles.warning : Style := { fg := some .warning }
def Styles.error : Style := { fg := some .error, attrs := [.bold] }
def Styles.crypto : Style := { fg := some .crypto }
def Styles.dimmed : Style := { fg := some .secondary, attrs := [.dim] }

/-- Terminal output format. -/
inductive OutputFormat where
  | pretty   -- Multicolored dashboard with boxes
  | plain    -- ASCII-safe, no ANSI
  | json     -- Single JSON object
  | ndjson   -- Newline-delimited JSON stream
  deriving Repr, BEq, Inhabited

/-- Color mode flag. -/
inductive ColorMode where
  | auto     -- Detect from TTY + NO_COLOR
  | always   -- Force color
  | never    -- No color
  deriving Repr, BEq, Inhabited

/-- Terminal capabilities (computed from flags + environment). -/
structure Caps where
  color : Bool      -- ANSI color sequences allowed
  unicode : Bool    -- Unicode glyphs allowed (✔ vs [OK])
  deriving Repr, BEq, Inhabited

namespace Caps

/-- Compute capabilities from environment and flags.
    This is a pure function for easy testing.

    Rules:
    - json/ndjson formats force color=false, unicode=false
    - color=never forces color=false
    - color=auto: enabled if isTty AND NOT noColorEnv
    - color=always: enabled (except for json/ndjson)
    - unicode follows color unless explicitly overridden -/
def compute
    (isTty : Bool)
    (noColorEnv : Bool)
    (format : OutputFormat)
    (colorFlag : ColorMode)
    (noUnicode : Bool := false) : Caps :=
  -- Machine formats force everything off
  if format == .json || format == .ndjson then
    { color := false, unicode := false }
  else
    let colorEnabled := match colorFlag with
      | .never => false
      | .always => true
      | .auto => isTty && !noColorEnv
    let unicodeEnabled := !noUnicode && colorEnabled && isTty
    { color := colorEnabled, unicode := unicodeEnabled }

/-- No capabilities (plain text mode). -/
def plain : Caps := { color := false, unicode := false }

/-- Full capabilities (TTY with color). -/
def full : Caps := { color := true, unicode := true }

end Caps

/-- A styled text span. -/
structure Span where
  style : Style
  text : String
  deriving Repr, BEq

namespace Span

/-- Unstyled text. -/
def plain (s : String) : Span := { style := .none, text := s }

/-- Styled text. -/
def styled (style : Style) (text : String) : Span := { style, text }

end Span

/-- Icon set with TTY and plain variants. -/
structure IconSet where
  pass : String
  warn : String
  fail : String
  info : String
  deriving Repr, BEq

/-- Unicode icons for TTY. -/
def unicodeIcons : IconSet :=
  { pass := "✔"
  , warn := "▲"
  , fail := "✖"
  , info := "●" }

/-- ASCII icons for plain mode. -/
def asciiIcons : IconSet :=
  { pass := "[OK]"
  , warn := "[WARN]"
  , fail := "[FAIL]"
  , info := "[INFO]" }

/-- Select icon set based on capabilities. -/
def selectIcons (caps : Caps) : IconSet :=
  if caps.unicode then unicodeIcons else asciiIcons

end CLI.Terminal
