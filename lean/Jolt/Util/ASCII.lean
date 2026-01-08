/-!
# ASCII Utilities

Explicit ASCII character class checks.

## Main Definitions
* `isUpperASCII` - Check if char is ASCII uppercase [A-Z]
* `isDigitASCII` - Check if char is ASCII digit [0-9]
* `isTagCharASCII` - Check if char is valid in tags [A-Z0-9/_]

## Implementation Notes
The spec requires ASCII strings. Lean's `Char.isUpper` and `Char.isDigit`
are Unicode-aware and would accept non-ASCII characters like Greek letters
or Arabic numerals. We define explicit ASCII-only checks.

## References
* Jolt Spec §3.2, §8.6
-/

namespace Jolt.ASCII

/-- Check if character is ASCII uppercase [A-Z]. -/
def isUpperASCII (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'

/-- Check if character is ASCII lowercase [a-z]. -/
def isLowerASCII (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'

/-- Check if character is ASCII digit [0-9]. -/
def isDigitASCII (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- Check if character is ASCII alphanumeric [A-Z0-9]. -/
def isAlphaNumASCII (c : Char) : Bool := isUpperASCII c || isDigitASCII c

/-- Check if character is ASCII alphanumeric or underscore [A-Z0-9_]. -/
def isAlphaNumUnderscoreASCII (c : Char) : Bool := isAlphaNumASCII c || c == '_'

/-- Check if character is valid in transcript tags [A-Z0-9/_]. -/
def isTagCharASCII (c : Char) : Bool := isAlphaNumASCII c || c == '_' || c == '/'

/-- Check if all characters in string are ASCII (< 128). -/
def isASCII (s : String) : Bool := s.all (·.toNat < 128)

/-- Check if string is non-empty and all chars are [A-Z0-9_]. -/
def isAlphaNumUnderscorePlusASCII (s : String) : Bool :=
  !s.isEmpty && s.all isAlphaNumUnderscoreASCII

/-- Check if string is non-empty and all chars are digits [0-9]. -/
def isDigitsPlusASCII (s : String) : Bool :=
  !s.isEmpty && s.all isDigitASCII

/-- Convert string to UTF-8 bytes. -/
def stringToBytes (s : String) : ByteArray := s.toUTF8

end Jolt.ASCII
