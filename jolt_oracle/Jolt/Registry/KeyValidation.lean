import Jolt.Util.ASCII

namespace Jolt.Registry

open Jolt.ASCII

/-- Helper to get element from list. -/
private def getChar (chars : List Char) (i : Nat) : Char :=
  chars.getD i ' '

/-- Find the last occurrence of a substring in a string. -/
def findLastSubstring (s : String) (sub : String) : Option Nat := Id.run do
  let chars := s.toList
  let subChars := sub.toList
  if subChars.length > chars.length then return none
  let mut lastIdx : Option Nat := none
  for i in [:(chars.length - subChars.length + 1)] do
    let matched := chars.drop i |>.take subChars.length
    if matched == subChars then
      lastIdx := some i
  return lastIdx

/-- Check if a registry key has valid format. -/
def isValidKeyFormat (key : String) : Bool := Id.run do
  if !isASCII key then return false
  if !key.startsWith "JOLT_" then return false
  let afterPrefix := key.drop 5
  if afterPrefix.isEmpty then return false
  match findLastSubstring afterPrefix "_V" with
  | none => return false
  | some idx =>
      let middle := afterPrefix.take idx
      let version := afterPrefix.drop (idx + 2)
      if !isAlphaNumUnderscorePlusASCII middle then return false
      if !isDigitsPlusASCII version then return false
      return true

/-- Extract the version number from a valid registry key. -/
def extractVersion (key : String) : Option Nat := do
  if !isValidKeyFormat key then none
  let afterPrefix := key.drop 5
  let idx ← findLastSubstring afterPrefix "_V"
  let version := afterPrefix.drop (idx + 2)
  version.toNat?

/-- Extract the base name (without version) from a registry key. -/
def extractBaseName (key : String) : Option String := do
  if !isValidKeyFormat key then none
  let afterPrefix := key.drop 5
  let idx ← findLastSubstring afterPrefix "_V"
  some ("JOLT_" ++ afterPrefix.take idx)

end Jolt.Registry
