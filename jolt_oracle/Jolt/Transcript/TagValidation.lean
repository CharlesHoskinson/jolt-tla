import Jolt.Errors
import Jolt.Util.ASCII
import Jolt.Registry.KeyValidation

namespace Jolt.Transcript

open Jolt.ASCII
open Jolt.Registry (findLastSubstring)

/-- Validate a transcript tag.

Tags must:
- Be ASCII only
- Match charset [A-Z0-9/_]
- Start with "JOLT/"
- Have version suffix /V[0-9]+ -/
def validateTag (tag : String) : OracleResult Unit := do
  -- Must be ASCII
  if !isASCII tag then
    throw (ErrorCode.E406_InvalidTagFormat "must be ASCII")
  -- Check all characters are valid
  for c in tag.toList do
    if !isTagCharASCII c then
      throw (ErrorCode.E406_InvalidTagFormat s!"invalid char '{c}'")
  -- Must start with JOLT/
  if !tag.startsWith "JOLT/" then
    throw (ErrorCode.E406_InvalidTagFormat "must start with 'JOLT/'")
  -- Check version suffix
  let afterPrefix := tag.drop 5
  match findLastSubstring afterPrefix "/V" with
  | none =>
    throw (ErrorCode.E406_InvalidTagFormat "must contain '/V' version suffix")
  | some idx =>
    -- Path between JOLT/ and /V must be non-empty
    if afterPrefix.take idx |>.isEmpty then
      throw (ErrorCode.E406_InvalidTagFormat "empty path")
    -- Version after /V must be non-empty digits
    let version := afterPrefix.drop (idx + 2)
    if !isDigitsPlusASCII version then
      throw (ErrorCode.E406_InvalidTagFormat "version must be digits")

/-- Check if tag is valid without throwing. -/
def isValidTag (tag : String) : Bool :=
  match validateTag tag with
  | .ok _ => true
  | .error _ => false

end Jolt.Transcript
