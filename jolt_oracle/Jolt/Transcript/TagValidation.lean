import Jolt.Errors
import Jolt.Util.ASCII

namespace Jolt.Transcript

open Jolt.ASCII

/-- Validate a transcript tag per §8.6.

Per spec §8.6, tags must:
- Be ASCII only
- Match charset [A-Z0-9/_] (uppercase, digits, forward slash, underscore)
- Start with "JOLT/"
- Have length ≥ 3 (implicit since "JOLT/" is already 5 chars)

NOTE: §8.6 does NOT require a /V version suffix. That requirement
applies only to registry keys (§3.3), not transcript tags. -/
def validateTag (tag : String) : OracleResult Unit := do
  -- Must be ASCII
  if !isASCII tag then
    throw (ErrorCode.E406_InvalidTagFormat "must be ASCII")
  -- Must have minimum length (prefix "JOLT/" is 5 chars, spec says ≥ 3)
  if tag.length < 5 then
    throw (ErrorCode.E406_InvalidTagFormat "tag too short")
  -- Must start with JOLT/
  if !tag.startsWith "JOLT/" then
    throw (ErrorCode.E406_InvalidTagFormat "must start with 'JOLT/'")
  -- Check all characters are valid [A-Z0-9/_]
  for c in tag.toList do
    if !isTagCharASCII c then
      throw (ErrorCode.E406_InvalidTagFormat s!"invalid char '{c}'")

/-- Check if tag is valid without throwing. -/
def isValidTag (tag : String) : Bool :=
  match validateTag tag with
  | .ok _ => true
  | .error _ => false

end Jolt.Transcript
