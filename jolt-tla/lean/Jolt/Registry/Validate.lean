import Jolt.Errors
import Jolt.Registry.KeyValidation
import Jolt.Registry.ConfigTags
import Jolt.JSON.Types
import Jolt.JSON.Safety
import Jolt.JSON.JCS

namespace Jolt.Registry

open Jolt.JSON

/-- A parsed registry entry. -/
structure RegistryEntry where
  key : String
  value : JsonValue
  deriving Repr

/-- Validate a single registry key format. -/
def validateKey (key : String) : OracleResult Unit := do
  if !isValidKeyFormat key then
    throw (ErrorCode.E206_InvalidKeyFormat key)

/-- Check if value contains "TBD" placeholder. -/
def checkNoTBD (key : String) (value : JsonValue) : OracleResult Unit := do
  if containsTBD value then
    throw (ErrorCode.E203_TBDValuePresent key)

/-- Validate a registry entry. -/
def validateEntry (entry : RegistryEntry) : OracleResult Unit := do
  validateKey entry.key
  checkNoTBD entry.key entry.value
  -- Check for external handle if not allowed
  if isExternalTag entry.key then
    throw (ErrorCode.E201_ExternalHandlePresent entry.key)

/-- Parse and validate registry JSON. -/
def parseRegistry (json : JsonValue) : OracleResult (Array RegistryEntry) := do
  match json with
  | .obj fields =>
    let mut entries : Array RegistryEntry := #[]
    for (key, value) in fields do
      entries := entries.push { key := key, value := value }
    pure entries
  | _ =>
    throw (ErrorCode.E106_UnexpectedType "object")

/-- Full registry validation.

Validates all entries and checks required keys are present. -/
def validateRegistry (json : JsonValue) : OracleResult (Array RegistryEntry) := do
  let entries ← parseRegistry json

  -- Validate each entry
  for entry in entries do
    validateEntry entry

  -- Check all required keys are present
  let keys := entries.map (·.key)
  for required in RequiredNonExternalTags do
    if !keys.contains required then
      throw (ErrorCode.E202_MissingRequiredKey required)

  pure entries

/-- Create lookup function from registry entries. -/
def makeLookup (entries : Array RegistryEntry) : String → Option ByteArray :=
  fun key =>
    match entries.find? (·.key == key) with
    | some entry => some (JCS.canonicalizeBytes entry.value)
    | none => none

end Jolt.Registry
