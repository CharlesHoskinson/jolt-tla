namespace Jolt.JSON

/-- A simple JSON value type for the oracle. -/
inductive JsonValue where
  | null : JsonValue
  | bool : Bool → JsonValue
  | num : Int → JsonValue
  | str : String → JsonValue
  | arr : Array JsonValue → JsonValue
  | obj : Array (String × JsonValue) → JsonValue
  deriving Repr, Inhabited

namespace JsonValue

/-- Check if this is a null value. -/
def isNull : JsonValue → Bool
  | .null => true
  | _ => false

/-- Check if this is a string value. -/
def isStr : JsonValue → Bool
  | .str _ => true
  | _ => false

/-- Get string value if present. -/
def asStr? : JsonValue → Option String
  | .str s => some s
  | _ => none

/-- Get integer value if present. -/
def asInt? : JsonValue → Option Int
  | .num n => some n
  | _ => none

/-- Get bool value if present. -/
def asBool? : JsonValue → Option Bool
  | .bool b => some b
  | _ => none

/-- Get array if present. -/
def asArr? : JsonValue → Option (Array JsonValue)
  | .arr a => some a
  | _ => none

/-- Get object fields if present. -/
def asObj? : JsonValue → Option (Array (String × JsonValue))
  | .obj o => some o
  | _ => none

/-- Look up a field in an object. -/
def getField? (v : JsonValue) (key : String) : Option JsonValue :=
  match v with
  | .obj fields => fields.find? (fun (k, _) => k == key) |>.map (·.2)
  | _ => none

end JsonValue
end Jolt.JSON
