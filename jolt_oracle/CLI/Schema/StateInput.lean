import Jolt.Errors
import Jolt.Field.Fr
import Jolt.Encoding.Bytes32
import Jolt.State.VMState
import Jolt.JSON.Types
import Jolt.JSON.Parser

/-!
# State Input Schema

JSON deserialization for VMState and related types.
Strict by default per spec requirements.

## Main Definitions
* `parseBytes32` - Parse Bytes32 from hex string
* `parseFr` - Parse Fr from decimal string
* `parseVMStateV1` - Parse VMStateV1 from JSON
* `parseDigestInput` - Parse digest command input

## Spec Requirements
* Bytes32: `0x` + 64 lowercase hex chars (§2.5.1)
* Fr: Decimal string (§2.6.1)
* No duplicate keys (enforced by parser)
-/

namespace CLI.Schema

open Jolt
open Jolt.JSON
open Jolt.State

/-- Parse a single hex digit (lowercase only). -/
def parseHexDigit (c : Char) : OracleResult UInt8 :=
  if '0' ≤ c && c ≤ '9' then
    pure (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c && c ≤ 'f' then
    pure (c.toNat - 'a'.toNat + 10).toUInt8
  else
    throw ErrorCode.E103_InvalidHex

/-- Parse two hex digits into a byte. -/
def parseHexByte (hi lo : Char) : OracleResult UInt8 := do
  let hiNibble ← parseHexDigit hi
  let loNibble ← parseHexDigit lo
  pure (hiNibble * 16 + loNibble)

/-- Parse Bytes32 from hex string.
    Strict: requires `0x` prefix + 64 lowercase hex chars. -/
def parseBytes32 (s : String) : OracleResult Bytes32 := do
  -- Check prefix
  if s.length < 2 then throw ErrorCode.E103_InvalidHex
  let chars := s.toList
  if chars[0]! != '0' || chars[1]! != 'x' then throw ErrorCode.E103_InvalidHex

  -- Check length: 2 (prefix) + 64 (hex) = 66
  if s.length != 66 then
    throw (ErrorCode.E104_WrongLength 66 s.length)

  -- Parse hex bytes
  let hexPart := s.drop 2
  let hexChars := hexPart.toList
  let mut bytes : ByteArray := ByteArray.empty
  for i in [:32] do
    let hi := hexChars[2 * i]!
    let lo := hexChars[2 * i + 1]!
    let b ← parseHexByte hi lo
    bytes := bytes.push b

  Bytes32.ofByteArray bytes

/-- Parse Fr from decimal string.
    Strict: must be decimal (no hex), no leading zeros except "0". -/
def parseFr (s : String) : OracleResult Fr := do
  if s.isEmpty then throw (ErrorCode.E300_NonCanonicalFr s)

  -- No leading zeros (except "0" itself)
  let frChars := s.toList
  if s.length > 1 && frChars[0]! == '0' then
    throw (ErrorCode.E300_NonCanonicalFr s)

  -- All chars must be digits
  for c in s.toList do
    if !('0' ≤ c && c ≤ '9') then
      throw (ErrorCode.E300_NonCanonicalFr s)

  -- Parse to natural number
  let n := s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

  -- Must be < r (Fr modulus)
  if n >= Fr.modulus then
    throw (ErrorCode.E300_NonCanonicalFr s)

  pure (Fr.ofNat n)

/-- Maximum value for UInt64. -/
private def maxUInt64 : Nat := 18446744073709551615

/-- Parse UInt64 from JSON integer. -/
def parseUInt64 (v : JsonValue) (field : String) : OracleResult UInt64 := do
  match v.asInt? with
  | some i =>
    if i < 0 then throw (ErrorCode.E402_OutOfRange field)
    if i > maxUInt64 then throw (ErrorCode.E402_OutOfRange field)
    pure i.toNat.toUInt64
  | none => throw (ErrorCode.E106_UnexpectedType "integer")

/-- Parse UInt8 from JSON integer. -/
def parseUInt8 (v : JsonValue) (field : String) : OracleResult UInt8 := do
  match v.asInt? with
  | some i =>
    if i < 0 then throw (ErrorCode.E402_OutOfRange field)
    if i > 255 then throw (ErrorCode.E402_OutOfRange field)
    pure i.toNat.toUInt8
  | none => throw (ErrorCode.E106_UnexpectedType "integer")

/-- Parse Bytes32 from JSON string field. -/
def parseBytes32Field (v : JsonValue) (_field : String) : OracleResult Bytes32 := do
  match v.asStr? with
  | some s => parseBytes32 s
  | none => throw (ErrorCode.E106_UnexpectedType "string (hex Bytes32)")

/-- Parse register array (32 UInt64 values). -/
def parseRegs (v : JsonValue) : OracleResult (Array UInt64) := do
  match v.asArr? with
  | some arr =>
    if arr.size != 32 then
      throw (ErrorCode.E104_WrongLength 32 arr.size)
    let mut regs : Array UInt64 := #[]
    for i in [:32] do
      let r ← parseUInt64 arr[i]! s!"regs[{i}]"
      regs := regs.push r
    pure regs
  | none => throw (ErrorCode.E106_UnexpectedType "array")

/-- Parse a config tag from JSON object. -/
def parseConfigTag (v : JsonValue) : OracleResult ConfigTag := do
  match v.asObj? with
  | some _ =>
    let nameVal := v.getField? "name"
    let valueVal := v.getField? "value"
    match nameVal, valueVal with
    | some nv, some vv =>
      match nv.asStr?, vv.asStr? with
      | some ns, some vs =>
        -- Parse hex strings to bytes (0x prefix + hex)
        let nameBytes ← parseHexToBytes ns "config_tag.name"
        let valueBytes ← parseHexToBytes vs "config_tag.value"
        pure { name := nameBytes, value := valueBytes }
      | _, _ => throw (ErrorCode.E106_UnexpectedType "string")
    | _, _ => throw (ErrorCode.E202_MissingRequiredKey "name or value")
  | none => throw (ErrorCode.E106_UnexpectedType "object")
where
  /-- Parse hex string to ByteArray. -/
  parseHexToBytes (s : String) (_field : String) : OracleResult ByteArray := do
    if s.length < 2 then throw ErrorCode.E103_InvalidHex
    let prefixChars := s.toList
    if prefixChars[0]! != '0' || prefixChars[1]! != 'x' then throw ErrorCode.E103_InvalidHex

    let hexPart := s.drop 2
    if hexPart.length % 2 != 0 then throw ErrorCode.E103_InvalidHex

    let hexChars := hexPart.toList
    let mut bytes : ByteArray := ByteArray.empty
    for i in [:(hexChars.length / 2)] do
      let hi := hexChars[2 * i]!
      let lo := hexChars[2 * i + 1]!
      let b ← parseHexByte hi lo
      bytes := bytes.push b
    pure bytes

/-- Parse config tags array. -/
def parseConfigTags (v : JsonValue) : OracleResult (Array ConfigTag) := do
  match v.asArr? with
  | some arr =>
    let mut tags : Array ConfigTag := #[]
    for item in arr do
      let tag ← parseConfigTag item
      tags := tags.push tag
    pure tags
  | none => throw (ErrorCode.E106_UnexpectedType "array")

/-- Get required field from JSON object. -/
def getRequiredField (v : JsonValue) (key : String) : OracleResult JsonValue := do
  match v.getField? key with
  | some field => pure field
  | none => throw (ErrorCode.E202_MissingRequiredKey key)

/-- Parse VMStateV1 from JSON object.

Expected schema:
```json
{
  "pc": 4096,
  "regs": [0, 1, 2, ...],  // 32 elements
  "step_counter": 100,
  "rw_mem_root": "0x<64 hex>",
  "io_root": "0x<64 hex>",
  "halted": 0,
  "exit_code": 0,
  "config_tags": [{"name": "0x...", "value": "0x..."}]
}
```
-/
def parseVMStateV1 (v : JsonValue) : OracleResult VMStateV1 := do
  let pcVal ← getRequiredField v "pc"
  let regsVal ← getRequiredField v "regs"
  let stepVal ← getRequiredField v "step_counter"
  let rwMemVal ← getRequiredField v "rw_mem_root"
  let ioVal ← getRequiredField v "io_root"
  let haltedVal ← getRequiredField v "halted"
  let exitVal ← getRequiredField v "exit_code"

  let pc ← parseUInt64 pcVal "pc"
  let regs ← parseRegs regsVal
  let stepCounter ← parseUInt64 stepVal "step_counter"
  let rwMemRoot ← parseBytes32Field rwMemVal "rw_mem_root"
  let ioRoot ← parseBytes32Field ioVal "io_root"
  let halted ← parseUInt8 haltedVal "halted"
  let exitCode ← parseUInt64 exitVal "exit_code"

  -- config_tags is optional, default to empty
  let configTags ← match v.getField? "config_tags" with
    | some tagsVal => parseConfigTags tagsVal
    | none => pure #[]

  let state : VMStateV1 := {
    pc := pc
    regs := regs
    stepCounter := stepCounter
    rwMemRoot := rwMemRoot
    ioRoot := ioRoot
    halted := halted
    exitCode := exitCode
    configTags := configTags
  }

  -- Validate the state
  state.validate
  pure state

/-- Input for digest command.

Expected schema:
```json
{
  "program_hash": "0x<64 hex>",
  "state": { ... VMStateV1 ... }
}
```
-/
structure DigestInput where
  programHash : Bytes32
  state : VMStateV1
  deriving Repr

/-- Parse digest command input. -/
def parseDigestInput (v : JsonValue) : OracleResult DigestInput := do
  let hashVal ← getRequiredField v "program_hash"
  let stateVal ← getRequiredField v "state"

  let programHash ← parseBytes32Field hashVal "program_hash"
  let state ← parseVMStateV1 stateVal

  pure { programHash := programHash, state := state }

/-- Parse digest input from JSON bytes. -/
def parseDigestInputBytes (bytes : ByteArray) : OracleResult DigestInput := do
  let json ← parseJSONBytes bytes
  parseDigestInput json

end CLI.Schema
