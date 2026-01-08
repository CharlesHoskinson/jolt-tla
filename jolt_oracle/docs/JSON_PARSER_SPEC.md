# JSON Parser Technical Specification

**Module:** `Jolt.JSON.Parser`
**Status:** Not Implemented
**Spec Reference:** §2.6.1, §3.3
**Last Updated:** 2026-01-07

---

## 1. Overview

The JSON parser transforms a token stream (produced by `Jolt.JSON.Lexer`) into a typed AST (`JsonValue`). Unlike standard JSON parsers, this implementation must enforce consensus-critical validation rules that prevent parser-level nondeterminism.

**Design Principle:** Reject, don't normalize. Invalid inputs must produce errors, not silently-corrected output.

---

## 2. Function Signatures

### 2.1 Primary Entry Point

```lean
/-- Parse JSON tokens into a JsonValue AST.
    Returns E100_InvalidJSON on malformed structure.
    Returns E101_DuplicateKey if any object has repeated keys. -/
def parseJSON (tokens : Array Token) : OracleResult JsonValue
```

### 2.2 Internal Helpers

```lean
/-- Parser state tracking position in token stream. -/
structure ParserState where
  tokens : Array Token
  pos : Nat

/-- Parse a single JSON value starting at current position. -/
def parseValue (s : ParserState) : OracleResult (JsonValue × ParserState)

/-- Parse array contents after opening bracket. -/
def parseArray (s : ParserState) : OracleResult (Array JsonValue × ParserState)

/-- Parse object contents after opening brace. -/
def parseObject (s : ParserState) : OracleResult (Array (String × JsonValue) × ParserState)
```

---

## 3. Token Types (from Lexer)

The parser consumes tokens produced by `lexJSON`:

| Token | Description |
|-------|-------------|
| `lbrace` | `{` — object start |
| `rbrace` | `}` — object end |
| `lbracket` | `[` — array start |
| `rbracket` | `]` — array end |
| `colon` | `:` — key-value separator |
| `comma` | `,` — element separator |
| `string s` | String literal (escapes already processed) |
| `number raw value` | Number with raw string preserved |
| `true_` | Boolean true |
| `false_` | Boolean false |
| `null_` | Null value |

---

## 4. Output AST

Target type from `Jolt.JSON.Types`:

```lean
inductive JsonValue where
  | null : JsonValue
  | bool : Bool → JsonValue
  | num : Int → JsonValue          -- Only integers allowed
  | str : String → JsonValue
  | arr : Array JsonValue → JsonValue
  | obj : Array (String × JsonValue) → JsonValue
```

**Note:** Objects use `Array (String × JsonValue)` not `HashMap`. This preserves insertion order, which matters for:
1. Duplicate key detection (first occurrence vs. error)
2. JCS canonicalization (keys sorted by UTF-16 code units)

---

## 5. Validation Requirements

### 5.1 Structural Validation

| Rule | Error Code | Description |
|------|------------|-------------|
| Well-formed JSON | `E100_InvalidJSON` | Tokens must form valid JSON grammar |
| Single root value | `E100_InvalidJSON` | Exactly one value, no trailing tokens |
| Balanced delimiters | `E100_InvalidJSON` | Every `{` has `}`, every `[` has `]` |
| Proper separators | `E100_InvalidJSON` | Colons between key-value, commas between elements |

### 5.2 Object Key Validation

| Rule | Error Code | Spec Reference |
|------|------------|----------------|
| **No duplicate keys** | `E101_DuplicateKey(key)` | §2.6.1 |
| Keys must be strings | `E100_InvalidJSON` | RFC 8259 |

**Duplicate Key Detection Algorithm:**
```
For each object during parsing:
  1. Initialize empty set: seen_keys = {}
  2. For each key-value pair:
     a. If key ∈ seen_keys → throw E101_DuplicateKey(key)
     b. Add key to seen_keys
  3. Return parsed object
```

### 5.3 Number Validation

Numbers require special handling because JSON allows forms that cause consensus divergence.

| Rule | Error Code | Spec Reference |
|------|------------|----------------|
| **No exponent notation** | `E107_ExponentNotation` | §2.6.1 |
| **No fractional values** | `E108_FractionalNumber` | §2.6.1 |
| **Integer range ±(2^53−1)** | `E109_IntegerOutOfRange` | §2.6.1 |

**Safe Integer Bounds:**
```
MAX_SAFE_INT =  9007199254740991  = 2^53 - 1
MIN_SAFE_INT = -9007199254740991  = -(2^53 - 1)
```

**Validation Logic (already in Safety.lean):**
```lean
def validateNumberToken (raw : String) (value : Int) : OracleResult Unit := do
  if stringContains raw "e" || stringContains raw "E" then
    throw ErrorCode.E107_ExponentNotation
  if stringContains raw "." then
    throw ErrorCode.E108_FractionalNumber
  if value > MAX_SAFE_INT || value < MIN_SAFE_INT then
    throw ErrorCode.E109_IntegerOutOfRange
```

**Rationale:** JavaScript's `Number` type uses IEEE 754 double-precision, which can only exactly represent integers up to 2^53−1. Larger values or fractional values may parse differently across implementations.

### 5.4 Encoding Validation (Pre-Lexer)

These checks should occur before lexing, on raw bytes:

| Rule | Error Code | Spec Reference |
|------|------------|----------------|
| **No UTF-8 BOM** | `E100_InvalidJSON` | §2.6.1 |
| **Valid UTF-8** | `E105_InvalidUTF8` | §2.6.1 |
| **ASCII-only for tags** | Context-dependent | §2.4 |

**BOM Detection (already in Safety.lean):**
```lean
def hasBOM (bytes : ByteArray) : Bool :=
  bytes.size >= 3 &&
  bytes[0] == 0xEF &&
  bytes[1] == 0xBB &&
  bytes[2] == 0xBF
```

---

## 6. Grammar (RFC 8259 Subset)

The parser implements this grammar:

```
value     = object / array / string / number / "true" / "false" / "null"

object    = "{" [ member *( "," member ) ] "}"
member    = string ":" value

array     = "[" [ value *( "," value ) ] "]"

string    = <from lexer, escapes processed>
number    = <from lexer, raw string preserved>
```

**Rejected Extensions (must error):**
- Trailing commas: `[1, 2, ]`
- Comments: `// ...` or `/* ... */`
- Unquoted keys: `{foo: 1}`
- Single quotes: `'string'`
- NaN, Infinity, -Infinity
- Hexadecimal numbers: `0xFF`
- Leading zeros: `007` (except `0` itself)

---

## 7. Implementation Strategy

### 7.1 Recursive Descent Parser

```lean
partial def parseValue (s : ParserState) : OracleResult (JsonValue × ParserState) := do
  match s.current? with
  | some .null_ => return (.null, s.advance)
  | some .true_ => return (.bool true, s.advance)
  | some .false_ => return (.bool false, s.advance)
  | some (.string str) => return (.str str, s.advance)
  | some (.number raw value) =>
      validateNumberToken raw value
      return (.num value, s.advance)
  | some .lbracket =>
      let (items, s') ← parseArray s.advance
      return (.arr items, s')
  | some .lbrace =>
      let (fields, s') ← parseObject s.advance
      return (.obj fields, s')
  | _ => throw .E100_InvalidJSON
```

### 7.2 Array Parsing

```lean
partial def parseArray (s : ParserState) : OracleResult (Array JsonValue × ParserState) := do
  if s.current? == some .rbracket then
    return (#[], s.advance)  -- Empty array

  let mut items : Array JsonValue := #[]
  let mut state := s

  loop:
    let (val, s') ← parseValue state
    items := items.push val
    state := s'

    match state.current? with
    | some .rbracket => return (items, state.advance)
    | some .comma => state := state.advance; continue
    | _ => throw .E100_InvalidJSON
```

### 7.3 Object Parsing with Duplicate Detection

```lean
partial def parseObject (s : ParserState) : OracleResult (Array (String × JsonValue) × ParserState) := do
  if s.current? == some .rbrace then
    return (#[], s.advance)  -- Empty object

  let mut fields : Array (String × JsonValue) := #[]
  let mut seenKeys : Std.HashSet String := {}
  let mut state := s

  loop:
    -- Expect string key
    let key ← match state.current? with
      | some (.string k) => pure k
      | _ => throw .E100_InvalidJSON
    state := state.advance

    -- Check for duplicate
    if seenKeys.contains key then
      throw (.E101_DuplicateKey key)
    seenKeys := seenKeys.insert key

    -- Expect colon
    if state.current? != some .colon then
      throw .E100_InvalidJSON
    state := state.advance

    -- Parse value
    let (val, s') ← parseValue state
    fields := fields.push (key, val)
    state := s'

    match state.current? with
    | some .rbrace => return (fields, state.advance)
    | some .comma => state := state.advance; continue
    | _ => throw .E100_InvalidJSON
```

### 7.4 Top-Level Entry Point

```lean
def parseJSON (tokens : Array Token) : OracleResult JsonValue := do
  if tokens.isEmpty then
    throw .E100_InvalidJSON

  let state : ParserState := { tokens := tokens, pos := 0 }
  let (value, finalState) ← parseValue state

  -- Ensure no trailing tokens
  if finalState.pos < tokens.size then
    throw .E100_InvalidJSON

  return value
```

---

## 8. Integration Points

### 8.1 Full Parsing Pipeline

```lean
/-- Parse JSON from raw bytes with all validations. -/
def parseJSONBytes (bytes : ByteArray) : OracleResult JsonValue := do
  -- Pre-lexer checks
  if hasBOM bytes then
    throw .E100_InvalidJSON

  -- Tokenize
  let tokens ← lexJSON bytes

  -- Parse with validation
  parseJSON tokens
```

### 8.2 Registry Loading

```lean
/-- Load and validate registry.json for config_tags projection. -/
def loadRegistry (bytes : ByteArray) : OracleResult JsonValue := do
  let json ← parseJSONBytes bytes

  -- Additional registry-specific checks
  if containsTBD json then
    throw (.E203_TBDValuePresent "registry")

  -- Verify canonical form
  if !JCS.isCanonical bytes json then
    throw .E205_NonCanonicalJSON

  return json
```

### 8.3 CLI Commands

The parser enables these CLI commands:

| Command | Usage |
|---------|-------|
| `digest <file>` | Parse state JSON → compute StateDigest |
| `verify <file>` | Parse chain JSON → verify chunk linkage |
| `test <file>` | Parse test vectors → run batch verification |

---

## 9. Test Cases

### 9.1 Positive Cases (Must Parse)

```json
// Empty structures
{}
[]

// Primitives
null
true
false
0
-42
9007199254740991
"hello"

// Nested
{"a": [1, 2, {"b": null}]}
```

### 9.2 Negative Cases (Must Reject)

| Input | Expected Error |
|-------|----------------|
| `{"a": 1, "a": 2}` | `E101_DuplicateKey("a")` |
| `1e10` | `E107_ExponentNotation` |
| `3.14` | `E108_FractionalNumber` |
| `9007199254740992` | `E109_IntegerOutOfRange` |
| `[1, 2, ]` | `E100_InvalidJSON` (trailing comma) |
| `{a: 1}` | `E100_InvalidJSON` (unquoted key) |
| `// comment` | `E100_InvalidJSON` |
| BOM + `{}` | `E100_InvalidJSON` |

### 9.3 Edge Cases

| Input | Expected Result |
|-------|-----------------|
| `""` | Empty string `.str ""` |
| `"\\u0000"` | String with null char |
| `{"": 1}` | Empty key is valid |
| `-0` | Parses as `0` |
| Deeply nested | Must not stack overflow |

---

## 10. Constraints

### 10.1 Lean 4 Constraints

- **No `noncomputable`** — parser must execute
- **No `sorry`** — all cases handled
- **Termination proof** — recursion must provably terminate (use `partial` if needed for MVP)

### 10.2 Performance Constraints

- **Single pass** — O(n) in token count
- **Bounded memory** — proportional to nesting depth
- **No backtracking** — LL(1) grammar

### 10.3 Consensus Constraints

- **Deterministic** — same input always produces same output or error
- **Byte-exact** — validation based on original bytes, not normalized form
- **Fail-closed** — ambiguous cases must error, not assume

---

## 11. Dependencies

```
Level 0: Errors
Level 1: JSON/Types
Level 2: JSON/Lexer, JSON/Safety
Level 3: JSON/Parser (this module)
Level 4: JSON/JCS
```

### Required Imports

```lean
import Jolt.Errors
import Jolt.JSON.Types
import Jolt.JSON.Lexer
import Jolt.JSON.Safety
```

---

## 12. Acceptance Criteria

- [ ] `parseJSON` compiles without `noncomputable`
- [ ] All positive test cases parse correctly
- [ ] All negative test cases produce correct error codes
- [ ] `lake build Jolt.JSON.Parser` succeeds
- [ ] Integration with CLI `digest` command works
- [ ] No `sorry` in production code
- [ ] Duplicate key detection covers nested objects

---

## 13. References

- **RFC 8259:** The JavaScript Object Notation (JSON) Data Interchange Format
- **RFC 8785:** JSON Canonicalization Scheme (JCS)
- **Jolt Spec §2.6.1:** Canonical JSON safety requirements
- **Jolt Spec §3.3:** Registry canonicalization
- **ECMA-262:** JavaScript Number type precision limits
