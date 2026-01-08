(****************************************************************************)
(* Module: JSON.tla                                                         *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE JSON ----
(****************************************************************************)
(* Purpose: JSON structure and JCS canonicalization constraints             *)
(* Section Reference: §2.6.1 (JSON safety), JCS (RFC 8785)                  *)
(* Version: 1.0                                                             *)
(* Notes: Abstract model of JSON values with safety constraints.            *)
(*        Numbers must be in safe integer range for consensus.              *)
(****************************************************************************)
EXTENDS Sequences, Naturals, Integers, FiniteSets

(****************************************************************************)
(* JSON Value Types                                                          *)
(****************************************************************************)

\* JSON value type tags
JSON_TYPE_NULL == "null"
JSON_TYPE_BOOL == "bool"
JSON_TYPE_NUMBER == "number"
JSON_TYPE_STRING == "string"
JSON_TYPE_ARRAY == "array"
JSON_TYPE_OBJECT == "object"

JSONType == {JSON_TYPE_NULL, JSON_TYPE_BOOL, JSON_TYPE_NUMBER,
             JSON_TYPE_STRING, JSON_TYPE_ARRAY, JSON_TYPE_OBJECT}

(****************************************************************************)
(* Safe Integer Range (§2.6.1)                                               *)
(* JSON numbers must be in IEEE 754 double safe integer range               *)
(****************************************************************************)

\* Maximum safe integer: 2^53 - 1 = 9007199254740991
MAX_SAFE_INTEGER == 9007199254740991

\* Minimum safe integer: -(2^53 - 1)
MIN_SAFE_INTEGER == -9007199254740991

\* Safe integer range
SafeInteger == MIN_SAFE_INTEGER..MAX_SAFE_INTEGER

\* Check if a number is a safe integer
IsJSONSafeNumber(n) ==
    n \in SafeInteger

(****************************************************************************)
(* JSON Value Structure (Abstract)                                           *)
(* TLC model uses simplified representation                                 *)
(****************************************************************************)

\* For TLC tractability, we model JSON values abstractly
\* Real implementation would use recursive structure

\* JSON value representation (flattened for TLC)
\* type: JSONType
\* boolVal: BOOLEAN (if type = "bool")
\* numVal: Int (if type = "number")
\* strVal: STRING (if type = "string")
\* arrayLen: Nat (if type = "array")
\* objectKeys: set of STRING (if type = "object")

JSONValue == [
    type: JSONType,
    boolVal: BOOLEAN,
    numVal: Int,
    strVal: STRING
]

\* Constructors for JSON values
JSONNull == [type |-> JSON_TYPE_NULL, boolVal |-> FALSE, numVal |-> 0, strVal |-> ""]
JSONBool(b) == [type |-> JSON_TYPE_BOOL, boolVal |-> b, numVal |-> 0, strVal |-> ""]
JSONNumber(n) == [type |-> JSON_TYPE_NUMBER, boolVal |-> FALSE, numVal |-> n, strVal |-> ""]
JSONString(s) == [type |-> JSON_TYPE_STRING, boolVal |-> FALSE, numVal |-> 0, strVal |-> s]

(****************************************************************************)
(* JSON Validation                                                           *)
(****************************************************************************)

\* Validate a JSON value
ValidJSONValue(v) ==
    /\ v.type \in JSONType
    /\ (v.type = JSON_TYPE_NUMBER => IsJSONSafeNumber(v.numVal))

\* Check if value is null
IsNull(v) == v.type = JSON_TYPE_NULL

\* Check if value is boolean
IsBool(v) == v.type = JSON_TYPE_BOOL

\* Check if value is number
IsNumber(v) == v.type = JSON_TYPE_NUMBER

\* Check if value is string
IsString(v) == v.type = JSON_TYPE_STRING

\* Check if value is array
IsArray(v) == v.type = JSON_TYPE_ARRAY

\* Check if value is object
IsObject(v) == v.type = JSON_TYPE_OBJECT

(****************************************************************************)
(* JCS Canonicalization (RFC 8785)                                           *)
(* JSON Canonicalization Scheme for deterministic serialization             *)
(****************************************************************************)

\* JCS key ordering: UTF-16 codepoint order
\* For ASCII strings (which registry keys are), this is bytewise order
\* Same as TAR name ordering

\* Check if two keys are in JCS order (a should come before b)
RECURSIVE JCSKeyLess(_, _)
JCSKeyLess(a, b) ==
    IF a = "" THEN b # ""
    ELSE IF b = "" THEN FALSE
    ELSE IF a[1] < b[1] THEN TRUE
    ELSE IF a[1] > b[1] THEN FALSE
    ELSE JCSKeyLess(SubSeq(a, 2, Len(a)), SubSeq(b, 2, Len(b)))

\* Check if keys are in JCS canonical order
JCSKeysSorted(keys) ==
    \A i \in 1..(Len(keys)-1) :
        JCSKeyLess(keys[i], keys[i+1])

\* No duplicate keys in object
NoDuplicateKeys(keys) ==
    Cardinality({keys[i] : i \in 1..Len(keys)}) = Len(keys)

(****************************************************************************)
(* JSON Object for Registry                                                  *)
(* Registry is serialized as JSON object with string keys and values        *)
(****************************************************************************)

\* Registry JSON entry (key-value pair with string values)
RegistryJSONEntry == [key: STRING, value: STRING]

\* Valid registry JSON entry
ValidRegistryEntry(entry) ==
    /\ entry.key # ""
    /\ entry.value # ""

\* Check if registry entries are in JCS order
RegistryEntriesSorted(entries) ==
    \A i \in 1..(Len(entries)-1) :
        JCSKeyLess(entries[i].key, entries[i+1].key)

\* No duplicate keys in registry
RegistryNoDuplicates(entries) ==
    Cardinality({entries[i].key : i \in 1..Len(entries)}) = Len(entries)

\* Valid canonical registry JSON
ValidCanonicalRegistryJSON(entries) ==
    /\ \A i \in 1..Len(entries) : ValidRegistryEntry(entries[i])
    /\ RegistryEntriesSorted(entries)
    /\ RegistryNoDuplicates(entries)

(****************************************************************************)
(* JSON Parsing Error Cases                                                  *)
(****************************************************************************)

\* Parse result status
PARSE_OK == "ok"
PARSE_ERROR_SYNTAX == "syntax_error"
PARSE_ERROR_UNSAFE_NUMBER == "unsafe_number"
PARSE_ERROR_DUPLICATE_KEY == "duplicate_key"

ParseResult == {PARSE_OK, PARSE_ERROR_SYNTAX, PARSE_ERROR_UNSAFE_NUMBER, PARSE_ERROR_DUPLICATE_KEY}

\* Abstract parse result
JSONParseResult == [status: ParseResult, value: JSONValue]

\* Successful parse
ParseSuccess(v) == [status |-> PARSE_OK, value |-> v]

\* Failed parse
ParseFailure(reason) == [status |-> reason, value |-> JSONNull]

(****************************************************************************)
(* JSON Safety Invariants                                                    *)
(****************************************************************************)

\* All numbers in a JSON value are safe integers
NumbersSafe(v) ==
    v.type = JSON_TYPE_NUMBER => IsJSONSafeNumber(v.numVal)

\* All strings are non-empty (for registry keys)
StringsNonEmpty(v) ==
    v.type = JSON_TYPE_STRING => v.strVal # ""

(****************************************************************************)
(* Concrete Number Validation (for model checking)                           *)
(****************************************************************************)

\* For TLC, use smaller bounds
TLC_MAX_NUMBER == 1000000

\* TLC-safe number check
TLCValidNumber(n) ==
    /\ n >= -TLC_MAX_NUMBER
    /\ n <= TLC_MAX_NUMBER

====
