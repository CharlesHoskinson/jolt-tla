(****************************************************************************)
(* Module: Registry.tla                                                     *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE Registry ----
(****************************************************************************)
(* Purpose: Configuration registry and deployment validation                 *)
(* Appendix J Reference: J.2 (Registry), J.2.8 (config_tags)                *)
(* Version: 1.0                                                             *)
(* Notes: ValidateRegistryValue has semantic range checks.                  *)
(*        ComputeConfigTags uses RequiredKeysSorted for determinism.        *)
(****************************************************************************)
EXTENDS VMState

(****************************************************************************)
(* Registry Key Constants (J.2.3)                                           *)
(****************************************************************************)

\* Required registry keys
KEY_SPEC_VERSION == "JOLT_SPEC_VERSION"
KEY_MAX_MANIFEST_BYTES == "JOLT_MAX_MANIFEST_BYTES"
KEY_MAX_INTENTS == "JOLT_MAX_INTENTS"
KEY_MAX_CHECKPOINTS_BYTES == "JOLT_MAX_CHECKPOINTS_BYTES"
KEY_CONTEXT_BYTES32 == "JOLT_CONTEXT_BYTES32"

\* Required keys for deployment readiness
RequiredKeys == {
    KEY_SPEC_VERSION,
    KEY_MAX_MANIFEST_BYTES,
    KEY_MAX_INTENTS,
    KEY_MAX_CHECKPOINTS_BYTES,
    KEY_CONTEXT_BYTES32
}

\* Sorted sequence of required keys (for deterministic config_tags order)
\* Sort order: lexicographic on UTF-8 byte representation
\* J.2.8: "config_tags MUST be ordered canonically"
RequiredKeysSorted == <<
    KEY_CONTEXT_BYTES32,           \* "JOLT_CONTEXT_BYTES32"
    KEY_MAX_CHECKPOINTS_BYTES,     \* "JOLT_MAX_CHECKPOINTS_BYTES"
    KEY_MAX_INTENTS,               \* "JOLT_MAX_INTENTS"
    KEY_MAX_MANIFEST_BYTES,        \* "JOLT_MAX_MANIFEST_BYTES"
    KEY_SPEC_VERSION               \* "JOLT_SPEC_VERSION"
>>

\* For TLC: verify that RequiredKeysSorted contains exactly RequiredKeys
ASSUME {RequiredKeysSorted[i] : i \in 1..Len(RequiredKeysSorted)} = RequiredKeys
ASSUME Len(RequiredKeysSorted) = Cardinality(RequiredKeys)

(****************************************************************************)
(* Registry Entry Structure                                                  *)
(****************************************************************************)

\* "TBD" sentinel for uninitialized values
TBD_VALUE == "TBD"

\* Registry entry: key + value + metadata
RegistryEntry == [
    key: STRING,
    value: STRING,      \* All values serialized as strings for TLC
    required: BOOLEAN,
    validated: BOOLEAN
]

\* Registry state: mapping from key name to entry
RegistryState == [RequiredKeys -> RegistryEntry]

(****************************************************************************)
(* Registry Entry Type Predicate                                             *)
(****************************************************************************)

RegistryEntryTypeOK(entry) ==
    /\ entry.key \in STRING
    /\ entry.value \in STRING
    /\ entry.required \in BOOLEAN
    /\ entry.validated \in BOOLEAN

RegistryStateTypeOK(registry) ==
    \A k \in RequiredKeys : RegistryEntryTypeOK(registry[k])

(****************************************************************************)
(* Initial Registry State (all TBD)                                          *)
(****************************************************************************)

InitRegistryEntry(keyName) ==
    [
        key |-> keyName,
        value |-> TBD_VALUE,
        required |-> TRUE,
        validated |-> FALSE
    ]

InitRegistry == [k \in RequiredKeys |-> InitRegistryEntry(k)]

(****************************************************************************)
(* Registry Operations                                                       *)
(****************************************************************************)

\* Set a registry value (J.2.4)
SetRegistryValue(registry, keyName, value) ==
    IF keyName \notin RequiredKeys
    THEN registry  \* Invalid key: no-op
    ELSE [registry EXCEPT ![keyName] = [
        @ EXCEPT
            !.value = value,
            !.validated = FALSE  \* Need revalidation
    ]]

\* Mark a registry value as validated
ValidateRegistryEntry(registry, keyName) ==
    IF keyName \notin RequiredKeys
    THEN registry
    ELSE IF registry[keyName].value = TBD_VALUE
         THEN registry  \* Cannot validate TBD
         ELSE [registry EXCEPT ![keyName].validated = TRUE]

\* Get registry value (returns TBD_VALUE if not set)
GetRegistryValue(registry, keyName) ==
    IF keyName \in RequiredKeys
    THEN registry[keyName].value
    ELSE TBD_VALUE

\* Check if a value is TBD
IsTBD(value) == value = TBD_VALUE

\* Check if an entry is ready (not TBD and validated)
EntryReady(entry) ==
    /\ entry.value # TBD_VALUE
    /\ entry.validated

(****************************************************************************)
(* Registry Value Validation (J.2.5)                                        *)
(* MEDIUM FIX: Added semantic bounds checking for numeric values            *)
(****************************************************************************)

\* Parse string as natural number (TLC-safe approximation)
\* Returns -1 if not a valid number
ParseNat(s) ==
    CASE s = "0" -> 0
      [] s = "1" -> 1
      [] s = "2" -> 2
      [] s = "4" -> 4
      [] s = "8" -> 8
      [] s = "16" -> 16
      [] s = "32" -> 32
      [] s = "64" -> 64
      [] s = "128" -> 128
      [] s = "256" -> 256
      [] s = "512" -> 512
      [] s = "1024" -> 1024
      [] s = "2048" -> 2048
      [] s = "4096" -> 4096
      [] s = "8192" -> 8192
      [] s = "16384" -> 16384
      [] OTHER -> -1  \* Unknown format or too large

\* Validate a registry value by key type
\* Returns TRUE if value is semantically valid for its key
ValidateRegistryValue(keyName, value) ==
    IF value = TBD_VALUE
    THEN FALSE  \* TBD is never valid
    ELSE CASE keyName = KEY_SPEC_VERSION ->
              \* Version must be non-empty string (semantic check: valid semver)
              Len(value) > 0
           [] keyName = KEY_MAX_MANIFEST_BYTES ->
              \* Must be positive integer <= 2^20 (1 MiB reasonable bound)
              LET n == ParseNat(value)
              IN  n > 0 /\ n <= 1048576
           [] keyName = KEY_MAX_INTENTS ->
              \* Must be positive integer <= 256 (protocol bound)
              LET n == ParseNat(value)
              IN  n > 0 /\ n <= 256
           [] keyName = KEY_MAX_CHECKPOINTS_BYTES ->
              \* Must be positive integer <= 2^20
              LET n == ParseNat(value)
              IN  n > 0 /\ n <= 1048576
           [] keyName = KEY_CONTEXT_BYTES32 ->
              \* Context can be any non-empty string (32 bytes when decoded)
              Len(value) > 0
           [] OTHER ->
              FALSE  \* Unknown key

\* Validate entire registry
ValidateRegistry(registry) ==
    \A k \in RequiredKeys :
        ValidateRegistryValue(k, registry[k].value)

(****************************************************************************)
(* Deployment Readiness (J.2.4)                                             *)
(****************************************************************************)

\* Check if registry is deployment-ready
\* All required keys must have non-TBD values
RegistryDeploymentReady(registry) ==
    \A k \in RequiredKeys :
        /\ registry[k].value # TBD_VALUE
        /\ registry[k].validated

\* Count of TBD entries
TBDCount(registry) ==
    Cardinality({k \in RequiredKeys : registry[k].value = TBD_VALUE})

(****************************************************************************)
(* Config Tags Computation (J.2.8)                                          *)
(* Extract projection of registry for VMState                               *)
(****************************************************************************)

\* Convert registry entry to ConfigTag
EntryToConfigTag(entry) ==
    [name |-> entry.key, value |-> entry.value]

\* Compute config_tags sequence from registry
\* Uses RequiredKeysSorted for deterministic ordering
ComputeConfigTags(registry) ==
    [i \in 1..Len(RequiredKeysSorted) |->
        LET keyName == RequiredKeysSorted[i]
        IN  EntryToConfigTag(registry[keyName])
    ]

\* Extract config projection as a set (for comparison)
ExtractProjection(registry) ==
    {EntryToConfigTag(registry[k]) : k \in RequiredKeys}

(****************************************************************************)
(* Registry Invariants                                                       *)
(****************************************************************************)

\* No TBD values after deployment
NoTBDInvariant(registry) ==
    \A k \in RequiredKeys : registry[k].value # TBD_VALUE

\* All entries have correct keys
KeyConsistencyInvariant(registry) ==
    \A k \in RequiredKeys : registry[k].key = k

\* Required flag is always TRUE for required keys
RequiredFlagInvariant(registry) ==
    \A k \in RequiredKeys : registry[k].required = TRUE

\* Combined registry invariant
RegistryInvariant(registry) ==
    /\ RegistryStateTypeOK(registry)
    /\ KeyConsistencyInvariant(registry)
    /\ RequiredFlagInvariant(registry)

(****************************************************************************)
(* Config Tags Determinism                                                   *)
(* Same registry -> same config_tags                                         *)
(****************************************************************************)

\* Config tags are deterministic: same registry produces same tags
ConfigTagsDeterministic ==
    \A r1, r2 \in RegistryState :
        r1 = r2 => ComputeConfigTags(r1) = ComputeConfigTags(r2)

\* Config tags preserve all information (injective on required keys)
ConfigTagsInjective ==
    \A r1, r2 \in RegistryState :
        ComputeConfigTags(r1) = ComputeConfigTags(r2) =>
            \A k \in RequiredKeys :
                r1[k].value = r2[k].value

(****************************************************************************)
(* Registry State Machine                                                    *)
(* Valid registry transitions                                                *)
(****************************************************************************)

\* Initial -> Setting values (any TBD -> non-TBD)
CanSetValue(registry, keyName) ==
    /\ keyName \in RequiredKeys

\* Setting value -> Validating (non-TBD -> validated)
CanValidate(registry, keyName) ==
    /\ keyName \in RequiredKeys
    /\ registry[keyName].value # TBD_VALUE

\* All values set -> Deployment ready
CanDeploy(registry) ==
    RegistryDeploymentReady(registry)

====
