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
(* Registry Key Constants (§3.4)                                            *)
(* All 17 required keys per Lean Jolt/Registry/ConfigTags.lean              *)
(****************************************************************************)

\* Cryptographic configuration keys
KEY_POSEIDON_FR == "JOLT_POSEIDON_FR_V1"
KEY_PCS == "JOLT_PCS_V1"
KEY_TRANSCRIPT_SCHEDULE == "JOLT_TRANSCRIPT_SCHEDULE_V1"

\* Guest VM configuration keys
KEY_RISCV_PROFILE == "JOLT_RISCV_PROFILE_V1"
KEY_RISCV_UNPRIV_SPEC == "JOLT_RISCV_UNPRIV_SPEC_V1"
KEY_GUEST_MEMMAP == "JOLT_GUEST_MEMMAP_V1"
KEY_TOOLCHAIN == "JOLT_TOOLCHAIN_V1"

\* DoS caps configuration keys
KEY_MAX_MANIFEST_BYTES == "JOLT_MAX_MANIFEST_BYTES_V1"
KEY_MAX_INTENTS == "JOLT_MAX_INTENTS_V1"
KEY_MAX_CHECKPOINTS_BYTES == "JOLT_MAX_CHECKPOINTS_BYTES_V1"

\* Encoding configuration keys
KEY_BATCH_MANIFEST_ENCODING == "JOLT_BATCH_MANIFEST_ENCODING_V1"
KEY_BATCH_COMMITMENT == "JOLT_BATCH_COMMITMENT_V1"
KEY_CHECKPOINTS_ENCODING == "JOLT_CHECKPOINTS_ENCODING_V1"

\* Binding configuration keys
KEY_CONTEXT_BYTES32 == "JOLT_CONTEXT_BYTES32_V1"

\* Execution configuration keys
KEY_CONTINUATIONS == "JOLT_CONTINUATIONS_V1"

\* Identity configuration keys
KEY_IMPL_COMMIT == "JOLT_IMPL_COMMIT_V1"
KEY_WRAPPER_PROOF_SYSTEM == "JOLT_WRAPPER_PROOF_SYSTEM_V1"

\* All 17 required keys for deployment readiness (§3.4)
RequiredKeys == {
    KEY_POSEIDON_FR,
    KEY_PCS,
    KEY_TRANSCRIPT_SCHEDULE,
    KEY_RISCV_PROFILE,
    KEY_RISCV_UNPRIV_SPEC,
    KEY_GUEST_MEMMAP,
    KEY_TOOLCHAIN,
    KEY_MAX_MANIFEST_BYTES,
    KEY_MAX_INTENTS,
    KEY_MAX_CHECKPOINTS_BYTES,
    KEY_BATCH_MANIFEST_ENCODING,
    KEY_BATCH_COMMITMENT,
    KEY_CHECKPOINTS_ENCODING,
    KEY_CONTEXT_BYTES32,
    KEY_CONTINUATIONS,
    KEY_IMPL_COMMIT,
    KEY_WRAPPER_PROOF_SYSTEM
}

(****************************************************************************)
(* External Handle Tags (§3.4)                                              *)
(* These MUST NOT appear in registry.json - they are computed externally    *)
(****************************************************************************)

EXTERNAL_PARAMETER_REGISTRY_HASH == "JOLT_PARAMETER_REGISTRY_HASH_V1"
EXTERNAL_WRAPPER_VK_HASH == "JOLT_WRAPPER_VK_HASH_V1"
EXTERNAL_CONFORMANCE_BUNDLE_HASH == "JOLT_CONFORMANCE_BUNDLE_HASH_V1"

ExternalHandleTags == {
    EXTERNAL_PARAMETER_REGISTRY_HASH,
    EXTERNAL_WRAPPER_VK_HASH,
    EXTERNAL_CONFORMANCE_BUNDLE_HASH
}

(****************************************************************************)
(* Registry Key Format Validation (§3.2)                                    *)
(* Keys must match: ^JOLT_[A-Z0-9_]+_V[0-9]+$                               *)
(****************************************************************************)

\* Check if a string starts with "JOLT_"
StartsWithJOLT(s) ==
    /\ Len(s) >= 5
    /\ SubSeq(s, 1, 5) = "JOLT_"

\* Check if key matches the required format (simplified for TLC)
\* Full regex: ^JOLT_[A-Z0-9_]+_V[0-9]+$
IsValidKeyFormat(key) ==
    /\ Len(key) >= 8  \* Minimum: "JOLT_X_V1"
    /\ StartsWithJOLT(key)
    \* Note: Full charset validation [A-Z0-9_] omitted for TLC tractability
    \* Production implementations MUST validate the full format

\* Sorted sequence of required keys (for deterministic config_tags order)
\* Sort order: lexicographic on UTF-8 byte representation
\* J.2.8: "config_tags MUST be ordered canonically"
RequiredKeysSorted == <<
    KEY_BATCH_COMMITMENT,          \* "JOLT_BATCH_COMMITMENT_V1"
    KEY_BATCH_MANIFEST_ENCODING,   \* "JOLT_BATCH_MANIFEST_ENCODING_V1"
    KEY_CHECKPOINTS_ENCODING,      \* "JOLT_CHECKPOINTS_ENCODING_V1"
    KEY_CONTEXT_BYTES32,           \* "JOLT_CONTEXT_BYTES32_V1"
    KEY_CONTINUATIONS,             \* "JOLT_CONTINUATIONS_V1"
    KEY_GUEST_MEMMAP,              \* "JOLT_GUEST_MEMMAP_V1"
    KEY_IMPL_COMMIT,               \* "JOLT_IMPL_COMMIT_V1"
    KEY_MAX_CHECKPOINTS_BYTES,     \* "JOLT_MAX_CHECKPOINTS_BYTES_V1"
    KEY_MAX_INTENTS,               \* "JOLT_MAX_INTENTS_V1"
    KEY_MAX_MANIFEST_BYTES,        \* "JOLT_MAX_MANIFEST_BYTES_V1"
    KEY_PCS,                       \* "JOLT_PCS_V1"
    KEY_POSEIDON_FR,               \* "JOLT_POSEIDON_FR_V1"
    KEY_RISCV_PROFILE,             \* "JOLT_RISCV_PROFILE_V1"
    KEY_RISCV_UNPRIV_SPEC,         \* "JOLT_RISCV_UNPRIV_SPEC_V1"
    KEY_TOOLCHAIN,                 \* "JOLT_TOOLCHAIN_V1"
    KEY_TRANSCRIPT_SCHEDULE,       \* "JOLT_TRANSCRIPT_SCHEDULE_V1"
    KEY_WRAPPER_PROOF_SYSTEM       \* "JOLT_WRAPPER_PROOF_SYSTEM_V1"
>>

\* For TLC: verify that RequiredKeysSorted contains exactly RequiredKeys
ASSUME {RequiredKeysSorted[i] : i \in 1..Len(RequiredKeysSorted)} = RequiredKeys
ASSUME Len(RequiredKeysSorted) = Cardinality(RequiredKeys)
ASSUME Cardinality(RequiredKeys) = 17  \* Exactly 17 required keys

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
    ELSE CASE
         \* DoS caps: must be positive integers within bounds
         keyName = KEY_MAX_MANIFEST_BYTES ->
              LET n == ParseNat(value) IN n > 0 /\ n <= 1048576
         [] keyName = KEY_MAX_INTENTS ->
              LET n == ParseNat(value) IN n > 0 /\ n <= 256
         [] keyName = KEY_MAX_CHECKPOINTS_BYTES ->
              LET n == ParseNat(value) IN n > 0 /\ n <= 1048576
         \* String values: must be non-empty
         [] keyName = KEY_POSEIDON_FR -> Len(value) > 0
         [] keyName = KEY_PCS -> Len(value) > 0
         [] keyName = KEY_TRANSCRIPT_SCHEDULE -> Len(value) > 0
         [] keyName = KEY_RISCV_PROFILE -> Len(value) > 0
         [] keyName = KEY_RISCV_UNPRIV_SPEC -> Len(value) > 0
         [] keyName = KEY_GUEST_MEMMAP -> Len(value) > 0
         [] keyName = KEY_TOOLCHAIN -> Len(value) > 0
         [] keyName = KEY_BATCH_MANIFEST_ENCODING -> Len(value) > 0
         [] keyName = KEY_BATCH_COMMITMENT -> Len(value) > 0
         [] keyName = KEY_CHECKPOINTS_ENCODING -> Len(value) > 0
         [] keyName = KEY_CONTEXT_BYTES32 -> Len(value) > 0
         [] keyName = KEY_CONTINUATIONS -> Len(value) > 0
         [] keyName = KEY_IMPL_COMMIT -> Len(value) > 0
         [] keyName = KEY_WRAPPER_PROOF_SYSTEM -> Len(value) > 0
         [] OTHER -> FALSE  \* Unknown key

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

\* No external handle tags in registry (§3.4)
\* External handles are computed, not stored
NoExternalHandlesInvariant(registry) ==
    \A k \in DOMAIN registry : k \notin ExternalHandleTags

\* All keys have valid format (§3.2)
ValidKeyFormatInvariant(registry) ==
    \A k \in DOMAIN registry : IsValidKeyFormat(k)

\* Combined registry invariant
RegistryInvariant(registry) ==
    /\ RegistryStateTypeOK(registry)
    /\ KeyConsistencyInvariant(registry)
    /\ RequiredFlagInvariant(registry)
    /\ NoExternalHandlesInvariant(registry)
    /\ ValidKeyFormatInvariant(registry)

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
