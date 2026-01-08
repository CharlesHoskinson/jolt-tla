(****************************************************************************)
(* Module: RegistryValidationTests.tla                                      *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE RegistryValidationTests ----
(****************************************************************************)
(* Purpose: Test cases for registry validation                              *)
(* Section Reference: J.2 (Registry validation), §3.2 (Key format)          *)
(* Version: 1.0                                                             *)
(* Notes: These operators return TRUE if the test passes.                   *)
(*        Run with TLC to verify all tests pass.                            *)
(****************************************************************************)
EXTENDS Registry, TLC

(****************************************************************************)
(* Test Helpers                                                             *)
(****************************************************************************)

\* Create a valid registry with all keys set
ValidTestRegistry ==
    LET setOne(reg, k) == SetRegistryValue(reg, k, "valid_value")
    IN LET r1 == setOne(InitRegistry, KEY_POSEIDON_FR)
           r2 == setOne(r1, KEY_PCS)
           r3 == setOne(r2, KEY_TRANSCRIPT_SCHEDULE)
           r4 == setOne(r3, KEY_RISCV_PROFILE)
           r5 == setOne(r4, KEY_RISCV_UNPRIV_SPEC)
           r6 == setOne(r5, KEY_GUEST_MEMMAP)
           r7 == setOne(r6, KEY_TOOLCHAIN)
           r8 == setOne(r7, KEY_MAX_MANIFEST_BYTES)
           r9 == setOne(r8, KEY_MAX_INTENTS)
           r10 == setOne(r9, KEY_MAX_CHECKPOINTS_BYTES)
           r11 == setOne(r10, KEY_BATCH_MANIFEST_ENCODING)
           r12 == setOne(r11, KEY_BATCH_COMMITMENT)
           r13 == setOne(r12, KEY_CHECKPOINTS_ENCODING)
           r14 == setOne(r13, KEY_CONTEXT_BYTES32)
           r15 == setOne(r14, KEY_CONTINUATIONS)
           r16 == setOne(r15, KEY_IMPL_COMMIT)
           r17 == setOne(r16, KEY_WRAPPER_PROOF_SYSTEM)
       IN r17

(****************************************************************************)
(* Key Format Tests                                                          *)
(****************************************************************************)

\* Test: valid keys pass format check
TestValidKeyFormatPasses ==
    /\ IsValidKeyFormat("JOLT_X_V1")
    /\ IsValidKeyFormat("JOLT_POSEIDON_FR_V1")
    /\ IsValidKeyFormat("JOLT_LONG_KEY_NAME_V123")

\* Test: invalid keys fail format check
TestInvalidKeyFormatFails ==
    /\ ~IsValidKeyFormat("")           \* Empty
    /\ ~IsValidKeyFormat("JOLT_")      \* Too short
    /\ ~IsValidKeyFormat("jolt_x_v1")  \* Would fail full validation (lowercase)
    /\ ~IsValidKeyFormat("OTHER_X_V1") \* Wrong prefix

\* Test: all required keys have valid format
TestAllRequiredKeysValid ==
    \A k \in RequiredKeys : IsValidKeyFormat(k)

(****************************************************************************)
(* Registry State Tests                                                      *)
(****************************************************************************)

\* Test: initial registry has all TBD values
TestInitRegistryAllTBD ==
    \A k \in RequiredKeys : InitRegistry[k].value = TBD_VALUE

\* Test: initial registry is not deployment ready
TestInitRegistryNotReady ==
    ~RegistryDeploymentReady(InitRegistry)

\* Test: TBD count is correct for init
TestTBDCountInit ==
    TBDCount(InitRegistry) = 17

\* Test: setting a value updates correctly
TestSetValueWorks ==
    LET updated == SetRegistryValue(InitRegistry, KEY_POSEIDON_FR, "test_value")
    IN updated[KEY_POSEIDON_FR].value = "test_value"

\* Test: setting invalid key is no-op
TestSetInvalidKeyNoOp ==
    LET updated == SetRegistryValue(InitRegistry, "INVALID_KEY", "value")
    IN updated = InitRegistry

(****************************************************************************)
(* External Handle Tests                                                     *)
(****************************************************************************)

\* Test: external handles are not in required keys
TestExternalHandlesNotRequired ==
    \A h \in ExternalHandleTags : h \notin RequiredKeys

\* Test: external handles have valid format
TestExternalHandlesValidFormat ==
    \A h \in ExternalHandleTags : IsValidKeyFormat(h)

\* Test: no overlap between required keys and external handles
TestNoOverlapRequiredExternal ==
    RequiredKeys \cap ExternalHandleTags = {}

(****************************************************************************)
(* Config Tags Tests                                                         *)
(****************************************************************************)

\* Test: config tags sequence has correct length
TestConfigTagsLength ==
    Len(ComputeConfigTags(InitRegistry)) = 17

\* Test: config tags are deterministic
TestConfigTagsDeterministic ==
    ComputeConfigTags(InitRegistry) = ComputeConfigTags(InitRegistry)

\* Test: sorted sequence covers all required keys
TestRequiredKeysSortedComplete ==
    {RequiredKeysSorted[i] : i \in 1..Len(RequiredKeysSorted)} = RequiredKeys

(****************************************************************************)
(* Invariant Tests                                                           *)
(****************************************************************************)

\* Test: key consistency invariant holds for init
TestKeyConsistencyInit ==
    KeyConsistencyInvariant(InitRegistry)

\* Test: required flag invariant holds for init
TestRequiredFlagInit ==
    RequiredFlagInvariant(InitRegistry)

\* Test: no external handles invariant holds for init
TestNoExternalHandlesInit ==
    NoExternalHandlesInvariant(InitRegistry)

\* Test: valid key format invariant holds for init
TestValidKeyFormatInit ==
    ValidKeyFormatInvariant(InitRegistry)

(****************************************************************************)
(* All Tests Pass                                                            *)
(****************************************************************************)

AllRegistryTestsPass ==
    \* Key format tests
    /\ TestValidKeyFormatPasses
    /\ TestInvalidKeyFormatFails
    /\ TestAllRequiredKeysValid
    \* Registry state tests
    /\ TestInitRegistryAllTBD
    /\ TestInitRegistryNotReady
    /\ TestTBDCountInit
    /\ TestSetValueWorks
    /\ TestSetInvalidKeyNoOp
    \* External handle tests
    /\ TestExternalHandlesNotRequired
    /\ TestExternalHandlesValidFormat
    /\ TestNoOverlapRequiredExternal
    \* Config tags tests
    /\ TestConfigTagsLength
    /\ TestConfigTagsDeterministic
    /\ TestRequiredKeysSortedComplete
    \* Invariant tests
    /\ TestKeyConsistencyInit
    /\ TestRequiredFlagInit
    /\ TestNoExternalHandlesInit
    /\ TestValidKeyFormatInit

\* Use this as INVARIANT in TLC to verify all tests pass
ASSUME AllRegistryTestsPass

====
