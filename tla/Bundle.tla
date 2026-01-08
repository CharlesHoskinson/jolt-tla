(****************************************************************************)
(* Module: Bundle.tla                                                       *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE Bundle ----
(****************************************************************************)
(* Purpose: Conformance bundle structure tying together TAR, JSON, Registry *)
(* Section Reference: §14 (Bundle format), §3.4 (External handles)          *)
(* Version: 1.0                                                             *)
(* Notes: A conformance bundle is a TAR archive containing:                 *)
(*        - registry.json (JCS-canonical)                                   *)
(*        - Other required conformance files                                *)
(*        External handle tags are computed from bundle contents.           *)
(****************************************************************************)
EXTENDS Tar, JSON, Registry, Hash, Sequences, Naturals, FiniteSets

(****************************************************************************)
(* Bundle Structure                                                          *)
(****************************************************************************)

\* Conformance bundle: registry + TAR members
ConformanceBundle == [
    registry: RegistryState,
    tar_members: Seq(TarMember)
]

(****************************************************************************)
(* Required Bundle Files                                                     *)
(****************************************************************************)

\* registry.json must be present and contain all required keys
REGISTRY_JSON_PATH == "registry.json"

\* Check if bundle has registry.json
HasRegistryJSON(bundle) ==
    HasMember(bundle.tar_members, REGISTRY_JSON_PATH)

(****************************************************************************)
(* Bundle Validation                                                         *)
(****************************************************************************)

\* Valid conformance bundle structure
ValidBundleStructure(bundle) ==
    /\ ValidTar(bundle.tar_members)
    /\ HasRegistryJSON(bundle)

\* Registry in bundle must be deployment-ready
ValidBundleRegistry(bundle) ==
    /\ RegistryDeploymentReady(bundle.registry)
    /\ ValidateRegistry(bundle.registry)

\* Combined bundle validity
ValidBundle(bundle) ==
    /\ ValidBundleStructure(bundle)
    /\ ValidBundleRegistry(bundle)

(****************************************************************************)
(* External Handle Computation (§3.4)                                        *)
(* External handles are computed from bundle contents, NOT stored           *)
(****************************************************************************)

\* JOLT_PARAMETER_REGISTRY_HASH_V1: SHA-256 of JCS-canonical registry.json
\* This is computed, never stored in registry
ComputeRegistryHash(registry) ==
    \* Abstract: hash of JCS-canonical serialization of all key-value pairs
    \* Real implementation: SHA256(JCS(registry.json))
    LET configTags == ComputeConfigTags(registry)
        \* Serialize config tags to bytes for hashing
        serialized == Len(configTags)  \* Simplified fingerprint for TLC
    IN SHA256Hash(serialized)

\* JOLT_WRAPPER_VK_HASH_V1: SHA-256 of wrapper verification key
\* This is computed from the wrapper circuit, not the registry
\* Parameter: vkBytes is the serialized verification key
ComputeWrapperVKHash(vkBytes) ==
    SHA256Hash(vkBytes)

\* JOLT_CONFORMANCE_BUNDLE_HASH_V1: SHA-256 of canonical TAR
\* This is computed from the entire bundle TAR
ComputeBundleHash(tarMembers) ==
    \* Abstract: hash of canonical TAR bytes
    \* Real implementation: SHA256(canonical_tar_bytes)
    LET fingerprint == Len(tarMembers)  \* Simplified for TLC
    IN SHA256Hash(fingerprint)

(****************************************************************************)
(* External Handle Validation                                                *)
(* These tags must NOT appear in registry.json itself                       *)
(****************************************************************************)

\* Check that no external handle tags are in registry
NoExternalHandlesInRegistry(bundle) ==
    \A k \in DOMAIN bundle.registry :
        k \notin ExternalHandleTags

\* The external handles are valid (computed correctly)
ExternalHandlesValid(bundle, registryHash, wrapperVKHash, bundleHash) ==
    /\ registryHash = ComputeRegistryHash(bundle.registry)
    /\ bundleHash = ComputeBundleHash(bundle.tar_members)
    \* wrapperVKHash depends on external VK, can't verify here

(****************************************************************************)
(* Bundle State Machine                                                      *)
(* Bundle creation and validation workflow                                  *)
(****************************************************************************)

BUNDLE_STATE_EMPTY == "empty"
BUNDLE_STATE_LOADING == "loading"
BUNDLE_STATE_VALID == "valid"
BUNDLE_STATE_INVALID == "invalid"

BundleState == {BUNDLE_STATE_EMPTY, BUNDLE_STATE_LOADING, BUNDLE_STATE_VALID, BUNDLE_STATE_INVALID}

\* Bundle processing state
BundleProcessingState == [
    state: BundleState,
    bundle: ConformanceBundle,
    error: STRING
]

\* Initial processing state
InitBundleProcessing ==
    [state |-> BUNDLE_STATE_EMPTY,
     bundle |-> [registry |-> InitRegistry, tar_members |-> << >>],
     error |-> ""]

\* Load TAR members into bundle
LoadTarMembers(procState, members) ==
    IF procState.state # BUNDLE_STATE_EMPTY
    THEN procState  \* Can only load into empty state
    ELSE IF ~ValidTar(members)
         THEN [procState EXCEPT !.state = BUNDLE_STATE_INVALID,
                                !.error = "invalid_tar_structure"]
         ELSE [procState EXCEPT !.state = BUNDLE_STATE_LOADING,
                                !.bundle.tar_members = members]

\* Parse and load registry from TAR
LoadRegistry(procState, registry) ==
    IF procState.state # BUNDLE_STATE_LOADING
    THEN procState
    ELSE IF ~RegistryDeploymentReady(registry)
         THEN [procState EXCEPT !.state = BUNDLE_STATE_INVALID,
                                !.error = "registry_not_ready"]
         ELSE [procState EXCEPT !.bundle.registry = registry]

\* Validate complete bundle
ValidateBundle(procState) ==
    IF procState.state # BUNDLE_STATE_LOADING
    THEN procState
    ELSE IF ValidBundle(procState.bundle)
         THEN [procState EXCEPT !.state = BUNDLE_STATE_VALID]
         ELSE [procState EXCEPT !.state = BUNDLE_STATE_INVALID,
                                !.error = "bundle_validation_failed"]

(****************************************************************************)
(* Bundle Invariants                                                         *)
(****************************************************************************)

\* Valid bundle has no external handles in registry
BundleNoExternalHandles(bundle) ==
    ValidBundle(bundle) => NoExternalHandlesInRegistry(bundle)

\* Valid bundle has all required registry keys
BundleHasAllRequiredKeys(bundle) ==
    ValidBundle(bundle) =>
        \A k \in RequiredKeys : k \in DOMAIN bundle.registry

\* Valid bundle TAR is sorted
BundleTarSorted(bundle) ==
    ValidBundle(bundle) => TarMembersSorted(bundle.tar_members)

\* Valid bundle TAR has no duplicate names
BundleTarNoDuplicates(bundle) ==
    ValidBundle(bundle) => NoDuplicateNames(bundle.tar_members)

\* Combined bundle invariant
BundleInvariant(bundle) ==
    ValidBundle(bundle) =>
        /\ BundleNoExternalHandles(bundle)
        /\ BundleHasAllRequiredKeys(bundle)
        /\ BundleTarSorted(bundle)
        /\ BundleTarNoDuplicates(bundle)

(****************************************************************************)
(* Config Tags from Bundle                                                   *)
(* The 17 config_tags extracted from bundle for StateDigest                 *)
(****************************************************************************)

\* Extract config_tags sequence from bundle registry
\* Uses same ordering as Registry.ComputeConfigTags
BundleConfigTags(bundle) ==
    ComputeConfigTags(bundle.registry)

\* Config tags are deterministic
BundleConfigTagsDeterministic(b1, b2) ==
    b1.registry = b2.registry =>
        BundleConfigTags(b1) = BundleConfigTags(b2)

====
