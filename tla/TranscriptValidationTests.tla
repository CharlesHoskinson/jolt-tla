(****************************************************************************)
(* Module: TranscriptValidationTests.tla                                    *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE TranscriptValidationTests ----
(****************************************************************************)
(* Purpose: Test cases for Fiat-Shamir transcript validation                *)
(* Section Reference: J.7 (Transcript), §8.4 (Type tags), §8.6 (Tag format) *)
(* Version: 1.0                                                             *)
(* Notes: These operators return TRUE if the test passes.                   *)
(*        Run with TLC to verify all tests pass.                            *)
(****************************************************************************)
EXTENDS Transcript, TLC

(****************************************************************************)
(* Type Tag Tests (§8.4)                                                     *)
(****************************************************************************)

\* Test: type tags are distinct Fr values
TestTypeTagsDistinct ==
    /\ TYPE_BYTES_FR # TYPE_U64_FR
    /\ TYPE_BYTES_FR # TYPE_TAG_FR
    /\ TYPE_BYTES_FR # TYPE_VEC_FR
    /\ TYPE_U64_FR # TYPE_TAG_FR
    /\ TYPE_U64_FR # TYPE_VEC_FR
    /\ TYPE_TAG_FR # TYPE_VEC_FR

\* Test: type tags are in expected range
TestTypeTagsInRange ==
    /\ TYPE_BYTES_FR = 1
    /\ TYPE_U64_FR = 2
    /\ TYPE_TAG_FR = 3
    /\ TYPE_VEC_FR = 4

\* Test: TranscriptTypeTags set matches constants
TestTypeTagsSetComplete ==
    TranscriptTypeTags = {1, 2, 3, 4}

(****************************************************************************)
(* Initial Transcript Tests                                                  *)
(****************************************************************************)

\* Test: initial transcript is in absorbing phase
TestInitTranscriptAbsorbing ==
    IsAbsorbing(InitTranscript)

\* Test: initial transcript has no absorptions
TestInitTranscriptEmpty ==
    AbsorptionCount(InitTranscript) = 0

\* Test: initial transcript has unset challenge
TestInitTranscriptNoChallenge ==
    InitTranscript.challenge = CHALLENGE_UNSET

\* Test: initial transcript type is OK
TestInitTranscriptTypeOK ==
    TranscriptTypeOK(InitTranscript)

(****************************************************************************)
(* Absorption Tests                                                          *)
(****************************************************************************)

\* Test: absorbing increments count
TestAbsorbIncrementsCount ==
    LET t1 == TranscriptAbsorb(InitTranscript, ABSORB_TYPE_VM_STATE, TYPE_U64_FR, 42)
    IN AbsorptionCount(t1) = 1

\* Test: different type tags produce different entries
TestDifferentTypeTagsDifferentEntries ==
    LET t_u64 == TranscriptAbsorb(InitTranscript, ABSORB_TYPE_VM_STATE, TYPE_U64_FR, 42)
        t_bytes == TranscriptAbsorb(InitTranscript, ABSORB_TYPE_VM_STATE, TYPE_BYTES_FR, 42)
    IN t_u64.absorptions[1].fr_type_tag # t_bytes.absorptions[1].fr_type_tag

\* Test: same value with different semantic types are distinct
TestDifferentAbsorbTypesDifferent ==
    LET t_vm == TranscriptAbsorb(InitTranscript, ABSORB_TYPE_VM_STATE, TYPE_U64_FR, 100)
        t_commit == TranscriptAbsorb(InitTranscript, ABSORB_TYPE_COMMITMENT, TYPE_U64_FR, 100)
    IN t_vm.absorptions[1].type # t_commit.absorptions[1].type

\* Test: AbsorbU64 uses TYPE_U64_FR
TestAbsorbU64UsesCorrectTag ==
    LET t == AbsorbU64(InitTranscript, ABSORB_TYPE_NONCE, 12345)
    IN t.absorptions[1].fr_type_tag = TYPE_U64_FR

\* Test: AbsorbBytes uses TYPE_BYTES_FR
TestAbsorbBytesUsesCorrectTag ==
    LET t == AbsorbBytes(InitTranscript, ABSORB_TYPE_PROGRAM_HASH, 0)
    IN t.absorptions[1].fr_type_tag = TYPE_BYTES_FR

\* Test: AbsorbTag uses TYPE_TAG_FR
TestAbsorbTagUsesCorrectTag ==
    LET t == AbsorbTag(InitTranscript, "JOLT/TEST/V1")
    IN t.absorptions[1].fr_type_tag = TYPE_TAG_FR

(****************************************************************************)
(* Squeeze Tests                                                             *)
(****************************************************************************)

\* Test: squeezing changes phase
TestSqueezeChangesPhase ==
    LET t == TranscriptSqueeze(InitTranscript)
    IN IsSqueezed(t)

\* Test: squeezed transcript has valid challenge
TestSqueezedHasChallenge ==
    LET t == TranscriptSqueeze(InitTranscript)
    IN t.challenge \\in Fr

\* Test: squeezing absorbed transcript produces valid challenge
TestSqueezedAbsorbedHasChallenge ==
    LET t1 == AbsorbVMState(InitTranscript, 42)
        t2 == TranscriptSqueeze(t1)
    IN t2.challenge \\in Fr

\* Test: squeeze is idempotent
TestSqueezeIdempotent ==
    LET t1 == TranscriptSqueeze(InitTranscript)
        t2 == TranscriptSqueeze(t1)
    IN t1 = t2

\* Test: absorbing after squeeze is no-op
TestAbsorbAfterSqueezeNoOp ==
    LET t1 == TranscriptSqueeze(InitTranscript)
        t2 == TranscriptAbsorb(t1, ABSORB_TYPE_VM_STATE, TYPE_U64_FR, 99)
    IN t1 = t2

(****************************************************************************)
(* Challenge Computation Tests                                               *)
(****************************************************************************)

\* Test: different absorptions produce different challenges
TestDifferentAbsorptionsDifferentChallenges ==
    LET t1 == TranscriptSqueeze(AbsorbU64(InitTranscript, ABSORB_TYPE_NONCE, 1))
        t2 == TranscriptSqueeze(AbsorbU64(InitTranscript, ABSORB_TYPE_NONCE, 2))
    IN GetChallenge(t1) # GetChallenge(t2)

\* Test: same absorptions produce same challenge (deterministic)
TestSameAbsorptionsSameChallenge ==
    LET t1 == TranscriptSqueeze(AbsorbU64(InitTranscript, ABSORB_TYPE_NONCE, 42))
        t2 == TranscriptSqueeze(AbsorbU64(InitTranscript, ABSORB_TYPE_NONCE, 42))
    IN GetChallenge(t1) = GetChallenge(t2)

\* Test: GetChallenge returns UNSET for unsqueezed
TestGetChallengeUnsqueezed ==
    GetChallenge(InitTranscript) = CHALLENGE_UNSET

(****************************************************************************)
(* Type Invariant Tests                                                      *)
(****************************************************************************)

\* Test: type invariant holds after absorptions
TestTypeOKAfterAbsorb ==
    LET t == AbsorbU64(InitTranscript, ABSORB_TYPE_NONCE, 100)
    IN TranscriptTypeOK(t)

\* Test: type invariant holds after squeeze
TestTypeOKAfterSqueeze ==
    LET t == TranscriptSqueeze(AbsorbU64(InitTranscript, ABSORB_TYPE_NONCE, 100))
    IN TranscriptTypeOK(t)

(****************************************************************************)
(* Tag Format Tests (§8.6)                                                   *)
(****************************************************************************)

\* Test: valid tags pass format check
TestValidTagFormatPasses ==
    /\ IsValidTagFormat("JOLT/SMT/PAGE/V1")
    /\ IsValidTagFormat("JOLT/TRANSCRIPT/CHALLENGE/V1")
    /\ IsValidTagFormat("JOLT/STATE/V1")

\* Test: invalid tags fail format check
TestInvalidTagFormatFails ==
    /\ ~IsValidTagFormat("")              \* Empty
    /\ ~IsValidTagFormat("JOLT")          \* Too short
    /\ ~IsValidTagFormat("OTHER/TEST/V1") \* Wrong prefix

\* Test: all centralized domain tags are valid
TestAllDomainTagsValid ==
    \A t \in ALL_DOMAIN_TAGS : IsValidTagFormat(t)

(****************************************************************************)
(* BuildTranscript Tests                                                     *)
(****************************************************************************)

\* Test: BuildTranscript from empty is InitTranscript
TestBuildTranscriptEmpty ==
    BuildTranscript(<< >>) = InitTranscript

\* Test: BuildTranscript adds entries correctly
TestBuildTranscriptAddsEntries ==
    LET entries == <<[type |-> ABSORB_TYPE_NONCE, fr_type_tag |-> TYPE_U64_FR, value |-> 1]>>
        t == BuildTranscript(entries)
    IN AbsorptionCount(t) = 1

\* Test: BuildAndSqueeze produces squeezed transcript
TestBuildAndSqueezeWorks ==
    LET entries == <<[type |-> ABSORB_TYPE_NONCE, fr_type_tag |-> TYPE_U64_FR, value |-> 42]>>
        t == BuildAndSqueeze(entries)
    IN IsSqueezed(t)

(****************************************************************************)
(* All Tests Pass                                                            *)
(****************************************************************************)

AllTranscriptTestsPass ==
    \* Type tag tests
    /\ TestTypeTagsDistinct
    /\ TestTypeTagsInRange
    /\ TestTypeTagsSetComplete
    \* Initial transcript tests
    /\ TestInitTranscriptAbsorbing
    /\ TestInitTranscriptEmpty
    /\ TestInitTranscriptNoChallenge
    /\ TestInitTranscriptTypeOK
    \* Absorption tests
    /\ TestAbsorbIncrementsCount
    /\ TestDifferentTypeTagsDifferentEntries
    /\ TestDifferentAbsorbTypesDifferent
    /\ TestAbsorbU64UsesCorrectTag
    /\ TestAbsorbBytesUsesCorrectTag
    /\ TestAbsorbTagUsesCorrectTag
    \* Squeeze tests
    /\ TestSqueezeChangesPhase
    /\ TestSqueezedHasChallenge
    /\ TestSqueezedAbsorbedHasChallenge
    /\ TestSqueezeIdempotent
    /\ TestAbsorbAfterSqueezeNoOp
    \* Challenge tests
    /\ TestDifferentAbsorptionsDifferentChallenges
    /\ TestSameAbsorptionsSameChallenge
    /\ TestGetChallengeUnsqueezed
    \* Type invariant tests
    /\ TestTypeOKAfterAbsorb
    /\ TestTypeOKAfterSqueeze
    \* Tag format tests
    /\ TestValidTagFormatPasses
    /\ TestInvalidTagFormatFails
    /\ TestAllDomainTagsValid
    \* BuildTranscript tests
    /\ TestBuildTranscriptEmpty
    /\ TestBuildTranscriptAddsEntries
    /\ TestBuildAndSqueezeWorks

\* Use this as INVARIANT in TLC to verify all tests pass
ASSUME AllTranscriptTestsPass

====
