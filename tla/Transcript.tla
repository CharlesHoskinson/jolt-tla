(****************************************************************************)
(* Module: Transcript.tla                                                   *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE Transcript ----
(****************************************************************************)
(* Purpose: Fiat-Shamir transcript state machine (Poseidon sponge)          *)
(* Appendix J Reference: J.7 (Transcript specification)                     *)
(* Version: 1.0                                                             *)
(* Notes: Uses heterogeneous union pattern (disjunction, not set union).    *)
(****************************************************************************)
EXTENDS Hash, Sequences, Naturals

(****************************************************************************)
(* CONSTANTS                                                                 *)
(****************************************************************************)

CONSTANTS
    MAX_ABSORPTIONS     \* TLC bound: maximum absorptions in a transcript

ASSUME MAX_ABSORPTIONS \in Nat /\ MAX_ABSORPTIONS > 0

(****************************************************************************)
(* Challenge sentinel                                                       *)
(* Before squeezing, no challenge value exists; we model this explicitly.   *)
(* Using -1 as sentinel since Fr = 0..(FR_TLC_BOUND-1) doesn't include -1   *)
(****************************************************************************)

CHALLENGE_UNSET == -1
ChallengeValue == Fr \cup {CHALLENGE_UNSET}

(****************************************************************************)
(* Transcript Type Tags (§8.4)                                              *)
(* These are Fr discriminator values used for domain separation             *)
(* Matches Lean Jolt/Transcript/Types.lean                                  *)
(****************************************************************************)

\* Per spec §8.4: type discriminators are Fr values, not strings
TYPE_BYTES_FR == 1   \* For absorb_bytes operations
TYPE_U64_FR == 2     \* For absorb_u64 operations
TYPE_TAG_FR == 3     \* For absorb_tag operations
TYPE_VEC_FR == 4     \* For absorb_vec operations

TranscriptTypeTags == {TYPE_BYTES_FR, TYPE_U64_FR, TYPE_TAG_FR, TYPE_VEC_FR}

(****************************************************************************)
(* Absorption Types (semantic categorization)                               *)
(* These classify what KIND of data is being absorbed                       *)
(****************************************************************************)

\* Absorption type tags for semantic separation
\* Use TAG_TRANSCRIPT_VM_STATE from Hash.tla for proper domain alignment
ABSORB_TYPE_VM_STATE == TAG_TRANSCRIPT_VM_STATE
ABSORB_TYPE_COMMITMENT == "commitment"
ABSORB_TYPE_CONFIG == "config"
ABSORB_TYPE_PROGRAM_HASH == "program_hash"
ABSORB_TYPE_NONCE == "nonce"
ABSORB_TYPE_TAG == "tag"  \* For domain tag absorption (J.7)

AbsorptionTypes == {
    ABSORB_TYPE_VM_STATE,
    ABSORB_TYPE_COMMITMENT,
    ABSORB_TYPE_CONFIG,
    ABSORB_TYPE_PROGRAM_HASH,
    ABSORB_TYPE_NONCE,
    ABSORB_TYPE_TAG
}

\* An absorption entry: semantic type + Fr type tag + value
\* The fr_type_tag is what actually gets absorbed (per §8.4)
AbsorptionEntry == [type: AbsorptionTypes, fr_type_tag: TranscriptTypeTags, value: Fr]

(****************************************************************************)
(* Transcript State                                                          *)
(* We model transcript as sequence of typed absorptions                      *)
(****************************************************************************)

\* Transcript phases
PHASE_ABSORBING == "absorbing"
PHASE_SQUEEZED == "squeezed"

TranscriptPhase == {PHASE_ABSORBING, PHASE_SQUEEZED}

\* Transcript state record
TranscriptState == [
    absorptions: Seq(AbsorptionEntry),  \* Ordered sequence of absorbed values
    phase: TranscriptPhase,              \* Current phase
    challenge: ChallengeValue            \* Squeezed challenge (valid after squeeze)
]

(****************************************************************************)
(* Initial Transcript State                                                  *)
(****************************************************************************)

InitTranscript == [
    absorptions |-> << >>,
    phase |-> PHASE_ABSORBING,
    challenge |-> CHALLENGE_UNSET  \* No challenge until squeeze
]

(****************************************************************************)
(* Transcript Operations                                                     *)
(****************************************************************************)

\* Absorb a typed value into the transcript with Fr type discriminator
\* Precondition: transcript is in absorbing phase
\* Per §8.4: the fr_type_tag is absorbed as part of domain separation
TranscriptAbsorb(transcript, absorbType, frTypeTag, value) ==
    IF transcript.phase # PHASE_ABSORBING
    THEN transcript  \* No-op if already squeezed (error in real impl)
    ELSE IF Len(transcript.absorptions) >= MAX_ABSORPTIONS
         THEN transcript  \* TLC bound reached
         ELSE [transcript EXCEPT
             !.absorptions = Append(@, [
                 type |-> absorbType,
                 fr_type_tag |-> frTypeTag,
                 value |-> value
             ])
         ]

\* AbsorbU64: Absorb a u64 value (uses TYPE_U64_FR discriminator)
\* Per §8.4: absorb_u64(x) = absorb_fr(TYPE_U64), absorb_fr(x)
AbsorbU64(transcript, absorbType, u64Value) ==
    TranscriptAbsorb(transcript, absorbType, TYPE_U64_FR, u64Value % FR_TLC_BOUND)

\* AbsorbBytes: Absorb bytes (uses TYPE_BYTES_FR discriminator)
\* Per §8.4: absorb_bytes(b) = absorb_fr(TYPE_BYTES), absorb_u64(len), absorb chunks
\* Simplified for TLC: absorb as single Fr fingerprint
AbsorbBytes(transcript, absorbType, bytesFingerprint) ==
    TranscriptAbsorb(transcript, absorbType, TYPE_BYTES_FR, bytesFingerprint)

\* Absorb a VM state digest (Fr) into transcript
\* VMState digest is already Fr, so use TYPE_U64_FR (single element)
AbsorbVMState(transcript, stateDigestFr) ==
    TranscriptAbsorb(transcript, ABSORB_TYPE_VM_STATE, TYPE_U64_FR, stateDigestFr)

\* Absorb a commitment (Fr) into transcript
AbsorbCommitment(transcript, commitmentFr) ==
    TranscriptAbsorb(transcript, ABSORB_TYPE_COMMITMENT, TYPE_U64_FR, commitmentFr)

\* Absorb configuration digest into transcript
AbsorbConfig(transcript, configDigestFr) ==
    TranscriptAbsorb(transcript, ABSORB_TYPE_CONFIG, TYPE_U64_FR, configDigestFr)

\* Absorb program hash (as bytes) into transcript
\* Program hash is Bytes32, so use TYPE_BYTES_FR
AbsorbProgramHash(transcript, programHashFingerprint) ==
    TranscriptAbsorb(transcript, ABSORB_TYPE_PROGRAM_HASH, TYPE_BYTES_FR, programHashFingerprint)

\* Absorb nonce (as u64) into transcript
AbsorbNonce(transcript, nonceFr) ==
    TranscriptAbsorb(transcript, ABSORB_TYPE_NONCE, TYPE_U64_FR, nonceFr)

\* AbsorbTag: Domain-separated tag absorption (uses TYPE_TAG_FR)
\* Per §8.6: absorb_tag validates format, then absorbs with TYPE_TAG discriminator
\* This is used by StateDigestV1 algorithm (J.10.10.2 steps 2, 11, 13)
AbsorbTag(transcript, tagString) ==
    LET \* Convert tag string to Fr fingerprint
        tagFr == Len(tagString)  \* Simplified for TLC
    IN TranscriptAbsorb(transcript, ABSORB_TYPE_TAG, TYPE_TAG_FR, tagFr)

(****************************************************************************)
(* Squeeze Operation                                                         *)
(* Finalize transcript and derive challenge                                  *)
(****************************************************************************)

\* Serialize absorptions for hashing
\* Creates a numeric encoding that preserves uniqueness
\* Different absorption sequences MUST produce different values
\* Per §8.4: fr_type_tag is part of the absorption, so include it in encoding
RECURSIVE EncodeAbsorptions(_, _)
EncodeAbsorptions(absorptions, idx) ==
    IF idx > Len(absorptions) THEN 0
    ELSE LET entry == absorptions[idx]
             \* Each absorption: [type |-> String, fr_type_tag |-> Fr, value |-> Fr]
             \* Include fr_type_tag in encoding for proper domain separation
             typeContrib == entry.fr_type_tag * 100
             valueContrib == entry.value
             entryVal == typeContrib + valueContrib
         IN entryVal * (1000 ^ idx) + EncodeAbsorptions(absorptions, idx + 1)

SerializeAbsorptions(absorptions) ==
    EncodeAbsorptions(absorptions, 1)

\* Compute challenge from absorption sequence
\* Uses domain-separated Poseidon hash
ComputeChallenge(absorptions) ==
    PoseidonHashV1(TAG_TRANSCRIPT_CHALLENGE, SerializeAbsorptions(absorptions))

\* Squeeze the transcript to get a challenge
\* Transitions from ABSORBING to SQUEEZED phase
TranscriptSqueeze(transcript) ==
    IF transcript.phase # PHASE_ABSORBING
    THEN transcript  \* Already squeezed
    ELSE [transcript EXCEPT
        !.phase = PHASE_SQUEEZED,
        !.challenge = ComputeChallenge(transcript.absorptions)
    ]

\* Get the challenge (only valid after squeeze)
GetChallenge(transcript) ==
    IF transcript.phase = PHASE_SQUEEZED
    THEN transcript.challenge
    ELSE CHALLENGE_UNSET  \* Invalid; should check phase first

(****************************************************************************)
(* Transcript Predicates                                                     *)
(****************************************************************************)

\* Is the transcript in absorbing phase?
IsAbsorbing(transcript) == transcript.phase = PHASE_ABSORBING

\* Is the transcript finalized (squeezed)?
IsSqueezed(transcript) == transcript.phase = PHASE_SQUEEZED

\* How many values have been absorbed?
AbsorptionCount(transcript) == Len(transcript.absorptions)

\* Has a specific type been absorbed?
HasAbsorbedType(transcript, absorbType) ==
    \E i \in 1..Len(transcript.absorptions) :
        transcript.absorptions[i].type = absorbType

(****************************************************************************)
(* Transcript Type Invariant                                                 *)
(****************************************************************************)

TranscriptTypeOK(transcript) ==
    /\ transcript.absorptions \in Seq(AbsorptionEntry)
    /\ Len(transcript.absorptions) <= MAX_ABSORPTIONS
    /\ transcript.phase \in TranscriptPhase
    \* Pattern: rewrite (x \in A \cup B) as disjunction to avoid building heterogeneous set
    /\ (transcript.challenge \in Fr) \/ (transcript.challenge = CHALLENGE_UNSET)
    /\ (transcript.phase = PHASE_ABSORBING => transcript.challenge = CHALLENGE_UNSET)
    /\ (transcript.phase = PHASE_SQUEEZED => transcript.challenge \in Fr)


(****************************************************************************)
(* Transcript Safety Invariants                                              *)
(****************************************************************************)

\* Once squeezed, absorptions cannot change
TranscriptImmutableAfterSqueeze(transcript, transcript_next) ==
    transcript.phase = PHASE_SQUEEZED =>
        /\ transcript_next.absorptions = transcript.absorptions
        /\ transcript_next.challenge = transcript.challenge

\* Challenge is deterministic: same absorptions -> same challenge
TranscriptDeterministic ==
    \A t1, t2 \in TranscriptState :
        (t1.absorptions = t2.absorptions /\ IsSqueezed(t1) /\ IsSqueezed(t2))
        => t1.challenge = t2.challenge

\* Absorption order matters: different orders -> different challenges
\* (This follows from hash properties, stated for documentation)
AbsorptionOrderMatters ==
    \A abs1, abs2 \in Seq(AbsorptionEntry) :
        abs1 # abs2 => ComputeChallenge(abs1) # ComputeChallenge(abs2)

(****************************************************************************)
(* Transcript Binding Property                                               *)
(* The challenge cryptographically binds all absorbed values                 *)
(****************************************************************************)

\* If two transcripts have the same challenge, they absorbed the same values
\* (Follows from hash collision resistance)
TranscriptBindingProperty ==
    \A t1, t2 \in TranscriptState :
        (IsSqueezed(t1) /\ IsSqueezed(t2) /\ t1.challenge = t2.challenge)
        => t1.absorptions = t2.absorptions

(****************************************************************************)
(* Helper: Build transcript from sequence of typed values                    *)
(* Useful for specification of expected transcript construction              *)
(****************************************************************************)

RECURSIVE BuildTranscriptRec(_, _)
BuildTranscriptRec(entries, transcript) ==
    IF entries = << >>
    THEN transcript
    ELSE
        LET
            entry == Head(entries)
            \* Entry has: type, fr_type_tag, value
            updated == TranscriptAbsorb(transcript, entry.type, entry.fr_type_tag, entry.value)
        IN
            BuildTranscriptRec(Tail(entries), updated)

BuildTranscript(entries) == BuildTranscriptRec(entries, InitTranscript)

\* Build and squeeze in one operation
BuildAndSqueeze(entries) == TranscriptSqueeze(BuildTranscript(entries))

====
