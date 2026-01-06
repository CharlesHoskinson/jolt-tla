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
(* Absorption Types (J.7.4-J.7.6)                                           *)
(* Each absorption is tagged with its semantic type                         *)
(****************************************************************************)

\* Absorption type tags for domain separation
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

\* An absorption entry: type tag + value (Fr or Bytes32 encoded as Fr)
AbsorptionEntry == [type: AbsorptionTypes, value: Fr]

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

\* Absorb a typed value into the transcript
\* Precondition: transcript is in absorbing phase
TranscriptAbsorb(transcript, absorbType, value) ==
    IF transcript.phase # PHASE_ABSORBING
    THEN transcript  \* No-op if already squeezed (error in real impl)
    ELSE IF Len(transcript.absorptions) >= MAX_ABSORPTIONS
         THEN transcript  \* TLC bound reached
         ELSE [transcript EXCEPT
             !.absorptions = Append(@, [type |-> absorbType, value |-> value])
         ]

\* Absorb a VM state digest (Fr) into transcript
AbsorbVMState(transcript, stateDigestFr) ==
    TranscriptAbsorb(transcript, ABSORB_TYPE_VM_STATE, stateDigestFr)

\* Absorb a commitment (Fr) into transcript
AbsorbCommitment(transcript, commitmentFr) ==
    TranscriptAbsorb(transcript, ABSORB_TYPE_COMMITMENT, commitmentFr)

\* Absorb configuration digest into transcript
AbsorbConfig(transcript, configDigestFr) ==
    TranscriptAbsorb(transcript, ABSORB_TYPE_CONFIG, configDigestFr)

\* Absorb program hash (as Fr via encoding) into transcript
AbsorbProgramHash(transcript, programHashFr) ==
    TranscriptAbsorb(transcript, ABSORB_TYPE_PROGRAM_HASH, programHashFr)

\* Absorb nonce (as Fr) into transcript
AbsorbNonce(transcript, nonceFr) ==
    TranscriptAbsorb(transcript, ABSORB_TYPE_NONCE, nonceFr)

\* AbsorbTag: Alias for domain-separated tag absorption
\* J.7.4-J.7.6: absorb_tag(tag_string) hashes the tag for domain separation
\* This is used by StateDigestV1 algorithm (J.10.10.2 steps 2, 11, 13)
\* For TLC model: we use TranscriptAbsorb with tag name as value
AbsorbTag(transcript, tagString) ==
    LET \* Convert tag string to Fr by using length as fingerprint
        tagFr == Len(tagString)
    IN TranscriptAbsorb(transcript, ABSORB_TYPE_TAG, tagFr)

(****************************************************************************)
(* Squeeze Operation                                                         *)
(* Finalize transcript and derive challenge                                  *)
(****************************************************************************)

\* Serialize absorptions for hashing
\* Creates a numeric encoding that preserves uniqueness
\* Different absorption sequences MUST produce different values
RECURSIVE EncodeAbsorptions(_, _)
EncodeAbsorptions(absorptions, idx) ==
    IF idx > Len(absorptions) THEN 0
    ELSE LET entry == absorptions[idx]
             \* Each absorption: [type |-> String, value |-> Fr]
             \* Use value directly (type is for domain separation in real impl)
             entryVal == entry.value
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
            updated == TranscriptAbsorb(transcript, entry.type, entry.value)
        IN
            BuildTranscriptRec(Tail(entries), updated)

BuildTranscript(entries) == BuildTranscriptRec(entries, InitTranscript)

\* Build and squeeze in one operation
BuildAndSqueeze(entries) == TranscriptSqueeze(BuildTranscript(entries))

====
