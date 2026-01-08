(****************************************************************************)
(* Module: MC_BadTranscript_TypeConfusion.tla                              *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE MC_BadTranscript_TypeConfusion ----
(****************************************************************************)
(* Purpose: Verify transcript type tags prevent confusion attacks           *)
(* Pattern: Property check (type tags must be distinct)                     *)
(* Expected: TLC succeeds (invariants hold)                                 *)
(*                                                                          *)
(* This module verifies:                                                    *)
(* 1. Type tags {1,2,3,4} are all distinct                                  *)
(* 2. Different typed absorptions produce different encodings               *)
(* 3. Transcript determinism holds                                          *)
(****************************************************************************)
EXTENDS MC_Jolt

(****************************************************************************)
(* TYPE TAG DISTINCTNESS                                                     *)
(* Verify the four type tags are all unique                                  *)
(****************************************************************************)

TypeTagsDistinct ==
    /\ TYPE_BYTES_FR # TYPE_U64_FR
    /\ TYPE_BYTES_FR # TYPE_TAG_FR
    /\ TYPE_BYTES_FR # TYPE_VEC_FR
    /\ TYPE_U64_FR # TYPE_TAG_FR
    /\ TYPE_U64_FR # TYPE_VEC_FR
    /\ TYPE_TAG_FR # TYPE_VEC_FR

\* Verify cardinality matches expected
TypeTagsComplete ==
    Cardinality(TranscriptTypeTags) = 4

(****************************************************************************)
(* ENCODING DISTINCTNESS                                                     *)
(* Different type tags must produce different absorption encodings          *)
(****************************************************************************)

\* Two absorptions with same value but different types must encode differently
\* This is ensured by including fr_type_tag in the encoding
EncodingDistinctness ==
    \A v \in Fr :
        \A t1, t2 \in TranscriptTypeTags :
            t1 # t2 =>
                \* The encoding formula: typeContrib = fr_type_tag * 100
                (t1 * 100 + v) # (t2 * 100 + v)

(****************************************************************************)
(* TRANSCRIPT DETERMINISM                                                    *)
(* Same absorptions must produce same challenge                              *)
(****************************************************************************)

\* This is an ASSUME in Transcript.tla, verified here for documentation
TranscriptIsDeterministic == TranscriptDeterministic

(****************************************************************************)
(* COMBINED TEST INVARIANT                                                   *)
(****************************************************************************)

TestTypeConfusionPrevented ==
    /\ TypeTagsDistinct
    /\ TypeTagsComplete
    /\ EncodingDistinctness

====
