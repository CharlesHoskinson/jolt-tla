(****************************************************************************)
(* Module: Hash.tla                                                         *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE Hash ----
(****************************************************************************)
(* Purpose: Cryptographic hash primitives as ideal functionalities          *)
(* Appendix J Reference: J.7 (Poseidon transcript), J.10.8.3 (SMT hash),    *)
(*                       J.4.7 (SHA-256 batch commitment)                   *)
(* Version: 1.0                                                             *)
(* Notes: Contains all 12 domain tags for Fiat-Shamir separation.           *)
(****************************************************************************)
EXTENDS Types, Encodings, FiniteSets

(****************************************************************************)
(* CONSTANTS                                                                 *)
(* Hash functions as uninterpreted constants with assumed properties        *)
(****************************************************************************)

CONSTANTS
    \* Domain separation tags (ASCII strings modeled as values)
    TAG_STRINGS,        \* Set of valid domain tags for TLC (finite)

    \* Poseidon hash: maps (tag, input) to Fr
    \* Actual signature: (String, Bytes) -> Fr
    PoseidonHashBytes(_, _),  \* (tag, data) -> Fr

    \* Poseidon hash for two Fr inputs (SMT internal nodes)
    \* Actual signature: (String, Fr, Fr) -> Fr
    PoseidonHashFr2(_, _, _), \* (tag, fr1, fr2) -> Fr

    \* SHA-256: maps bytes to Bytes32
    SHA256Hash(_)             \* (inputBytes) -> Bytes32

(****************************************************************************)
(* ASSUME: Collision resistance as injectivity within each domain           *)
(* NOTE: Unbounded quantifiers are documented properties, not TLC-checked   *)
(****************************************************************************)

\* TAG_STRINGS is a finite set for TLC
ASSUME IsFiniteSet(TAG_STRINGS)
ASSUME TAG_STRINGS # {}

\* Output type assumptions (ideal functionality - documented, not TLC-checked)
\* PROPERTY: \A tag \in TAG_STRINGS : \A data : PoseidonHashBytes(tag, data) \in Fr
\* PROPERTY: \A tag \in TAG_STRINGS : \A fr1, fr2 \in Fr : PoseidonHashFr2(tag, fr1, fr2) \in Fr
\* PROPERTY: \A input : SHA256Hash(input) \in Bytes32

\* Poseidon over bytes is injective within each tag domain (ideal functionality)
\* PROPERTY: \A tag \in TAG_STRINGS : \A x, y : PoseidonHashBytes(tag, x) = PoseidonHashBytes(tag, y) => x = y

\* Poseidon over Fr pairs is injective within each tag domain
\* PROPERTY: \A tag \in TAG_STRINGS : \A a1, a2, b1, b2 \in Fr :
\*     PoseidonHashFr2(tag, a1, a2) = PoseidonHashFr2(tag, b1, b2) => (a1 = b1 /\ a2 = b2)

\* SHA-256 is injective (collision resistant)
\* PROPERTY: \A x, y : SHA256Hash(x) = SHA256Hash(y) => x = y

\* Domain separation: different tags produce different hash functions
\* PROPERTY: \A tag1, tag2 \in TAG_STRINGS : tag1 # tag2 =>
\*     \A x : PoseidonHashBytes(tag1, x) # PoseidonHashBytes(tag2, x)

(****************************************************************************)
(* Domain Tags (J.7.7, J.10.8.3, J.4.7)                                     *)
(* These are the actual ASCII tags used in Appendix J                       *)
(****************************************************************************)

\* SMT tags (J.10.8.3)
TAG_SMT_PAGE == "JOLT/SMT/PAGE/V1"
TAG_SMT_NODE == "JOLT/SMT/NODE/V1"

\* Transcript tags (J.7)
TAG_TRANSCRIPT_VM_STATE == "JOLT/TRANSCRIPT/VM_STATE/V1"
TAG_TRANSCRIPT_CHALLENGE == "JOLT/TRANSCRIPT/CHALLENGE/V1"
TAG_TRANSCRIPT_DOMAIN == "JOLT/TRANSCRIPT/V1"  \* Domain tag for transcript initialization

\* Batch commitment tags (J.4.7)
TAG_BATCH_HEADER_LEAF == "JOLT/BATCH/HEADER_LEAF/V1"
TAG_BATCH_FILL_LEAF == "JOLT/BATCH/FILL_LEAF/V1"
TAG_BATCH_EMPTY_FILL_LEAF == "JOLT/BATCH/EMPTY_FILL_LEAF/V1"
TAG_BATCH_PAD_LEAF == "JOLT/BATCH/PAD_LEAF/V1"
TAG_BATCH_NODE == "JOLT/BATCH/NODE/V1"

\* StateDigest tag (J.10.10) - domain separator for state digests
TAG_STATE_DIGEST == "JOLT/STATE/V1"

\* Checkpoints tag (J.4.8)
TAG_CHECKPOINTS == "JOLT/CHECKPOINTS/V1"

\* Config tags domain separator (J.10.10.2 step 11)
\* Used when absorbing config_tags in StateDigestV1 algorithm
TAG_CONFIG_TAGS == "JOLT/CONFIG_TAGS/V1"

\* Individual tag domain separator (J.10.10.2 step 13)
\* Used for each (tag_name, tag_value) pair in config_tags
TAG_TAG == "JOLT/TAG/V1"

\* All domain tags defined in this module.
ALL_DOMAIN_TAGS ==
    { TAG_SMT_PAGE,
      TAG_SMT_NODE,
      TAG_TRANSCRIPT_VM_STATE,
      TAG_TRANSCRIPT_CHALLENGE,
      TAG_TRANSCRIPT_DOMAIN,
      TAG_BATCH_HEADER_LEAF,
      TAG_BATCH_FILL_LEAF,
      TAG_BATCH_EMPTY_FILL_LEAF,
      TAG_BATCH_PAD_LEAF,
      TAG_BATCH_NODE,
      TAG_STATE_DIGEST,
      TAG_CHECKPOINTS,
      TAG_CONFIG_TAGS,
      TAG_TAG }

ASSUME ALL_DOMAIN_TAGS \subseteq TAG_STRINGS

(****************************************************************************)
(* Poseidon Hash Operators (J.7.7)                                          *)
(* Domain-separated Poseidon returning Fr                                   *)
(****************************************************************************)

\* PoseidonHashV1: Hash bytes with domain tag, return Fr
\* J.7.7: "PoseidonHashV1(tag, data) := ..."
PoseidonHashV1(tag, data) == PoseidonHashBytes(tag, data)

\* PoseidonHashFr2V1: Hash two Fr values with domain tag, return Fr
\* J.10.8.3: "node_fr(left_fr, right_fr) := PoseidonHashFr2V1(...)"
PoseidonHashFr2V1(tag, fr1, fr2) == PoseidonHashFr2(tag, fr1, fr2)

(****************************************************************************)
(* SHA-256 Operators (J.4.7)                                                *)
(* For batch commitment Merkle tree                                         *)
(****************************************************************************)

\* SHA256 with domain separation via tag prefix
\* J.4.7: "LeafHash(tag_ascii, payload) := SHA-256( UTF8(tag_ascii) || 0x00 || payload )"
SHA256WithTag(tag, payload) ==
    \* Model: tag || 0x00 || payload concatenation abstracted
    \* The actual byte concatenation is handled by assuming SHA256Hash
    \* takes the full input including tag prefix
    SHA256Hash(<<tag, payload>>)

\* Node hash for batch Merkle tree (J.4.7)
\* "NodeHash(left32, right32) := SHA-256( b"JOLT/BATCH/NODE/V1\0" || left32 || right32 )"
BatchNodeHash(left32, right32) ==
    SHA256WithTag(TAG_BATCH_NODE, <<left32, right32>>)

\* Leaf hash for batch Merkle tree
BatchLeafHash(tag, payload) == SHA256WithTag(tag, payload)

(****************************************************************************)
(* SMT Hash Operators (J.10.8.3)                                            *)
(* Sparse Merkle Tree hashing for memory commitments                        *)
(****************************************************************************)

\* Leaf hash: 4096-byte page -> Fr
\* J.10.8.3: "leaf_fr(page_bytes4096) := PoseidonHashV1("JOLT/SMT/PAGE/V1", page_bytes4096)"
SMTLeafHash(pageBytes) == PoseidonHashV1(TAG_SMT_PAGE, pageBytes)

\* Node hash: two Fr children -> Fr
\* J.10.8.3: "node_fr(left_fr, right_fr) := PoseidonHashFr2V1("JOLT/SMT/NODE/V1", ...)"
SMTNodeHash(leftFr, rightFr) == PoseidonHashFr2V1(TAG_SMT_NODE, leftFr, rightFr)

(****************************************************************************)
(* StateDigest Hash (J.10.10)                                               *)
(****************************************************************************)

\* StateDigest uses Poseidon over the serialized VM state + config
\* Detailed construction is in the Continuations module
StateDigestHash(serializedState) == PoseidonHashV1(TAG_STATE_DIGEST, serializedState)

(****************************************************************************)
(* Checkpoints Hash (J.4.8)                                                 *)
(****************************************************************************)

\* checkpoints_digest_fr := PoseidonHashV1("JOLT/CHECKPOINTS/V1", checkpoints_bytes)
CheckpointsDigestHash(checkpointsBytes) == PoseidonHashV1(TAG_CHECKPOINTS, checkpointsBytes)

(****************************************************************************)
(* Hash Output Type Predicates                                               *)
(****************************************************************************)

\* Poseidon outputs are in Fr
IsPoseidonOutput(x) == x \in Fr

\* SHA-256 outputs are Bytes32
IsSHA256Output(x) == x \in Bytes32

(****************************************************************************)
(* Hash Invariants (documented properties - unbounded, not TLC-checked)     *)
(****************************************************************************)

\* All Poseidon outputs are valid Fr elements
\* PROPERTY: \A tag \in TAG_STRINGS, data : PoseidonHashV1(tag, data) \in Fr

\* All SMT hashes produce Fr
\* PROPERTY: \A page : SMTLeafHash(page) \in Fr
\* PROPERTY: \A l, r \in Fr : SMTNodeHash(l, r) \in Fr

====
