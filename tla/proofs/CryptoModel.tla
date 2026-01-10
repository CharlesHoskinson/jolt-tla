(****************************************************************************)
(* Module: CryptoModel.tla                                                  *)
(* Purpose: Minimal ideal-hash interface with tagged constructors           *)
(* Part of: Unbounded/infinite-state verification for Jolt                  *)
(* Reference: ASSUMPTIONS.md CRYPTO-01, CRYPTO-02                           *)
(****************************************************************************)
---- MODULE CryptoModel ----
(****************************************************************************)
(* This module provides a typed preimage domain with tagged constructors    *)
(* to ensure disjoint preimage domains. The key axiom HInjectiveOnCritical  *)
(* scopes hash injectivity to security-critical encodings only.             *)
(*                                                                          *)
(* Tagged constructors:                                                     *)
(*   TB(tag, x)  - Tag-Bytes encoding (domain separation)                   *)
(*   SE(enc)     - State encoding (StateDigest)                             *)
(*   TR(enc)     - Transcript encoding (Fiat-Shamir)                        *)
(*                                                                          *)
(* The outer tuple tag ("TB", "SE", "TR") guarantees disjointness.          *)
(****************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

(****************************************************************************)
(* CONSTANTS: Abstract domains                                               *)
(****************************************************************************)

CONSTANTS
    Tag,                \* Set of domain tags (strings like "JOLT/STATE/V1")
    Bytes,              \* Set of byte sequences
    StateEncoding,      \* Set of valid state encodings
    TranscriptEncoding, \* Set of valid transcript encodings
    Digest              \* Set of hash outputs (Fr elements)

(****************************************************************************)
(* ASSUME: Domain sets are non-empty                                         *)
(****************************************************************************)

ASSUME Tag # {}
ASSUME Digest # {}

(****************************************************************************)
(* Tagged Constructors                                                       *)
(* Outer tag ensures DISJOINT preimage domains                               *)
(****************************************************************************)

\* Tag-Bytes encoding: for domain-separated Poseidon
TB(tag, x) == << "TB", tag, x >>

\* State encoding: for StateDigest computation
SE(enc) == << "SE", enc >>

\* Transcript encoding: for Fiat-Shamir transcript
TR(enc) == << "TR", enc >>

(****************************************************************************)
(* Preimage Domain: Union of all tagged constructors                         *)
(****************************************************************************)

\* Full preimage is union of tagged constructors - guaranteed disjoint by outer tag
Preimage == { TB(tag, x) : tag \in Tag, x \in Bytes }
         \cup { SE(e) : e \in StateEncoding }
         \cup { TR(e) : e \in TranscriptEncoding }

\* Critical preimage: ALL encodings used for security-critical binding
\* IMPORTANT: TB is included so DomainSeparation can be derived from HInjectiveOnCritical
\* See ASSUMPTIONS.md CRYPTO-01 for justification
CriticalPreimage == Preimage

(****************************************************************************)
(* Hash Function: Ideal functionality                                        *)
(****************************************************************************)

CONSTANT H

\* H is a total function from Preimage to Digest
ASSUME H \in [Preimage -> Digest]

(****************************************************************************)
(* AXIOM: Injectivity scoped to CriticalPreimage                             *)
(* This is the ONLY cryptographic assumption.                                *)
(* See ASSUMPTIONS.md CRYPTO-01                                              *)
(****************************************************************************)

AXIOM HInjectiveOnCritical ==
    \A p1, p2 \in CriticalPreimage : H[p1] = H[p2] => p1 = p2

(****************************************************************************)
(* Constructor Injectivity Lemmas (pure structural - no crypto)              *)
(* These follow from tuple structure, not hash properties                    *)
(****************************************************************************)

\* TB is injective: equal outputs imply equal inputs
LEMMA TBInjective ==
    \A t1, t2 \in Tag, x1, x2 \in Bytes :
        TB(t1, x1) = TB(t2, x2) => t1 = t2 /\ x1 = x2
<1>1. TAKE t1 \in Tag, t2 \in Tag, x1 \in Bytes, x2 \in Bytes
<1>2. ASSUME TB(t1, x1) = TB(t2, x2)
<1>3. << "TB", t1, x1 >> = << "TB", t2, x2 >>
      BY <1>2 DEF TB
<1>4. t1 = t2 /\ x1 = x2
      BY <1>3  \* Tuple equality
<1>5. QED BY <1>4

\* SE is injective
LEMMA SEInjective ==
    \A e1, e2 \in StateEncoding : SE(e1) = SE(e2) => e1 = e2
<1>1. TAKE e1 \in StateEncoding, e2 \in StateEncoding
<1>2. ASSUME SE(e1) = SE(e2)
<1>3. << "SE", e1 >> = << "SE", e2 >>
      BY <1>2 DEF SE
<1>4. e1 = e2
      BY <1>3  \* Tuple equality
<1>5. QED BY <1>4

\* TR is injective
LEMMA TRInjective ==
    \A e1, e2 \in TranscriptEncoding : TR(e1) = TR(e2) => e1 = e2
<1>1. TAKE e1 \in TranscriptEncoding, e2 \in TranscriptEncoding
<1>2. ASSUME TR(e1) = TR(e2)
<1>3. << "TR", e1 >> = << "TR", e2 >>
      BY <1>2 DEF TR
<1>4. e1 = e2
      BY <1>3  \* Tuple equality
<1>5. QED BY <1>4

(****************************************************************************)
(* Constructor Disjointness Lemma                                            *)
(* Different outer tags guarantee different preimages                        *)
(****************************************************************************)

LEMMA ConstructorDisjoint ==
    /\ \A t \in Tag, x \in Bytes, e \in StateEncoding : TB(t, x) # SE(e)
    /\ \A t \in Tag, x \in Bytes, e \in TranscriptEncoding : TB(t, x) # TR(e)
    /\ \A e1 \in StateEncoding, e2 \in TranscriptEncoding : SE(e1) # TR(e2)
<1>1. \A t \in Tag, x \in Bytes, e \in StateEncoding : TB(t, x) # SE(e)
      BY DEF TB, SE  \* "TB" # "SE"
<1>2. \A t \in Tag, x \in Bytes, e \in TranscriptEncoding : TB(t, x) # TR(e)
      BY DEF TB, TR  \* "TB" # "TR"
<1>3. \A e1 \in StateEncoding, e2 \in TranscriptEncoding : SE(e1) # TR(e2)
      BY DEF SE, TR  \* "SE" # "TR"
<1>4. QED BY <1>1, <1>2, <1>3

(****************************************************************************)
(* Domain-Separated Hash                                                     *)
(* Wraps PoseidonHashBytes with tagged constructor                           *)
(****************************************************************************)

PoseidonHashBytesIdeal(tag, x) == H[TB(tag, x)]

(****************************************************************************)
(* Domain Separation Lemma                                                   *)
(* Different tags produce different hashes (derived from HInjectiveOnCritical)*)
(* See ASSUMPTIONS.md CRYPTO-02                                              *)
(****************************************************************************)

LEMMA DomainSeparation ==
    \A tag1, tag2 \in Tag, x \in Bytes :
        tag1 # tag2 => PoseidonHashBytesIdeal(tag1, x) # PoseidonHashBytesIdeal(tag2, x)
<1>1. TAKE tag1 \in Tag, tag2 \in Tag, x \in Bytes
<1>2. ASSUME tag1 # tag2
<1>3. TB(tag1, x) # TB(tag2, x)
      \* Contrapositive of TBInjective: if TB equal, then tags equal
      BY <1>2, TBInjective
<1>4. TB(tag1, x) \in CriticalPreimage /\ TB(tag2, x) \in CriticalPreimage
      BY DEF CriticalPreimage, Preimage, TB
<1>5. H[TB(tag1, x)] # H[TB(tag2, x)]
      \* Contrapositive of HInjectiveOnCritical: if H equal, then inputs equal
      BY <1>3, <1>4, HInjectiveOnCritical
<1>6. PoseidonHashBytesIdeal(tag1, x) # PoseidonHashBytesIdeal(tag2, x)
      BY <1>5 DEF PoseidonHashBytesIdeal
<1>7. QED BY <1>6

(****************************************************************************)
(* State Digest Hash                                                         *)
(* Uses SE constructor for state encodings                                   *)
(****************************************************************************)

StateDigestHashIdeal(enc) == H[SE(enc)]

(****************************************************************************)
(* State Digest Binding Lemma                                                *)
(* Equal digests imply equal state encodings                                 *)
(****************************************************************************)

LEMMA StateDigestBinding ==
    \A e1, e2 \in StateEncoding :
        StateDigestHashIdeal(e1) = StateDigestHashIdeal(e2) => e1 = e2
<1>1. TAKE e1 \in StateEncoding, e2 \in StateEncoding
<1>2. ASSUME StateDigestHashIdeal(e1) = StateDigestHashIdeal(e2)
<1>3. H[SE(e1)] = H[SE(e2)]
      BY <1>2 DEF StateDigestHashIdeal
<1>4. SE(e1) \in CriticalPreimage /\ SE(e2) \in CriticalPreimage
      BY DEF CriticalPreimage, Preimage, SE
<1>5. SE(e1) = SE(e2)
      BY <1>3, <1>4, HInjectiveOnCritical
<1>6. e1 = e2
      BY <1>5, SEInjective
<1>7. QED BY <1>6

(****************************************************************************)
(* Transcript Digest Hash                                                    *)
(* Uses TR constructor for transcript encodings                              *)
(****************************************************************************)

TranscriptHashIdeal(enc) == H[TR(enc)]

(****************************************************************************)
(* Transcript Binding Lemma                                                  *)
(****************************************************************************)

LEMMA TranscriptBinding ==
    \A e1, e2 \in TranscriptEncoding :
        TranscriptHashIdeal(e1) = TranscriptHashIdeal(e2) => e1 = e2
<1>1. TAKE e1 \in TranscriptEncoding, e2 \in TranscriptEncoding
<1>2. ASSUME TranscriptHashIdeal(e1) = TranscriptHashIdeal(e2)
<1>3. H[TR(e1)] = H[TR(e2)]
      BY <1>2 DEF TranscriptHashIdeal
<1>4. TR(e1) \in CriticalPreimage /\ TR(e2) \in CriticalPreimage
      BY DEF CriticalPreimage, Preimage, TR
<1>5. TR(e1) = TR(e2)
      BY <1>3, <1>4, HInjectiveOnCritical
<1>6. e1 = e2
      BY <1>5, TRInjective
<1>7. QED BY <1>6

(****************************************************************************)
(* Cross-Domain Collision Resistance                                         *)
(* State and Transcript encodings never collide                              *)
(****************************************************************************)

LEMMA NoCrossCollision ==
    \A e1 \in StateEncoding, e2 \in TranscriptEncoding :
        StateDigestHashIdeal(e1) # TranscriptHashIdeal(e2)
<1>1. TAKE e1 \in StateEncoding, e2 \in TranscriptEncoding
<1>2. SE(e1) # TR(e2)
      BY ConstructorDisjoint
<1>3. SE(e1) \in CriticalPreimage /\ TR(e2) \in CriticalPreimage
      BY DEF CriticalPreimage, Preimage, SE, TR
<1>4. H[SE(e1)] # H[TR(e2)]
      BY <1>2, <1>3, HInjectiveOnCritical  \* Contrapositive
<1>5. StateDigestHashIdeal(e1) # TranscriptHashIdeal(e2)
      BY <1>4 DEF StateDigestHashIdeal, TranscriptHashIdeal
<1>6. QED BY <1>5

====
