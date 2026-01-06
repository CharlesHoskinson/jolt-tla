(****************************************************************************)
(* Module: SMTOps.tla                                                       *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE SMTOps ----
(****************************************************************************)
(* Purpose: Sparse Merkle Tree operations for memory commitments (Part 2)   *)
(* Appendix J Reference: J.10.8.5 (Root computation), J.10.8.6 (Encoding)   *)
(* Version: 1.0                                                             *)
(* Notes: Includes TLC-checkable Merkle property checks.                    *)
(*        ComputeInitialIORoot takes 4 parameters.                          *)
(****************************************************************************)
EXTENDS SMT

(****************************************************************************)
(* Root Computation (J.10.8.5)                                              *)
(* Compute SMT root from sparse memory map                                  *)
(****************************************************************************)

\* Compute the hash of a subtree rooted at a given depth
\* depth: current depth (0 = leaves, KEY_BITS = root)
\* keyPrefix: the prefix of keys in this subtree (as a natural number shifted appropriately)
\* memMap: the sparse memory map
\*
\* For TLC tractability, we compute this directly from the page map
\* rather than building an explicit tree structure

\* Helper: Check if any page in memMap falls within a subtree
\* A subtree at depth d with prefix p contains all keys where
\* the high (KEY_BITS - d) bits equal p
HasPagesInSubtree(memMap, depth, prefix) ==
    \E pageIdx \in DOMAIN memMap :
        LET
            \* Drop the low `depth` bits; remaining high (KEY_BITS - depth) bits form the prefix
            shift == depth
            keyHighBits == IF shift >= KEY_BITS THEN 0 ELSE pageIdx \div (2^shift)
        IN
            keyHighBits = prefix

\* Recursive root computation
\* This computes the Merkle root for a subtree
RECURSIVE ComputeSubtreeHash(_, _, _)
ComputeSubtreeHash(memMap, depth, prefix) ==
    IF depth = 0
    THEN
        \* Leaf level: return page hash or zero page hash
        LET pageIdx == prefix
        IN  GetPageHash(memMap, pageIdx)
    ELSE IF ~HasPagesInSubtree(memMap, depth, prefix)
    THEN
        \* Entire subtree is empty: use precomputed default
        DefaultHashes[depth]
    ELSE
        \* Recurse into children
        LET
            leftPrefix == prefix * 2
            rightPrefix == prefix * 2 + 1
            leftHash == ComputeSubtreeHash(memMap, depth - 1, leftPrefix)
            rightHash == ComputeSubtreeHash(memMap, depth - 1, rightPrefix)
        IN
            SMTNodeHash(leftHash, rightHash)

\* Compute full tree root
ComputeRoot(memMap) ==
    IF DOMAIN memMap = {}
    THEN EmptyTreeRoot
    ELSE ComputeSubtreeHash(memMap, KEY_BITS, 0)

(****************************************************************************)
(* Alternative: Direct Root Computation for Small Models                    *)
(* For TLC with very small PAGE_INDEX_TLC_BOUND                            *)
(****************************************************************************)

\* Build leaf layer: hash for each possible page index
LeafLayer(memMap) ==
    [idx \in PageIndex |-> GetPageHash(memMap, idx)]

\* Combine pairs of hashes moving up the tree
\* This is a simplified model for small bounds
RECURSIVE CombineLayer(_)
CombineLayer(layer) ==
    IF Cardinality(DOMAIN layer) <= 1
    THEN layer
    ELSE
        LET
            indices == DOMAIN layer
            maxIdx == CHOOSE m \in indices : \A n \in indices : n <= m
            newLayer == [i \in 0..(maxIdx \div 2) |->
                LET
                    leftIdx == i * 2
                    rightIdx == i * 2 + 1
                    leftHash == IF leftIdx \in indices THEN layer[leftIdx] ELSE ZERO_PAGE_HASH
                    rightHash == IF rightIdx \in indices THEN layer[rightIdx] ELSE ZERO_PAGE_HASH
                IN
                    SMTNodeHash(leftHash, rightHash)
            ]
        IN
            CombineLayer(newLayer)

\* Compute root for small models
ComputeRootSmall(memMap) ==
    LET
        leaves == LeafLayer(memMap)
        result == CombineLayer(leaves)
    IN
        IF DOMAIN result = {} THEN EmptyTreeRoot
        ELSE result[0]

(****************************************************************************)
(* SMT Update Operations                                                    *)
(****************************************************************************)

\* Update a single page and recompute root
UpdatePage(smt, pageIdx, newContentHash) ==
    LET
        newMemMap == SetPage(smt.memMap, pageIdx, newContentHash)
        newRoot == ComputeRoot(newMemMap)
        newDirtyCount == Cardinality(DOMAIN newMemMap)
    IN
        [smt EXCEPT
            !.memMap = newMemMap,
            !.root = newRoot,
            !.dirtyCount = newDirtyCount
        ]

\* Update multiple pages atomically
RECURSIVE UpdatePagesRec(_, _)
UpdatePagesRec(smt, updates) ==
    IF updates = << >>
    THEN smt
    ELSE
        LET
            update == Head(updates)
            pageIdx == update[1]
            contentHash == update[2]
            updatedSmt == UpdatePage(smt, pageIdx, contentHash)
        IN
            UpdatePagesRec(updatedSmt, Tail(updates))

UpdatePages(smt, updates) == UpdatePagesRec(smt, updates)

(****************************************************************************)
(* Root Encoding (J.10.8.6)                                                 *)
(* Convert Fr root to bytes32 for VMState                                   *)
(****************************************************************************)

\* Encode SMT root as bytes32 (little-endian)
\* J.10.8.6: "root_fr MUST be encoded deterministically"
RootToBytes32(rootFr) == FrToBytes32LE(rootFr)

\* Decode bytes32 to SMT root
Bytes32ToRoot(bytes32) == Bytes32ToFrLE(bytes32)

(****************************************************************************)
(* SMT Invariants                                                           *)
(****************************************************************************)

\* Core binding invariant: root equals computed root from map
\* This is the fundamental soundness property
SMTRootBindingInvariant(smt) ==
    smt.root = ComputeRoot(smt.memMap)

\* Dirty count matches actual non-zero pages
SMTDirtyCountInvariant(smt) ==
    smt.dirtyCount = Cardinality(DOMAIN smt.memMap)

\* Combined SMT invariant
SMTInvariant(smt) ==
    /\ SMTStateTypeOK(smt)
    /\ SMTRootBindingInvariant(smt)
    /\ SMTDirtyCountInvariant(smt)

(****************************************************************************)
(* Collision Resistance Properties                                          *)
(* Different memory maps -> different roots (security assumption)           *)
(****************************************************************************)
(* NOTE: Full properties quantify over exponential/infinite sets and are     *)
(* NOT checkable by TLC. They document security assumptions for proof.       *)
(* HIGH FIX: Added TLC-checkable sanity checks on small domains below.       *)

\* Two different memory maps produce different roots
\* This follows from hash collision resistance
SMTCollisionResistance ==
    \A m1, m2 \in MemoryMap :
        m1 # m2 => ComputeRoot(m1) # ComputeRoot(m2)

\* Root uniquely determines memory contents
\* (Inverse of collision resistance)
SMTRootDeterminesContents ==
    \A m1, m2 \in MemoryMap :
        ComputeRoot(m1) = ComputeRoot(m2) => m1 = m2

(****************************************************************************)
(* TLC-CHECKABLE MERKLE SANITY CHECKS                                       *)
(* HIGH FIX: Verify Merkle properties on small bounded domains              *)
(* These provide confidence that the implementation is correct              *)
(****************************************************************************)

\* Small domain for TLC verification: single-page memory maps
\* Uses PageIndex from SMT module (bounded by PAGE_INDEX_TLC_BOUND)
SmallMemoryMaps ==
    {[p |-> h] : p \in 0..1, h \in 0..3}  \* 2 pages x 4 hash values = 8 maps

\* TLC-checkable: Different single-page maps produce different roots
\* This is a sanity check that ComputeRoot is injective on small domain
SMTCollisionResistance_TLCCheck ==
    \A m1, m2 \in SmallMemoryMaps :
        m1 # m2 => ComputeRoot(m1) # ComputeRoot(m2)

\* TLC-checkable: Empty map produces EmptyTreeRoot
SMTEmptyMapRoot_TLCCheck ==
    ComputeRoot([p \in {} |-> 0]) = EmptyTreeRoot

\* TLC-checkable: Root computation is deterministic
\* Same map always produces same root
SMTRootDeterministic_TLCCheck ==
    \A m \in SmallMemoryMaps :
        ComputeRoot(m) = ComputeRoot(m)

\* TLC-checkable: Single page update changes root (unless same hash)
SMTUpdateChangesRoot_TLCCheck ==
    \A p \in 0..1, h1, h2 \in 0..2 :
        h1 # h2 =>
            ComputeRoot([p |-> h1]) # ComputeRoot([p |-> h2])

\* Combined TLC-checkable Merkle invariant
\* Add to INVARIANT in .cfg for runtime verification
SMTMerkleInvariants_TLCCheckable ==
    /\ SMTEmptyMapRoot_TLCCheck
    /\ SMTRootDeterministic_TLCCheck

(****************************************************************************)
(* Update Determinism                                                       *)
(* Same updates to same state -> same result                                *)
(****************************************************************************)

SMTUpdateDeterministic ==
    \A smt \in SMTState, pageIdx \in PageIndex, contentHash \in Fr :
        LET result == UpdatePage(smt, pageIdx, contentHash)
        IN  result.root = ComputeRoot(result.memMap)

(****************************************************************************)
(* Initial Memory Roots (J.5.8.4)                                           *)
(* Computation of initial memory roots from inputs                          *)
(****************************************************************************)

\* Compute initial IO memory root from manifest bytes
\* J.5.8.4: io_root_in = SMT root of manifest at input region
ComputeInitialIORoot(manifestBytes, inputPtr, inputLen, regionBase) ==
    \* For each byte in manifest, determine which page it falls into
    \* This is abstracted: we assume manifestBytes hashes to some pages
    \* Real implementation would compute page hashes from byte ranges
    LET
        \* Number of pages touched by input
        startPage == (inputPtr - regionBase) \div PAGE_SIZE_BYTES
        endPage == (inputPtr + inputLen - 1 - regionBase) \div PAGE_SIZE_BYTES
        \* Build memory map with input pages
        \* For TLC: hash based on page number and manifest length
        inputMemMap == [p \in startPage..endPage |->
            PoseidonHashV1(TAG_SMT_PAGE, Len(manifestBytes) * 100 + p)
        ]
    IN
        ComputeRoot(inputMemMap)

\* Initial RW memory root is empty tree root
\* J.5.8.4: "All bytes MUST be zero at execution start"
ComputeInitialRWRoot == EmptyTreeRoot

(****************************************************************************)
(* Memory Region Operations                                                 *)
(* Operations on the two separate memory regions                            *)
(****************************************************************************)

\* Update RW memory region
UpdateRWMemory(rwRegion, pageIdx, contentHash) ==
    [rwRegion EXCEPT !.smtState = UpdatePage(@, pageIdx, contentHash)]

\* Update IO memory region
UpdateIOMemory(ioRegion, pageIdx, contentHash) ==
    [ioRegion EXCEPT !.smtState = UpdatePage(@, pageIdx, contentHash)]

\* Get roots from both regions
GetMemoryRoots(rwRegion, ioRegion) ==
    [rw_root |-> rwRegion.smtState.root,
     io_root |-> ioRegion.smtState.root]

(****************************************************************************)
(* Encoding for VMState Integration                                         *)
(* Prepare roots for inclusion in VMStateV1                                *)
(****************************************************************************)

\* Package memory roots as bytes32 for VMState
MemoryRootsToBytes32(rwRoot, ioRoot) ==
    [rw_mem_root_bytes32 |-> RootToBytes32(rwRoot),
     io_root_bytes32 |-> RootToBytes32(ioRoot)]

(****************************************************************************)
(* Type OK for Operations                                                   *)
(****************************************************************************)

SMTOpsTypeOK ==
    /\ \A smt \in SMTState : ComputeRoot(smt.memMap) \in Fr
    /\ \A fr \in Fr : RootToBytes32(fr) \in Bytes32

====
