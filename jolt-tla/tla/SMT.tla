(****************************************************************************)
(* Module: SMT.tla                                                          *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE SMT ----
(****************************************************************************)
(* Purpose: Sparse Merkle Tree structures for memory commitments (Part 1)   *)
(* Appendix J Reference: J.10.8 (Memory commitments)                        *)
(* Version: 1.0                                                             *)
(* Notes: Uses predicate form for TLC efficiency.                           *)
(****************************************************************************)
EXTENDS Hash, Sequences, Naturals

(****************************************************************************)
(* CONSTANTS                                                                 *)
(****************************************************************************)

CONSTANTS
    PAGE_INDEX_TLC_BOUND,   \* TLC bound: max page indices to model
    MAX_DIRTY_PAGES         \* TLC bound: max non-zero pages in a tree

\* SMT Parameters (J.10.8.2) - these are protocol constants
PAGE_SIZE_BYTES == 4096     \* 4 KiB per page
PAGE_SHIFT == 12            \* log2(PAGE_SIZE_BYTES)
KEY_BITS == 32              \* Tree depth (32-bit page indices)

ASSUME PAGE_INDEX_TLC_BOUND \in Nat /\ PAGE_INDEX_TLC_BOUND > 0
ASSUME MAX_DIRTY_PAGES \in Nat /\ MAX_DIRTY_PAGES >= 0

(****************************************************************************)
(* Page Types                                                                *)
(****************************************************************************)

\* Page index: 32-bit unsigned integer (TLC-bounded)
PageIndex == 0..(PAGE_INDEX_TLC_BOUND - 1)

\* Full page index range (spec anchor, not for TLC enumeration)
FullPageIndexRange == 0..(2^KEY_BITS - 1)

\* Page content: abstractly represented
\* In reality, this is [0..4095 -> Byte], but we abstract for TLC
\* We use Fr as a proxy for "page content hash" since that's what matters
PageContentHash == Fr

\* ZERO_PAGE is an abstract stand-in for the 4096-byte all-zero page (J.10.8.2).
\* We do not model bytes explicitly in this module; we only need a distinguished value.
ZERO_PAGE == "ZERO_PAGE_BYTES4096"

\* Leaf hash of the all-zero page (used for absent pages)
ZERO_PAGE_HASH == SMTLeafHash(ZERO_PAGE)

(****************************************************************************)
(* SMT Memory Map Representation                                             *)
(* We represent memory as a sparse map: only non-zero pages are stored      *)
(****************************************************************************)

\* A memory map is a *partial* function with DOMAIN(memMap) \subseteq PageIndex.
\* Only non-zero pages are stored; pages not in DOMAIN(memMap) are implicitly ZERO_PAGE_HASH.
\*
\* Set form (for documentation/specification):
MemoryMap ==
    UNION { [dom -> PageContentHash] : dom \in SUBSET PageIndex }

\* Predicate form (for TLC type checking - avoids building exponential set):
IsMemoryMap(memMap) ==
    /\ DOMAIN memMap \subseteq PageIndex
    /\ \A p \in DOMAIN memMap : memMap[p] \in PageContentHash

\* Canonical representation: stored pages are never the ZERO_PAGE_HASH.
MemoryMapCanonical(memMap) ==
    \A p \in DOMAIN memMap : memMap[p] # ZERO_PAGE_HASH

\* Empty memory map (all pages are zero)
EmptyMemoryMap == [p \in {} |-> ZERO_PAGE_HASH]

\* Check if a page is present (non-zero) in the map
PagePresent(memMap, pageIdx) == pageIdx \in DOMAIN memMap

\* Get page hash (returns ZERO_PAGE_HASH for absent pages)
GetPageHash(memMap, pageIdx) ==
    IF PagePresent(memMap, pageIdx)
    THEN memMap[pageIdx]
    ELSE ZERO_PAGE_HASH

\* Set a page in the memory map
SetPage(memMap, pageIdx, contentHash) ==
    IF contentHash = ZERO_PAGE_HASH
    THEN [p \in (DOMAIN memMap \ {pageIdx}) |-> memMap[p]]  \* Remove if zero
    ELSE [p \in (DOMAIN memMap \union {pageIdx}) |->
            IF p = pageIdx THEN contentHash ELSE memMap[p]]

(****************************************************************************)
(* Default (Empty) Subtree Hashes (J.10.8.4)                                *)
(* Precomputed hashes for all-zero subtrees at each depth                   *)
(****************************************************************************)

\* Default hash at depth 0 is the leaf hash of the zero page
\* Default hash at depth d is node_hash(default[d-1], default[d-1])

\* We model this as a function from depth to Fr
\* In TLC, this would be instantiated with concrete values

CONSTANT DefaultHashes  \* [0..KEY_BITS -> Fr]

\* Assumption: DefaultHashes is correctly computed
ASSUME DefaultHashes \in [0..KEY_BITS -> Fr]

\* THEOREM (not TLC-checkable with model substitution):
\*   DefaultHashes[0] = ZERO_PAGE_HASH
\*   DefaultHashes[d] = SMTNodeHash(DefaultHashes[d-1], DefaultHashes[d-1]) for d > 0
\* These hold by construction in any correct implementation.

\* Empty tree root is DefaultHashes[KEY_BITS]
EmptyTreeRoot == DefaultHashes[KEY_BITS]

(****************************************************************************)
(* Bit Extraction for Tree Navigation (J.10.8.2)                            *)
(* MSB-first: bit 31 is first branch decision                               *)
(****************************************************************************)

\* Extract bit at position pos from a 32-bit integer
\* pos = 0 is LSB, pos = 31 is MSB
GetBit(n, pos) == (n \div (2^pos)) % 2

\* Get the branch direction at depth d (0..31) for key k
\* At depth d, we use bit (31 - d): MSB first
\* Returns 0 for left, 1 for right
BranchDirection(k, d) == GetBit(k, 31 - d)

\* Path from root to leaf: sequence of 0/1 branch decisions
KeyToPath(k) == [d \in 0..(KEY_BITS-1) |-> BranchDirection(k, d)]

(****************************************************************************)
(* SMT Node Structure                                                        *)
(* For explicit tree representation (optional, for verification)            *)
(****************************************************************************)

\* A node is either a leaf or an internal node
\* Leaf: contains page hash
\* Internal: has left and right children (by hash reference)

SMTNodeType == {"leaf", "internal", "default"}

SMTNode == [
    type: SMTNodeType,
    hash: Fr,
    \* For internal nodes:
    leftHash: Fr,
    rightHash: Fr,
    \* For leaf nodes:
    pageIndex: PageIndex \union {-1},  \* -1 for non-leaves
    pageHash: Fr
]

\* Leaf node constructor
MakeLeafNode(pageIdx, pageHash) == [
    type |-> "leaf",
    hash |-> pageHash,  \* For leaves, hash = pageHash
    leftHash |-> 0,
    rightHash |-> 0,
    pageIndex |-> pageIdx,
    pageHash |-> pageHash
]

\* Internal node constructor
MakeInternalNode(leftHash, rightHash) == [
    type |-> "internal",
    hash |-> SMTNodeHash(leftHash, rightHash),
    leftHash |-> leftHash,
    rightHash |-> rightHash,
    pageIndex |-> -1,
    pageHash |-> 0
]

\* Default node at depth d
MakeDefaultNode(d) == [
    type |-> "default",
    hash |-> DefaultHashes[d],
    leftHash |-> IF d > 0 THEN DefaultHashes[d-1] ELSE 0,
    rightHash |-> IF d > 0 THEN DefaultHashes[d-1] ELSE 0,
    pageIndex |-> -1,
    pageHash |-> 0
]

(****************************************************************************)
(* SMT State Record                                                          *)
(* Combines memory map with cached root                                      *)
(****************************************************************************)

SMTState == [
    memMap: MemoryMap,      \* Sparse page map
    root: Fr,               \* Current Merkle root
    dirtyCount: Nat         \* Number of non-zero pages (for TLC bounds)
]

\* Initial empty SMT state
InitSMTState == [
    memMap |-> EmptyMemoryMap,
    root |-> EmptyTreeRoot,
    dirtyCount |-> 0
]

(****************************************************************************)
(* Address Translation (J.10.8.2)                                           *)
(* Guest address -> page index + offset                                     *)
(****************************************************************************)

\* Given a region base and a guest address, compute page index
\* Returns -1 if address is out of range
AddressToPageIndex(addr, regionBase, regionSize) ==
    IF addr < regionBase \/ addr >= regionBase + regionSize
    THEN -1  \* Out of range
    ELSE LET offset == addr - regionBase
         IN  offset \div PAGE_SIZE_BYTES

\* Compute offset within page
AddressToPageOffset(addr, regionBase) ==
    LET offset == addr - regionBase
    IN  offset % PAGE_SIZE_BYTES

(****************************************************************************)
(* Memory Region Types                                                       *)
(* Two separate regions: RW memory and I/O memory                           *)
(****************************************************************************)

MemoryRegionType == {"rw", "io"}

MemoryRegion == [
    regionType: MemoryRegionType,
    base: Nat,
    size: Nat,
    smtState: SMTState
]

(****************************************************************************)
(* Type Invariants                                                           *)
(****************************************************************************)

SMTStateTypeOK(smt) ==
    /\ IsMemoryMap(smt.memMap)  \* Use predicate form for TLC
    /\ MemoryMapCanonical(smt.memMap)
    /\ smt.root \in Fr
    /\ smt.dirtyCount \in Nat
    /\ smt.dirtyCount <= MAX_DIRTY_PAGES

PageIndexTypeOK(idx) == idx \in PageIndex

MemoryRegionTypeOK(region) ==
    /\ region.regionType \in MemoryRegionType
    /\ region.base \in Nat
    /\ region.size \in Nat
    /\ region.base % PAGE_SIZE_BYTES = 0  \* Must be page-aligned (J.10.8.2)
    /\ region.size % PAGE_SIZE_BYTES = 0  \* Must be page-aligned (J.10.8.2)
    /\ (region.size \div PAGE_SIZE_BYTES) <= 2^KEY_BITS  \* Must fit page_index_u32 (J.10.8.2)
    /\ SMTStateTypeOK(region.smtState)

====
