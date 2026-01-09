import NearFall.TLATypes

/-!
# Sparse Merkle Tree Types

Types and operations for SMT-based memory commitments matching jolt-tla.

## Main Definitions

* `PageIndex` - 32-bit page index
* `SMTState` - Sparse merkle tree state with root and dirty count
* `MemoryRegion` - RW or IO memory region with SMT

## References

* jolt-tla/tla/SMT.tla
* Jolt Spec §10.8 (Memory commitments)
-/

namespace NearFall.SMT

open TLATypes

/-! ### Protocol Constants (J.10.8.2) -/

/-- Page size in bytes (4 KiB). -/
def PAGE_SIZE_BYTES : Nat := 4096

/-- Page size as U64 for arithmetic. -/
def PAGE_SIZE_U64 : U64 := 4096

/-- Log2 of page size. -/
def PAGE_SHIFT : Nat := 12

/-- SMT tree depth (32-bit page indices). -/
def KEY_BITS : Nat := 32

/-! ### Page Types -/

/-- Page index: 32-bit unsigned integer.

**TLA+ equivalent**: `PageIndex == 0..(PAGE_INDEX_TLC_BOUND - 1)` -/
abbrev PageIndex := UInt32

/-- Page content hash (represented as Fr).

In the actual SMT, this is the Poseidon hash of page contents.

**TLA+ equivalent**: `PageContentHash == Fr` -/
abbrev PageContentHash := Fr

/-- Sentinel for zero page (all 4096 zero bytes). -/
def ZERO_PAGE : String := "ZERO_PAGE_BYTES4096"

/-! ### SMT Memory Map -/

/-- A memory map as a sparse association list.

Only non-zero pages are stored. Pages not in the map are implicitly
the zero page hash.

**TLA+ equivalent**: partial function from PageIndex to PageContentHash -/
structure MemoryMap where
  /-- Sparse page entries (pageIndex, contentHash). -/
  entries : List (PageIndex × PageContentHash)
  deriving DecidableEq, BEq

namespace MemoryMap

/-- Empty memory map (all pages are zero). -/
def empty : MemoryMap := ⟨[]⟩

/-- Check if a page is present (non-zero) in the map. -/
def pagePresent (m : MemoryMap) (idx : PageIndex) : Bool :=
  m.entries.any (fun (i, _) => i == idx)

/-- Get page hash, returning zero hash for absent pages.

The zero hash is represented as Fr.zero. -/
def getPageHash (m : MemoryMap) (idx : PageIndex) (zeroHash : Fr) : Fr :=
  match m.entries.find? (fun (i, _) => i == idx) with
  | some (_, h) => h
  | none => zeroHash

/-- Set a page in the memory map.

If contentHash equals zeroHash, removes the page (sparse representation). -/
def setPage (m : MemoryMap) (idx : PageIndex) (contentHash : Fr) (zeroHash : Fr) : MemoryMap :=
  let filtered := m.entries.filter (fun (i, _) => i != idx)
  if contentHash == zeroHash then
    ⟨filtered⟩
  else
    ⟨(idx, contentHash) :: filtered⟩

/-- Number of non-zero pages. -/
def dirtyCount (m : MemoryMap) : Nat := m.entries.length

end MemoryMap

instance : Inhabited MemoryMap where
  default := MemoryMap.empty

/-! ### Default Subtree Hashes (J.10.8.4) -/

/-- Default hashes for each tree depth.

Default hash at depth 0 is the leaf hash of the zero page.
Default hash at depth d is node_hash(default[d-1], default[d-1]).

In production, these are precomputed Poseidon hashes. Here we model
them abstractly as an array of Fr values. -/
structure DefaultHashes where
  /-- Precomputed default hashes for depths 0..KEY_BITS. -/
  hashes : Array Fr
  /-- Proof that array has correct length. -/
  h_len : hashes.size = KEY_BITS + 1
  deriving DecidableEq

namespace DefaultHashes

/-- Get default hash at depth d. -/
def get (dh : DefaultHashes) (d : Fin (KEY_BITS + 1)) : Fr :=
  dh.hashes[d.val]'(by have := dh.h_len; omega)

/-- Empty tree root is default hash at maximum depth. -/
def emptyTreeRoot (dh : DefaultHashes) : Fr :=
  dh.get ⟨KEY_BITS, by omega⟩

end DefaultHashes

/-! ### Bit Extraction for Tree Navigation (J.10.8.2) -/

/-- Extract bit at position pos from a 32-bit integer.

pos = 0 is LSB, pos = 31 is MSB. -/
def getBit (n : UInt32) (pos : Nat) : UInt32 :=
  (n >>> pos.toUInt32) &&& 1

/-- Get the branch direction at depth d for key k.

At depth d, we use bit (31 - d): MSB first.
Returns 0 for left, 1 for right. -/
def branchDirection (k : UInt32) (d : Nat) (_h : d < 32 := by decide) : UInt32 :=
  getBit k (31 - d)

/-! ### SMT State Record -/

/-- SMT state combining memory map with cached root.

**TLA+ equivalent**: `SMTState == [memMap: MemoryMap, root: Fr, dirtyCount: Nat]` -/
structure SMTState where
  /-- Sparse page map. -/
  memMap : MemoryMap
  /-- Current Merkle root. -/
  root : Fr
  /-- Cached number of non-zero pages. -/
  dirtyCount : Nat
  deriving DecidableEq, BEq

namespace SMTState

/-- Initial empty SMT state. -/
def init (emptyRoot : Fr) : SMTState := {
  memMap := MemoryMap.empty
  root := emptyRoot
  dirtyCount := 0
}

/-- Check if SMT is empty. -/
def isEmpty (s : SMTState) : Bool := s.dirtyCount == 0

end SMTState

instance : Inhabited SMTState where
  default := SMTState.init Fr.zero

/-! ### Address Translation (J.10.8.2) -/

/-- Given a guest address, compute page index.

Returns none if address is out of range. -/
def addressToPageIndex (addr : U64) (regionBase : U64) (regionSize : U64) : Option PageIndex :=
  if addr < regionBase || addr >= regionBase + regionSize then
    none
  else
    let offset := addr - regionBase
    some (offset / PAGE_SIZE_U64).toUInt32

/-- Compute offset within page. -/
def addressToPageOffset (addr : U64) (regionBase : U64) : U64 :=
  let offset := addr - regionBase
  offset % PAGE_SIZE_U64

/-! ### Memory Region Types -/

/-- Memory region type: RW (read-write) or IO (input/output).

**TLA+ equivalent**: `MemoryRegionType == {"rw", "io"}` -/
inductive MemoryRegionType where
  | rw : MemoryRegionType
  | io : MemoryRegionType
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Memory region with SMT state.

**TLA+ equivalent**: `MemoryRegion == [regionType, base, size, smtState]` -/
structure MemoryRegion where
  /-- Region type (rw or io). -/
  regionType : MemoryRegionType
  /-- Base address of region. -/
  base : U64
  /-- Size of region in bytes. -/
  size : U64
  /-- SMT state for this region. -/
  smtState : SMTState
  deriving DecidableEq, BEq

namespace MemoryRegion

/-- Create initial RW memory region. -/
def initRW (base size : U64) (emptyRoot : Fr) : MemoryRegion := {
  regionType := .rw
  base := base
  size := size
  smtState := SMTState.init emptyRoot
}

/-- Create initial IO memory region. -/
def initIO (base size : U64) (emptyRoot : Fr) : MemoryRegion := {
  regionType := .io
  base := base
  size := size
  smtState := SMTState.init emptyRoot
}

/-- Check if region base is page-aligned. -/
def isBaseAligned (r : MemoryRegion) : Bool :=
  r.base % PAGE_SIZE_U64 == 0

/-- Check if region size is page-aligned. -/
def isSizeAligned (r : MemoryRegion) : Bool :=
  r.size % PAGE_SIZE_U64 == 0

/-- Check if region fits in 32-bit page index space. -/
def fitsPageIndex (r : MemoryRegion) : Bool :=
  (r.size / PAGE_SIZE_U64).toNat ≤ 2^KEY_BITS

end MemoryRegion

instance : Inhabited MemoryRegion where
  default := MemoryRegion.initRW 0 0 Fr.zero

/-! ### Type Invariants -/

/-- SMTState type invariant. -/
def smtStateTypeOK (smt : SMTState) : Prop :=
  smt.dirtyCount = smt.memMap.entries.length

/-- Memory region type invariant. -/
def memoryRegionTypeOK (region : MemoryRegion) : Prop :=
  region.base % PAGE_SIZE_U64 = 0 ∧
  region.size % PAGE_SIZE_U64 = 0 ∧
  (region.size / PAGE_SIZE_U64).toNat ≤ 2^KEY_BITS ∧
  smtStateTypeOK region.smtState

/-! ### SMT Axioms (2 new axioms) -/

/-- **AXIOM 4**: SMT binding - root determines memory map.

Given the same SMT root, the memory contents are identical.
This captures the binding property of Merkle trees.

**TLA+ equivalent**: Implicit in SMT correctness -/
axiom smt_root_binding :
  ∀ (s1 s2 : SMTState), s1.root = s2.root →
    ∀ (idx : PageIndex), s1.memMap.getPageHash idx Fr.zero = s2.memMap.getPageHash idx Fr.zero

/-- **AXIOM 5**: SMT collision resistance.

Different memory contents produce different roots.

**TLA+ equivalent**: Merkle tree collision resistance -/
axiom smt_collision_resistant :
  ∀ (s1 s2 : SMTState) (idx : PageIndex),
    s1.memMap.getPageHash idx Fr.zero ≠ s2.memMap.getPageHash idx Fr.zero →
    s1.root ≠ s2.root

end NearFall.SMT
