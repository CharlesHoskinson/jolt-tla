namespace Jolt

/-- Helper to get byte from ByteArray with bounds check. -/
private def getByte (a : ByteArray) (i : Nat) : UInt8 :=
  if i < a.size then a.data[i]! else 0

/-- Compare two ByteArrays in bytewise lexicographic order. -/
def bytewiseLexicographic (a b : ByteArray) : Ordering := Id.run do
  let minLen := min a.size b.size
  for i in [:minLen] do
    let cmp := compare (getByte a i).toNat (getByte b i).toNat
    if cmp ≠ .eq then return cmp
  compare a.size b.size

/-- Less-than predicate for ByteArrays using bytewise lexicographic order. -/
def byteArrayLt (a b : ByteArray) : Bool := bytewiseLexicographic a b == .lt

/-- Less-than-or-equal predicate for ByteArrays. -/
def byteArrayLe (a b : ByteArray) : Bool := bytewiseLexicographic a b != .gt

/-- Helper to get element from array with bounds check. -/
private def getElem {α : Type} [Inhabited α] (arr : Array α) (i : Nat) : α :=
  if i < arr.size then arr[i]! else default

/-- Sort an array by a byte key extractor. -/
def sortByBytes {α : Type} [Inhabited α] (key : α → ByteArray) (arr : Array α) : Array α :=
  arr.qsort (fun x y => byteArrayLt (key x) (key y))

/-- Check if array is sorted by byte key. -/
def isSortedByBytes {α : Type} [Inhabited α] (key : α → ByteArray) (arr : Array α) : Bool := Id.run do
  if arr.size ≤ 1 then return true
  for i in [:arr.size - 1] do
    if !byteArrayLe (key (getElem arr i)) (key (getElem arr (i+1))) then return false
  return true

end Jolt
