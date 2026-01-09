import Jolt.Errors
import Jolt.Util.ByteOrder

namespace Jolt.Bundle

/-- Tar member type. -/
inductive TarType where
  | Regular   -- '0' or '\0'
  | Directory -- '5'
  deriving Repr, DecidableEq, Inhabited

/-- Tar archive member. -/
structure TarMember where
  /-- Member name (path) -/
  name : String
  /-- Member type -/
  type : TarType
  /-- Content (empty for directories) -/
  content : ByteArray
  deriving Inhabited

namespace TarMember

instance : Repr TarMember where
  reprPrec m _ := s!"TarMember({m.name}, {repr m.type}, {m.content.size} bytes)"

/-- Get name as bytes for sorting. -/
def nameBytes (m : TarMember) : ByteArray := m.name.toUTF8

end TarMember

/-- Compare ByteArrays for equality. -/
private def byteArrayEq (a b : ByteArray) : Bool :=
  a.data == b.data

/-- Check if array of ByteArrays contains a given ByteArray. -/
private def containsBytes (arr : Array ByteArray) (ba : ByteArray) : Bool :=
  arr.any (fun x => byteArrayEq x ba)

/-- Check if a character is a control character (0x00-0x1F). -/
private def isControlChar (c : Char) : Bool := c.toNat < 0x20

/-- Validate a path component per §14.3.

Rejects . and .. segments, and empty segments. -/
def isValidPathComponent (s : String) : Bool :=
  !s.isEmpty && s != "." && s != ".."

/-- Validate a tar member path per §14.3.

Per spec §14.3 path normalization:
- MUST NOT start with `/` (no absolute paths)
- MUST NOT contain `..` or `.` path segments
- MUST NOT contain `\\` (backslash)
- MUST NOT contain NUL bytes or control characters
- Empty segments between consecutive `/` are invalid
- Directory names MUST end with `/` (validated in validateTarMember) -/
def validatePath (path : String) : OracleResult Unit := do
  if path.isEmpty then
    throw (ErrorCode.E704_InvalidPath "empty path")
  if path.startsWith "/" then
    throw (ErrorCode.E704_InvalidPath "absolute path not allowed")
  -- Check for backslash
  if path.any (· == '\\') then
    throw (ErrorCode.E704_InvalidPath "backslash not allowed")
  -- Check for control characters (including NUL)
  if path.any isControlChar then
    throw (ErrorCode.E704_InvalidPath "control characters not allowed")
  -- Check path segments
  let segments := path.splitOn "/"
  -- Note: trailing '/' for directories creates an empty final segment, which is OK
  let checkSegments := if path.endsWith "/" then segments.dropLast else segments
  for seg in checkSegments do
    if !isValidPathComponent seg then
      throw (ErrorCode.E704_InvalidPath s!"invalid segment '{seg}'")

/-- Validate a single tar member per §14.3. -/
def validateTarMember (m : TarMember) : OracleResult Unit := do
  validatePath m.name
  -- Per §14.3: Directory member names MUST end with '/'
  match m.type with
  | .Directory =>
    if !m.name.endsWith "/" then
      throw (ErrorCode.E704_InvalidPath "directory name must end with '/'")
    -- Directories must have size 0
    if m.content.size != 0 then
      throw (ErrorCode.E704_InvalidPath "directory must have size 0")
  | .Regular =>
    -- Regular files MUST NOT end with '/'
    if m.name.endsWith "/" then
      throw (ErrorCode.E704_InvalidPath "regular file name must not end with '/'")

/-- Validate tar archive structure per §14.3. -/
def validateTar (members : Array TarMember) : OracleResult Unit := do
  -- Check each member
  for m in members do
    validateTarMember m

  -- Check sorted order (bytewise lexicographic on name bytes)
  if !isSortedByBytes TarMember.nameBytes members then
    throw ErrorCode.E702_UnsortedMembers

  -- Check for duplicates (per §14.3: Duplicate member names MUST NOT appear)
  let mut seen : Array ByteArray := #[]
  for m in members do
    let nameB := m.nameBytes
    if containsBytes seen nameB then
      throw ErrorCode.E705_DuplicateMember
    seen := seen.push nameB

/-- TAR header size. -/
def HEADER_SIZE : Nat := 512

/-- TAR block size. -/
def BLOCK_SIZE : Nat := 512

/-- Compute checksum for tar header. -/
def computeChecksum (header : ByteArray) : Nat := Id.run do
  let mut sum : Nat := 0
  for i in [:header.size] do
    -- Checksum field (bytes 148-155) treated as spaces
    if i >= 148 && i < 156 then
      sum := sum + 0x20
    else
      sum := sum + header.data[i]!.toNat
  return sum

/-- Convert natural number to octal string with explicit termination. -/
private def natToOctal (n : Nat) : String := Id.run do
  if n == 0 then return "0"
  let mut result : List Char := []
  let mut val := n
  for _ in [:64] do  -- Max 64 iterations is more than enough for any Nat
    if val == 0 then break
    result := Char.ofNat (0x30 + val % 8) :: result
    val := val / 8
  return result.foldl (fun s c => s.push c) ""

/-- Write octal number to buffer (with trailing NUL/space). -/
def writeOctal (buf : ByteArray) (offset : Nat) (width : Nat) (value : Nat) : ByteArray := Id.run do
  let mut b := buf
  let digits := natToOctal value
  let padLen := if width > 1 + digits.length then width - 1 - digits.length else 0
  let padded := (List.replicate padLen '0').foldl (fun s c => s.push c) "" ++ digits
  for i in [:padded.length] do
    if offset + i < b.size then
      b := b.set! (offset + i) (padded.toList[i]!.toNat.toUInt8)
  -- NUL terminator
  if offset + width - 1 < b.size then
    b := b.set! (offset + width - 1) 0
  return b

/-- Create tar header for a member. -/
def createHeader (member : TarMember) : OracleResult ByteArray := do
  validatePath member.name
  let mut header := ByteArray.mk (List.replicate HEADER_SIZE 0).toArray

  -- Name (0-99)
  let nameBytes := member.name.toUTF8
  if nameBytes.size > 100 then
    throw (ErrorCode.E704_InvalidPath "name too long")
  for i in [:nameBytes.size] do
    header := header.set! i nameBytes.data[i]!

  -- Mode (100-107): 0644 for files, 0755 for dirs
  let mode := if member.type == .Directory then 0o755 else 0o644
  header := writeOctal header 100 8 mode

  -- UID (108-115): 0
  header := writeOctal header 108 8 0

  -- GID (116-123): 0
  header := writeOctal header 116 8 0

  -- Size (124-135)
  let size := if member.type == .Directory then 0 else member.content.size
  header := writeOctal header 124 12 size

  -- Mtime (136-147): must be 0
  header := writeOctal header 136 12 0

  -- Checksum placeholder (148-155): spaces
  for i in [:8] do
    header := header.set! (148 + i) 0x20

  -- Type (156)
  let typeChar : UInt8 := match member.type with
    | .Regular => 0x30    -- '0'
    | .Directory => 0x35  -- '5'
  header := header.set! 156 typeChar

  -- Linkname (157-256): empty

  -- Magic (257-262): "ustar\0"
  let magic := "ustar".toUTF8
  for i in [:magic.size] do
    header := header.set! (257 + i) magic.data[i]!
  header := header.set! 262 0

  -- Version (263-264): "00"
  header := header.set! 263 0x30
  header := header.set! 264 0x30

  -- Compute and write checksum
  let checksum := computeChecksum header
  header := writeOctal header 148 7 checksum
  header := header.set! 155 0x20  -- space after checksum

  pure header

/-- Create canonical tar archive from members. -/
def createCanonicalTar (members : Array TarMember) : OracleResult ByteArray := do
  -- Sort members by name bytes
  let sorted := sortByBytes TarMember.nameBytes members

  -- Validate
  validateTar sorted

  let mut archive := ByteArray.empty

  -- Write each member
  for member in sorted do
    let header ← createHeader member
    archive := archive ++ header

    -- Write content (padded to block size)
    if member.type == .Regular && member.content.size > 0 then
      archive := archive ++ member.content
      let padding := (BLOCK_SIZE - member.content.size % BLOCK_SIZE) % BLOCK_SIZE
      archive := archive ++ ByteArray.mk (List.replicate padding 0).toArray

  -- Two 512-byte zero blocks at end
  archive := archive ++ ByteArray.mk (List.replicate (2 * BLOCK_SIZE) 0).toArray

  pure archive

end Jolt.Bundle
