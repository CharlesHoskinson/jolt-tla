(****************************************************************************)
(* Module: Tar.tla                                                          *)
(* Author: Charles Hoskinson                                                *)
(* Copyright: 2026 Charles Hoskinson                                        *)
(* License: Apache 2.0                                                      *)
(* Part of: https://github.com/CharlesHoskinson/jolt-tla                    *)
(****************************************************************************)
---- MODULE Tar ----
(****************************************************************************)
(* Purpose: TAR archive structure and canonicalization                      *)
(* Section Reference: §14.3 (TAR canonicalization)                          *)
(* Version: 1.0                                                             *)
(* Notes: Defines TAR member structure, path validation, and canonical      *)
(*        ordering. Reject absolute paths, require bytewise sorted names.   *)
(****************************************************************************)
EXTENDS Encodings, Sequences, Naturals, FiniteSets

(****************************************************************************)
(* TAR Member Types                                                          *)
(****************************************************************************)

\* TAR entry types (subset relevant for conformance bundles)
TAR_TYPE_REGULAR == "regular"
TAR_TYPE_DIRECTORY == "directory"

TarType == {TAR_TYPE_REGULAR, TAR_TYPE_DIRECTORY}

(****************************************************************************)
(* TAR Member Structure                                                      *)
(****************************************************************************)

\* A TAR member (file or directory entry)
\* TLC model: simplified to essential fields
TarMember == [
    name: STRING,           \* Path within archive
    type: TarType,          \* File type
    content: Seq(Byte)      \* File contents (empty for directories)
]

(****************************************************************************)
(* Path Validation (§14.3)                                                   *)
(****************************************************************************)

\* Check if character is a control character (0x00-0x1F)
IsControlChar(c) ==
    \E i \in 0..31 : c = i

\* Check if path starts with "/" (absolute path)
IsAbsolutePath(path) ==
    /\ Len(path) > 0
    /\ path[1] = "/"

\* Check if path starts with backslash (Windows absolute)
StartsWithBackslash(path) ==
    /\ Len(path) > 0
    /\ path[1] = "\\"

\* Split path on "/" to get segments
\* Simplified for TLC: returns sequence of segment lengths for validation
RECURSIVE CountSlashes(_)
CountSlashes(path) ==
    IF path = "" THEN 0
    ELSE IF path[1] = "/" THEN 1 + CountSlashes(SubSeq(path, 2, Len(path)))
    ELSE CountSlashes(SubSeq(path, 2, Len(path)))

\* Check if path contains ".." segment (path traversal attack)
\* Simplified: check for ".." anywhere in path
ContainsDoubleDot(path) ==
    \E i \in 1..(Len(path)-1) :
        /\ path[i] = "."
        /\ path[i+1] = "."

\* Check if path contains "." as a standalone segment
\* A single dot segment is either at start, between slashes, or at end
ContainsDotSegment(path) ==
    \/ (Len(path) = 1 /\ path[1] = ".")
    \/ (Len(path) >= 2 /\ path[1] = "." /\ path[2] = "/")
    \/ (\E i \in 2..(Len(path)-1) : path[i-1] = "/" /\ path[i] = "." /\ path[i+1] = "/")
    \/ (Len(path) >= 2 /\ path[Len(path)-1] = "/" /\ path[Len(path)] = ".")

\* Valid path per §14.3
\* - Not empty
\* - Not absolute (no leading /)
\* - No backslash (Windows path)
\* - No path traversal (.. or .)
\* - No control characters
ValidPath(path) ==
    /\ path # ""
    /\ ~IsAbsolutePath(path)
    /\ ~StartsWithBackslash(path)
    /\ ~ContainsDoubleDot(path)
    /\ ~ContainsDotSegment(path)
    \* Note: Control char check would require character-level access
    \* Production implementations MUST check for 0x00-0x1F

\* Directory names must end with "/"
ValidDirectoryName(name) ==
    /\ name # ""
    /\ name[Len(name)] = "/"

\* Regular file names must NOT end with "/"
ValidRegularFileName(name) ==
    /\ name # ""
    /\ name[Len(name)] # "/"

(****************************************************************************)
(* TAR Member Validation                                                     *)
(****************************************************************************)

\* Valid TAR member structure
ValidTarMember(m) ==
    /\ ValidPath(m.name)
    /\ m.type \\in TarType
    /\ (m.type = TAR_TYPE_DIRECTORY => ValidDirectoryName(m.name))
    /\ (m.type = TAR_TYPE_REGULAR => ValidRegularFileName(m.name))
    /\ (m.type = TAR_TYPE_DIRECTORY => m.content = << >>)

(****************************************************************************)
(* Canonical Ordering (§14.3)                                                *)
(* TAR members must be sorted by bytewise comparison of names               *)
(****************************************************************************)

\* Bytewise less-than comparison for strings
\* Returns TRUE if a < b in bytewise lexicographic order
RECURSIVE BytewiseLess(_, _)
BytewiseLess(a, b) ==
    IF a = "" THEN b # ""  \* Empty string < any non-empty
    ELSE IF b = "" THEN FALSE  \* Non-empty > empty
    ELSE IF a[1] < b[1] THEN TRUE
    ELSE IF a[1] > b[1] THEN FALSE
    ELSE BytewiseLess(SubSeq(a, 2, Len(a)), SubSeq(b, 2, Len(b)))

\* Bytewise less-than-or-equal
BytewiseLessEq(a, b) ==
    a = b \/ BytewiseLess(a, b)

\* Check if TAR members are sorted by name
TarMembersSorted(members) ==
    \A i \in 1..(Len(members)-1) :
        BytewiseLess(members[i].name, members[i+1].name)

\* No duplicate names allowed
NoDuplicateNames(members) ==
    Cardinality({members[i].name : i \\in 1..Len(members)}) = Len(members)

(****************************************************************************)
(* Valid TAR Archive                                                         *)
(****************************************************************************)

\* A valid TAR archive for conformance bundles
ValidTar(members) ==
    /\ \A i \\in 1..Len(members) : ValidTarMember(members[i])
    /\ TarMembersSorted(members)
    /\ NoDuplicateNames(members)

\* Empty TAR is valid
ValidEmptyTar == ValidTar(<< >>)

(****************************************************************************)
(* TAR Operations                                                            *)
(****************************************************************************)

\* Find member by name (returns member or error record)
FindMember(members, name) ==
    LET matches == {i \\in 1..Len(members) : members[i].name = name}
    IN IF matches = {} THEN [found |-> FALSE, member |-> [name |-> "", type |-> TAR_TYPE_REGULAR, content |-> << >>]]
       ELSE [found |-> TRUE, member |-> members[CHOOSE i \\in matches : TRUE]]

\* Check if archive contains a member with given name
HasMember(members, name) ==
    \E i \\in 1..Len(members) : members[i].name = name

\* Get all regular files
RegularFiles(members) ==
    {members[i] : i \\in 1..Len(members) /\ members[i].type = TAR_TYPE_REGULAR}

\* Get all directories
Directories(members) ==
    {members[i] : i \\in 1..Len(members) /\ members[i].type = TAR_TYPE_DIRECTORY}

(****************************************************************************)
(* Expected Conformance Bundle Structure                                     *)
(* Per §14.3, conformance bundles have specific required files              *)
(****************************************************************************)

\* Required files in a conformance bundle
REQUIRED_BUNDLE_FILE_REGISTRY == "registry.json"

\* Check if bundle has required structure
HasRequiredBundleFiles(members) ==
    HasMember(members, REQUIRED_BUNDLE_FILE_REGISTRY)

(****************************************************************************)
(* TAR Invariants                                                            *)
(****************************************************************************)

\* All members have valid paths
AllPathsValid(members) ==
    \A i \\in 1..Len(members) : ValidPath(members[i].name)

\* No absolute paths in archive
NoAbsolutePaths(members) ==
    \A i \\in 1..Len(members) : ~IsAbsolutePath(members[i].name)

\* No path traversal attacks
NoPathTraversal(members) ==
    \A i \\in 1..Len(members) :
        /\ ~ContainsDoubleDot(members[i].name)
        /\ ~ContainsDotSegment(members[i].name)

====
