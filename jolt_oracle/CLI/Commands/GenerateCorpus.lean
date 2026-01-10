import Jolt.Oracle
import Jolt.Field.Fr
import Jolt.Poseidon.Params
import Jolt.Poseidon.Constants
import Jolt.Poseidon.Permute
import Jolt.State.Digest
import CLI.Format.Json

/-!
# Generate Conformance Corpus

Generates golden test vectors for Rust implementation conformance testing.

## Output Structure
```
corpus/
  manifest.json           # Version info, param hashes
  fr/
    FR001_canonical.json  # Field canonical encoding
    FR003_overflow.json   # Non-canonical rejection
    ...
  poseidon/
    POS001_empty.json     # Empty input hash
    POS005_known.json     # Known-answer tests
    ...
  digest/
    DIG001_basic.json     # Basic state digest
    ...
  negative/
    ERR_E100.json         # Invalid JSON rejection
    ...
```

## Manifest Format
```json
{
  "version": "1",
  "generated_at": "<ISO timestamp>",
  "lean_version": "4.x.x",
  "oracle_version": "0.1.0",
  "round_constants_hash": "<sha256>",
  "modulus_hex": "<64 chars>"
}
```

## References
- Transpiler.md: CONF-001, CONF-002
-/

namespace CLI.Commands

open Jolt
open Jolt.Poseidon
open Jolt.Poseidon.Constants
open CLI.Format

/-- A test vector for the corpus. -/
structure CorpusVector where
  id : String
  op : String
  input : String  -- JSON object string
  expected : String  -- JSON value (ok or err)
  deriving Repr

/-- Format a corpus vector as JSON. -/
private def formatVector (v : CorpusVector) : String :=
  jsonObject [
    ("id", jsonString v.id),
    ("op", jsonString v.op),
    ("input", v.input),
    ("expected", v.expected)
  ]

/-- Format bytes as hex string (without 0x prefix). -/
private def bytesToHex (bytes : ByteArray) : String := Id.run do
  let mut result := ""
  for i in [:bytes.size] do
    let b := bytes.data[i]!.toNat
    let hi := if b / 16 < 10 then Char.ofNat ('0'.toNat + b / 16)
              else Char.ofNat ('a'.toNat + b / 16 - 10)
    let lo := if b % 16 < 10 then Char.ofNat ('0'.toNat + b % 16)
              else Char.ofNat ('a'.toNat + b % 16 - 10)
    result := result.push hi
    result := result.push lo
  result

/-- Convert a Nat to 64-char hex string (little-endian 32 bytes). -/
private def natToHex64LE (n : Nat) : String := Id.run do
  let mut result := ""
  let mut val := n
  for _ in [:32] do
    let b := val % 256
    let hi := if b / 16 < 10 then Char.ofNat ('0'.toNat + b / 16)
              else Char.ofNat ('a'.toNat + b / 16 - 10)
    let lo := if b % 16 < 10 then Char.ofNat ('0'.toNat + b % 16)
              else Char.ofNat ('a'.toNat + b % 16 - 10)
    result := result.push hi
    result := result.push lo
    val := val / 256
  result

/-- Generate Fr test vectors (FR-001 through FR-006). -/
private def generateFrVectors : List CorpusVector := [
  -- FR-001: Canonical encoding (zero)
  { id := "fr_FR001_zero"
    op := "fr_canonical"
    input := jsonObject [("hex", jsonString (natToHex64LE 0))]
    expected := jsonObject [("ok", jsonObject [("decimal", jsonString "0")])]
  },
  -- FR-001: Canonical encoding (one)
  { id := "fr_FR001_one"
    op := "fr_canonical"
    input := jsonObject [("hex", jsonString (natToHex64LE 1))]
    expected := jsonObject [("ok", jsonObject [("decimal", jsonString "1")])]
  },
  -- FR-001: Canonical encoding (modulus - 1, largest valid)
  { id := "fr_FR001_max"
    op := "fr_canonical"
    input := jsonObject [("hex", jsonString (natToHex64LE (Fr.modulus - 1)))]
    expected := jsonObject [("ok", jsonObject [("decimal", jsonString (toString (Fr.modulus - 1)))])]
  },
  -- FR-003: Non-canonical (modulus itself, should fail)
  { id := "fr_FR003_overflow_modulus"
    op := "fr_canonical"
    input := jsonObject [("hex", jsonString (natToHex64LE Fr.modulus))]
    expected := jsonObject [("err", jsonObject [("code", jsonNat 300), ("name", jsonString "E300_NonCanonicalFr")])]
  },
  -- FR-003: Non-canonical (modulus + 1, should fail)
  { id := "fr_FR003_overflow_modulus_plus_one"
    op := "fr_canonical"
    input := jsonObject [("hex", jsonString (natToHex64LE (Fr.modulus + 1)))]
    expected := jsonObject [("err", jsonObject [("code", jsonNat 300), ("name", jsonString "E300_NonCanonicalFr")])]
  },
  -- FR-005: Arithmetic (add)
  { id := "fr_FR005_add"
    op := "fr_add"
    input := jsonObject [
      ("a", jsonString (natToHex64LE 100)),
      ("b", jsonString (natToHex64LE 200))
    ]
    expected := jsonObject [("ok", jsonObject [("result", jsonString (natToHex64LE 300))])]
  },
  -- FR-005: Arithmetic (mul)
  { id := "fr_FR005_mul"
    op := "fr_mul"
    input := jsonObject [
      ("a", jsonString (natToHex64LE 7)),
      ("b", jsonString (natToHex64LE 11))
    ]
    expected := jsonObject [("ok", jsonObject [("result", jsonString (natToHex64LE 77))])]
  }
]

/-- Compute Poseidon hash of input Fr values. -/
private def computePoseidonHash (inputs : Array Fr) : Fr :=
  Poseidon.hash joltPoseidonConfig inputs

/-- Generate Poseidon test vectors (POS-001 through POS-006). -/
private def generatePoseidonVectors : List CorpusVector :=
  let zeroHash := computePoseidonHash #[]
  let oneHash := computePoseidonHash #[Fr.one]
  let twoHash := computePoseidonHash #[Fr.one, Fr.ofNat 2]
  [
    -- POS-001: Parameters validation
    { id := "poseidon_POS001_params"
      op := "poseidon_params"
      input := jsonObject []
      expected := jsonObject [("ok", jsonObject [
        ("width", jsonNat POSEIDON_WIDTH),
        ("rate", jsonNat POSEIDON_RATE),
        ("full_rounds", jsonNat POSEIDON_FULL_ROUNDS),
        ("partial_rounds", jsonNat POSEIDON_PARTIAL_ROUNDS)
      ])]
    },
    -- POS-005: Empty input hash
    { id := "poseidon_POS005_empty"
      op := "poseidon_hash"
      input := jsonObject [("elements", "[]")]
      expected := jsonObject [("ok", jsonObject [("hash", jsonString (Fr.toHex64LE zeroHash))])]
    },
    -- POS-005: Single element hash
    { id := "poseidon_POS005_one"
      op := "poseidon_hash"
      input := jsonObject [("elements", jsonArray [jsonString (Fr.toHex64LE Fr.one)])]
      expected := jsonObject [("ok", jsonObject [("hash", jsonString (Fr.toHex64LE oneHash))])]
    },
    -- POS-005: Two element hash
    { id := "poseidon_POS005_two"
      op := "poseidon_hash"
      input := jsonObject [("elements", jsonArray [
        jsonString (Fr.toHex64LE Fr.one),
        jsonString (Fr.toHex64LE (Fr.ofNat 2))
      ])]
      expected := jsonObject [("ok", jsonObject [("hash", jsonString (Fr.toHex64LE twoHash))])]
    }
  ]

/-- Format state array as JSON array of hex strings. -/
private def formatStateArray (state : Array Fr) : String :=
  jsonArray (state.toList.map (fun x => jsonString (Fr.toHex64LE x)))

/-- Generate Poseidon trace vectors (POS-006). -/
private def generatePoseidonTraceVectors : List CorpusVector :=
  -- Compute permutation with trace for a simple input state
  let initialState := #[Fr.one, Fr.ofNat 2, Fr.zero]
  let (finalState, traces) := Poseidon.permuteWithTrace joltPoseidonConfig initialState
  -- Format first few round traces (don't include all 68 rounds to keep output manageable)
  let traceLimit := 10  -- Include first 10 rounds for debugging
  let truncatedTraces := (traces.toList.take traceLimit).toArray
  let tracesJson := jsonArray (truncatedTraces.toList.map formatStateArray)
  [
    -- POS-006: Permutation with trace for divergence localization
    { id := "poseidon_POS006_trace"
      op := "poseidon_permute_trace"
      input := jsonObject [
        ("initial_state", formatStateArray initialState)
      ]
      expected := jsonObject [("ok", jsonObject [
        ("final_state", formatStateArray finalState),
        ("round_traces", tracesJson),
        ("trace_count", jsonNat truncatedTraces.size),
        ("total_rounds", jsonNat POSEIDON_TOTAL_ROUNDS)
      ])]
    }
  ]

/-- Generate state digest test vectors (DIG-001 through DIG-003). -/
private def generateDigestVectors : List CorpusVector := [
  -- DIG-001: Basic digest with zero state
  { id := "digest_DIG001_zero_state"
    op := "compute_state_digest"
    input := jsonObject [
      ("program_hash", jsonString "0x0000000000000000000000000000000000000000000000000000000000000000"),
      ("state", jsonObject [
        ("pc", jsonNat 0),
        ("regs", "[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]"),
        ("step_counter", jsonNat 0),
        ("rw_mem_root", jsonString "0x0000000000000000000000000000000000000000000000000000000000000000"),
        ("io_root", jsonString "0x0000000000000000000000000000000000000000000000000000000000000000"),
        ("halted", jsonNat 0),
        ("exit_code", jsonNat 0),
        ("config_tags", "[]")
      ])
    ]
    -- Expected will be computed at runtime and filled in
    expected := jsonObject [("ok", jsonObject [("digest", jsonString "TBD")])]
  }
]

/-- Generate negative test vectors (error conditions). -/
private def generateNegativeVectors : List CorpusVector := [
  -- E100: Invalid JSON
  { id := "negative_E100_invalid_json"
    op := "parse_json"
    input := jsonObject [("raw", jsonString "{invalid")]
    expected := jsonObject [("err", jsonObject [("code", jsonNat 100), ("name", jsonString "E100_InvalidJSON")])]
  },
  -- E101: Duplicate key
  { id := "negative_E101_duplicate_key"
    op := "parse_json"
    input := jsonObject [("raw", jsonString "{\"a\":1,\"a\":2}")]
    expected := jsonObject [("err", jsonObject [("code", jsonNat 101), ("name", jsonString "E101_DuplicateKey")])]
  },
  -- E103: Invalid hex
  { id := "negative_E103_invalid_hex"
    op := "parse_hex"
    input := jsonObject [("hex", jsonString "not_valid_hex")]
    expected := jsonObject [("err", jsonObject [("code", jsonNat 103), ("name", jsonString "E103_InvalidHex")])]
  },
  -- E104: Wrong length
  { id := "negative_E104_wrong_length"
    op := "fr_canonical"
    input := jsonObject [("hex", jsonString "0011223344")]  -- Only 5 bytes, need 32
    expected := jsonObject [("err", jsonObject [("code", jsonNat 104), ("name", jsonString "E104_WrongLength")])]
  }
]

/-- Generate the manifest JSON. -/
private def generateManifest : String :=
  jsonObject [
    ("version", jsonString "1"),
    ("format_version", jsonString "corpus-v1"),
    ("lean_version", jsonString "4.26.0"),
    ("oracle_version", jsonString "0.1.0"),
    ("round_constants_hash", jsonString ROUND_CONSTANTS_HASH),
    ("modulus_hex", jsonString (natToHex64LE Fr.modulus)),
    ("modulus_decimal", jsonString (toString Fr.modulus))
  ]

/-- Generate the full corpus as a single JSON file. -/
def generateCorpusJson : String :=
  let allVectors := generateFrVectors ++ generatePoseidonVectors ++
                    generatePoseidonTraceVectors ++ generateDigestVectors ++
                    generateNegativeVectors
  let vectorsJson := jsonArray (allVectors.map formatVector)
  jsonObject [
    ("manifest", generateManifest),
    ("vectors", vectorsJson)
  ]

/-- Main entry point for generate-corpus command. -/
def generateCorpusMain (_args : List String) : IO UInt32 := do
  IO.println (generateCorpusJson ++ "\n")
  return 0

end CLI.Commands
