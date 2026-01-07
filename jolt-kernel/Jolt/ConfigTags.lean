import Jolt.Types
import Jolt.Transcript

/-!
# Jolt Kernel Config Tags

Implements S3.8: config_tags projection from registry.json.

## Main Definitions

* `ConfigTag` - A single config tag entry (name + value bytes)
* `ConfigTags` - List of sorted, unique config tags
* `checkConfigTags` - Validate tag ordering and uniqueness

## References

* Jolt Spec S3.8 (config_tags projection)
* RFC 8785 (JSON Canonicalization Scheme)
-/

namespace Jolt.ConfigTags

open Jolt Transcript

/-! ### Config Tag Structure -/

/-- A single configuration tag entry.

Tags are key-value pairs where:
- name: The tag name (string)
- valueBytes: JCS-serialized value as bytes -/
structure ConfigTag where
  /-- Tag name (unique identifier). -/
  name : String
  /-- JCS-serialized value bytes. -/
  valueBytes : List UInt8
  deriving DecidableEq, Repr, Inhabited

namespace ConfigTag

/-- BEq instance for ConfigTag (derived from DecidableEq for LawfulBEq). -/
instance : BEq ConfigTag := ⟨fun a b => decide (a = b)⟩

/-- LawfulBEq for ConfigTag. -/
instance : LawfulBEq ConfigTag where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-- Hash the tag name using PoseidonHashV1. -/
noncomputable def hashName (tag : ConfigTag) : Fr :=
  PoseidonHashV1' "tag_name" tag.name.toUTF8.toList

/-- Hash the tag value using PoseidonHashV1. -/
noncomputable def hashValue (tag : ConfigTag) : Fr :=
  PoseidonHashV1' "tag_value" tag.valueBytes

end ConfigTag

/-- List of config tags. -/
abbrev ConfigTags := List ConfigTag

/-! ### UTF-16 Comparison -/

/-- UTF-16 code units comparison.

Per RFC 8785: Object keys are sorted by UTF-16 code units.
For ASCII/BMP characters, this matches standard string comparison. -/
def utf16Lt (s1 s2 : String) : Bool :=
  s1 < s2

/-! ### Specification Predicates -/

/-- Specification: tags must be sorted by name and unique. -/
def SpecConfigTags (tags : ConfigTags) : Prop :=
  ∀ i j : Nat, i < j → j < tags.length →
    utf16Lt (tags.getD i default).name (tags.getD j default).name

/-! ### Checker Functions -/

/-- Check if tags are strictly sorted (sorted and unique).

Strictly sorted implies unique (no equal adjacent elements). -/
def checkStrictlySorted (tags : ConfigTags) : Bool :=
  match tags with
  | [] => true
  | [_] => true
  | a :: b :: rest => utf16Lt a.name b.name && checkStrictlySorted (b :: rest)

/-- Combined checker for valid config tags. -/
def checkConfigTags (tags : ConfigTags) : Bool :=
  checkStrictlySorted tags

/-! ### Soundness Theorems -/

/-- Helper: checkStrictlySorted on tail. -/
theorem checkStrictlySorted_tail {a b : ConfigTag} {rest : List ConfigTag}
    (h : checkStrictlySorted (a :: b :: rest) = true) :
    checkStrictlySorted (b :: rest) = true := by
  simp only [checkStrictlySorted, Bool.and_eq_true] at h
  exact h.2

/-- Helper: adjacent pair is ordered when checkStrictlySorted passes. -/
theorem checkStrictlySorted_adjacent {a b : ConfigTag} {rest : List ConfigTag}
    (h : checkStrictlySorted (a :: b :: rest) = true) :
    utf16Lt a.name b.name = true := by
  simp only [checkStrictlySorted, Bool.and_eq_true] at h
  exact h.1

/-- Helper: transitivity of utf16Lt (follows from String.lt transitivity). -/
theorem utf16Lt_trans {s1 s2 s3 : String} (h1 : utf16Lt s1 s2 = true) (h2 : utf16Lt s2 s3 = true) :
    utf16Lt s1 s3 = true := by
  simp only [utf16Lt] at *
  -- Convert Bool equality to Prop
  have h1' : s1 < s2 := of_decide_eq_true h1
  have h2' : s2 < s3 := of_decide_eq_true h2
  exact decide_eq_true (String.lt_trans h1' h2')

/-- Helper: checkStrictlySorted implies index-based ordering.

Key lemma: for a strictly sorted list, index i < j implies element[i] < element[j]. -/
theorem checkStrictlySorted_spec (tags : ConfigTags) (h : checkStrictlySorted tags = true) :
    ∀ i j : Nat, i < j → j < tags.length →
      utf16Lt (tags.getD i default).name (tags.getD j default).name := by
  induction tags with
  | nil => intro i j hij hj; simp at hj
  | cons a rest ih =>
    intro i j hij hj
    cases rest with
    | nil =>
      -- Single element list: j < 1 and i < j, so contradiction
      simp at hj
      omega
    | cons b rest' =>
      -- List has at least two elements
      have h_adj := checkStrictlySorted_adjacent h
      have h_tail := checkStrictlySorted_tail h
      have h_tail_spec := ih h_tail
      cases hi : i with
      | zero =>
        -- i = 0, so tags[0] = a
        cases hj' : j with
        | zero => omega  -- i < j but j = 0, contradiction
        | succ j' =>
          -- j = j' + 1, so tags[j] = (b :: rest')[j']
          simp only [List.getD_cons_zero]
          cases j' with
          | zero =>
            -- j = 1, so tags[1] = b
            simp only [List.getD_cons_succ, List.getD_cons_zero]
            exact h_adj
          | succ j'' =>
            -- j > 1, need to show a.name < tags[j].name
            -- Use transitivity: a.name < b.name < ... < tags[j].name
            simp only [List.getD_cons_succ]
            -- tags[j] = (b :: rest')[j' + 1] = rest'[j']
            have h_b_lt : utf16Lt b.name ((b :: rest').getD (j'' + 1) default).name := by
              apply h_tail_spec 0 (j'' + 1)
              · omega
              · simp only [List.length_cons] at hj ⊢; omega
            simp only [List.getD_cons_zero] at h_b_lt
            exact utf16Lt_trans h_adj h_b_lt
      | succ i' =>
        -- i > 0, use induction on tail
        simp only [List.getD_cons_succ]
        -- Need to show j-th element of (a :: b :: rest') equals (j-1)-th of (b :: rest')
        have hj_pos : j ≥ 1 := by omega
        have hgetD_eq : (a :: b :: rest').getD j default = (b :: rest').getD (j - 1) default := by
          cases j with
          | zero => omega
          | succ j' => simp only [List.getD_cons_succ, Nat.add_sub_cancel]
        rw [hgetD_eq]
        apply h_tail_spec i' (j - 1)
        · omega
        · simp only [List.length_cons] at hj ⊢; omega

/-- THEOREM: checkConfigTags soundness.

If checkConfigTags passes, the specification holds. -/
theorem checkConfigTags_sound (tags : ConfigTags) :
    checkConfigTags tags = true → SpecConfigTags tags := by
  intro h
  unfold checkConfigTags at h
  unfold SpecConfigTags
  exact checkStrictlySorted_spec tags h

/-! ### Config Tag Operations -/

/-- Sort config tags by name (for normalization). -/
def sortTags (tags : ConfigTags) : ConfigTags :=
  tags.mergeSort (fun a b => a.name <= b.name)

/-- Lookup a tag by name. -/
def lookup (tags : ConfigTags) (name : String) : Option ConfigTag :=
  tags.find? (·.name == name)

/-- Check if a tag exists. -/
def contains (tags : ConfigTags) (name : String) : Bool :=
  tags.any (·.name == name)

/-! ### Hashing Operations -/

/-- Hash all tag names into a list of Fr elements.

Per spec S11.10 step 11: Absorb tag name hashes. -/
noncomputable def hashAllNames (tags : ConfigTags) : List Fr :=
  tags.map ConfigTag.hashName

/-- Hash all tag values into a list of Fr elements.

Per spec S11.10 step 12: Absorb tag value hashes. -/
noncomputable def hashAllValues (tags : ConfigTags) : List Fr :=
  tags.map ConfigTag.hashValue

/-- Absorb all config tags into a transcript.

This is used in StateDigestV1 steps 10-12:
1. Absorb tag count
2. Absorb all name hashes
3. Absorb all value hashes -/
noncomputable def absorbIntoTranscript (ts : TranscriptState) (tags : ConfigTags) : TranscriptState :=
  -- Step 10: Tag count
  let ts := ts.absorbFr (Fr.ofNat tags.length)
  -- Step 11: Name hashes
  let ts := ts.absorbFrs (hashAllNames tags)
  -- Step 12: Value hashes
  ts.absorbFrs (hashAllValues tags)

end Jolt.ConfigTags
