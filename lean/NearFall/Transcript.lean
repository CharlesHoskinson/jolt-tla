import NearFall.Types

/-!
# Fiat-Shamir Transcript

Formal model of the Fiat-Shamir transcript for the Jolt zkVM.

## Main Definitions

* `absorb` - Absorb labeled data into transcript state
* `squeeze` - Generate challenge from transcript (abstract)
* `transcript_digest` - Compute digest of transcript state (abstract)

## Main Results

* `domain_separation` - Different labels produce different digests (derived)
* `absorption_order_matters` - Absorption order affects digest (derived)
* `absorb_ne_of_label_ne` - Different labels → different states (derived)
* `absorb_ne_of_data_ne` - Different data → different states (derived)

## Axioms Introduced

This module introduces the final axiom (3 of 3 total):
* `transcript_collision_resistant` - Poseidon hash is collision resistant

## Implementation Notes

The transcript tracks absorption history as a list of (label, data) pairs.
The actual Poseidon hash computation is abstracted; we only need the
collision resistance property for soundness proofs.

## References

* Jolt Spec §8 - Transcript operations
* Jolt Spec §8.4 - Transcript initialization
* Jolt Spec §8.5 - Data absorption
* Jolt Spec §8.6 - Challenge generation (squeeze)
-/

namespace NearFall.Transcript

open NearFall

/-! ### Abstract Digest Function -/

/-- Compute the cryptographic digest of a transcript state.

This is an abstract function representing Poseidon sponge finalization.
We do not specify the exact computation, only that it satisfies
the collision resistance axiom below.
See Jolt Spec §8 for Poseidon transcript semantics. -/
opaque transcript_digest : TranscriptState → Digest

/-! ### Cryptographic Axiom (3 of 3 total) -/

/-- **AXIOM 3/3**: Poseidon transcript is collision resistant.

If two transcript states have different absorption histories,
they produce different digests. This is the cryptographic assumption
that underlies Fiat-Shamir security.

**Justification**: Poseidon is a cryptographic sponge construction
designed for ZK-friendly collision resistance. The security proof
relies on the algebraic properties of the Poseidon permutation
over the BN254 scalar field.

**Note**: This axiom uses the absorption history (list of entries)
as the distinguishing criterion, which is stronger than comparing
the full TranscriptState (which includes chunk_index and squeezed flag). -/
axiom transcript_collision_resistant : ∀ (st1 st2 : TranscriptState),
  st1.absorbed ≠ st2.absorbed → transcript_digest st1 ≠ transcript_digest st2

/-! ### Transcript Operations -/

/-- Absorb labeled data into the transcript.

Appends a new absorption entry to the transcript's history.
The label provides domain separation to prevent cross-protocol attacks.
See Jolt Spec §8.5 for absorption semantics.

**Precondition**: Transcript must not be squeezed (enforced by checker).
**Postcondition**: New entry appended to absorption history. -/
def absorb (st : TranscriptState) (label : Label) (data : ByteArray) : TranscriptState :=
  { st with absorbed := st.absorbed ++ [{ label := label, data := data }] }

/-- Mark transcript as squeezed (no more absorptions allowed).

After squeezing, the transcript cannot accept more absorptions.
This models the Fiat-Shamir requirement that challenges are
generated only after all relevant data is absorbed.
See Jolt Spec §8.6. -/
def after_squeeze (st : TranscriptState) : TranscriptState :=
  { st with squeezed := true }

/-- Check if transcript can still absorb data. -/
def can_absorb (st : TranscriptState) : Bool := !st.squeezed

/-! ### Helper Lemmas -/

/-- Absorbing changes the absorption history. -/
theorem absorb_absorbed (st : TranscriptState) (label : Label) (data : ByteArray) :
    (absorb st label data).absorbed = st.absorbed ++ [{ label := label, data := data }] := rfl

/-- Absorbing preserves chunk index. -/
theorem absorb_chunk_index (st : TranscriptState) (label : Label) (data : ByteArray) :
    (absorb st label data).chunk_index = st.chunk_index := rfl

/-- Absorbing preserves squeezed flag. -/
theorem absorb_squeezed (st : TranscriptState) (label : Label) (data : ByteArray) :
    (absorb st label data).squeezed = st.squeezed := rfl

/-- After squeeze, transcript is marked squeezed. -/
theorem after_squeeze_squeezed (st : TranscriptState) :
    (after_squeeze st).squeezed = true := rfl

/-- After squeeze, absorption history is preserved. -/
theorem after_squeeze_absorbed (st : TranscriptState) :
    (after_squeeze st).absorbed = st.absorbed := rfl

/-! ### Domain Separation Theorems -/

/-- Absorbing with different labels produces different absorption histories.

This is a key security property: domain separation ensures that
data absorbed under one label cannot be confused with data under
another label, even if the byte content is identical. -/
theorem absorb_ne_of_label_ne (st : TranscriptState) (l1 l2 : Label)
    (data : ByteArray) (hne : l1 ≠ l2) :
    (absorb st l1 data).absorbed ≠ (absorb st l2 data).absorbed := by
  simp only [absorb]
  intro h
  -- h : st.absorbed ++ [{label := l1, data}] = st.absorbed ++ [{label := l2, data}]
  have h_suffix : [{ label := l1, data := data : AbsorptionEntry }] =
                  [{ label := l2, data := data }] := by
    exact List.append_cancel_left h
  simp only [List.cons.injEq, and_true] at h_suffix
  -- h_suffix : {label := l1, data} = {label := l2, data}
  have h_label : l1 = l2 := by
    cases h_suffix
    rfl
  exact hne h_label

/-- Absorbing with different data produces different absorption histories. -/
theorem absorb_ne_of_data_ne (st : TranscriptState) (label : Label)
    (d1 d2 : ByteArray) (hne : d1 ≠ d2) :
    (absorb st label d1).absorbed ≠ (absorb st label d2).absorbed := by
  simp only [absorb]
  intro h
  have h_suffix : [{ label := label, data := d1 : AbsorptionEntry }] =
                  [{ label := label, data := d2 }] := by
    exact List.append_cancel_left h
  simp only [List.cons.injEq, and_true] at h_suffix
  have h_data : d1 = d2 := by
    cases h_suffix
    rfl
  exact hne h_data

/-- **Domain Separation**: Different labels produce different digests.

This is a critical security theorem. It ensures that an attacker
cannot replay absorptions from one domain (e.g., VM state) in
another domain (e.g., SMT node), even with identical byte content.

**Proof**: By `absorb_ne_of_label_ne`, different labels produce
different absorption histories. By `transcript_collision_resistant`,
different histories produce different digests. -/
theorem domain_separation (st : TranscriptState) (l1 l2 : Label)
    (data : ByteArray) (hne : l1 ≠ l2) :
    transcript_digest (absorb st l1 data) ≠ transcript_digest (absorb st l2 data) := by
  apply transcript_collision_resistant
  exact absorb_ne_of_label_ne st l1 l2 data hne

/-- **Data Separation**: Different data produces different digests.

Same label but different data still produces different digests.
This ensures transcript integrity - changing any absorbed byte
changes the final challenge. -/
theorem data_separation (st : TranscriptState) (label : Label)
    (d1 d2 : ByteArray) (hne : d1 ≠ d2) :
    transcript_digest (absorb st label d1) ≠ transcript_digest (absorb st label d2) := by
  apply transcript_collision_resistant
  exact absorb_ne_of_data_ne st label d1 d2 hne

/-! ### Absorption Order Theorems -/

/-- Helper: Two single-element lists are equal iff their elements are equal. -/
theorem singleton_eq_iff {α : Type} (a b : α) : [a] = [b] ↔ a = b := by
  constructor
  · intro h; exact List.head_eq_of_cons_eq h
  · intro h; rw [h]

/-- Absorbing in different orders produces different histories.

This ensures that the order of absorptions matters - swapping
two absorptions produces a detectably different transcript. -/
theorem absorb_order_ne (st : TranscriptState)
    (l1 l2 : Label) (d1 d2 : ByteArray)
    (hne : (l1, d1) ≠ (l2, d2)) :
    (absorb (absorb st l1 d1) l2 d2).absorbed ≠
    (absorb (absorb st l2 d2) l1 d1).absorbed := by
  simp only [absorb]
  -- LHS: st.absorbed ++ [{l1, d1}] ++ [{l2, d2}]
  -- RHS: st.absorbed ++ [{l2, d2}] ++ [{l1, d1}]
  intro h
  simp only [List.append_assoc] at h
  have h' : [{ label := l1, data := d1 : AbsorptionEntry },
             { label := l2, data := d2 }] =
            [{ label := l2, data := d2 },
             { label := l1, data := d1 }] := by
    exact List.append_cancel_left h
  simp only [List.cons.injEq] at h'
  obtain ⟨h1, h2_list⟩ := h'
  simp only [and_true] at h2_list
  -- h1 : {l1, d1} = {l2, d2}
  -- h2_list : {l2, d2} = {l1, d1}
  -- From h1: l1 = l2 and d1 = d2
  have hl : l1 = l2 := by cases h1; rfl
  have hd : d1 = d2 := by cases h1; rfl
  -- But this contradicts hne : (l1, d1) ≠ (l2, d2)
  apply hne
  exact Prod.ext hl hd

/-- **Absorption Order Matters**: Different orders produce different digests.

This is essential for Fiat-Shamir security: if an attacker could
reorder absorptions without detection, they could manipulate
the challenge generation. -/
theorem absorption_order_matters (st : TranscriptState)
    (l1 l2 : Label) (d1 d2 : ByteArray)
    (hne : (l1, d1) ≠ (l2, d2)) :
    transcript_digest (absorb (absorb st l1 d1) l2 d2) ≠
    transcript_digest (absorb (absorb st l2 d2) l1 d1) := by
  apply transcript_collision_resistant
  exact absorb_order_ne st l1 l2 d1 d2 hne

/-! ### Fresh Transcript Theorems -/

/-- Empty transcript has empty absorption history. -/
theorem empty_absorbed : TranscriptState.empty.absorbed = [] := rfl

/-- Initialized transcript has empty absorption history. -/
theorem init_absorbed (n : Nat) : (TranscriptState.init n).absorbed = [] := rfl

/-- Absorbing into empty transcript creates single-entry history. -/
theorem absorb_empty (label : Label) (data : ByteArray) :
    (absorb TranscriptState.empty label data).absorbed =
    [{ label := label, data := data }] := by
  simp only [absorb, empty_absorbed, List.nil_append]

/-- Different first absorptions produce different digests. -/
theorem first_absorb_ne (l1 l2 : Label) (d1 d2 : ByteArray)
    (hne : (l1, d1) ≠ (l2, d2)) :
    transcript_digest (absorb TranscriptState.empty l1 d1) ≠
    transcript_digest (absorb TranscriptState.empty l2 d2) := by
  apply transcript_collision_resistant
  simp only [absorb, empty_absorbed, List.nil_append]
  intro h
  simp only [List.cons.injEq, and_true] at h
  have hl : l1 = l2 := by cases h; rfl
  have hd : d1 = d2 := by cases h; rfl
  exact hne (Prod.ext hl hd)

end NearFall.Transcript
