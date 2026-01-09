import NearFall

/-!
# Tests.Transcript

Test suite for the Fiat-Shamir transcript module.

## Test Categories
* Absorb function tests
* After squeeze tests
* Domain separation tests
* Absorption history tests

## References
* Jolt Spec §8 - Transcript Operations
-/

namespace Tests.Transcript

open NearFall
open NearFall.Transcript

/-! ### Basic Absorb Tests -/

-- Absorb adds entry to history
#guard (absorb TranscriptState.empty Label.vm_state ByteArray.empty).absorbed.length == 1

-- Absorb preserves chunk_index
#guard (absorb TranscriptState.empty Label.vm_state ByteArray.empty).chunk_index == 0
#guard (absorb (TranscriptState.init 5) Label.vm_state ByteArray.empty).chunk_index == 5

-- Absorb preserves squeezed flag
#guard (absorb TranscriptState.empty Label.vm_state ByteArray.empty).squeezed == false

-- Multiple absorbs accumulate
#guard (absorb (absorb TranscriptState.empty Label.vm_state ByteArray.empty)
               Label.smt_page ByteArray.empty).absorbed.length == 2

/-! ### After Squeeze Tests -/

-- after_squeeze sets squeezed flag
#guard (after_squeeze TranscriptState.empty).squeezed == true

-- after_squeeze preserves absorbed history
#guard (after_squeeze TranscriptState.empty).absorbed == []

-- can_absorb returns true before squeeze
#guard (can_absorb TranscriptState.empty) == true

-- can_absorb returns false after squeeze
#guard (can_absorb (after_squeeze TranscriptState.empty)) == false

/-! ### Absorption Entry Tests -/

-- Absorbed entry has correct label
example : (absorb TranscriptState.empty Label.vm_state ByteArray.empty).absorbed =
          [{ label := Label.vm_state, data := ByteArray.empty }] := rfl

-- Different labels create different entries
example : (absorb TranscriptState.empty Label.vm_state ByteArray.empty).absorbed ≠
          (absorb TranscriptState.empty Label.smt_page ByteArray.empty).absorbed := by
  simp only [absorb, TranscriptState.empty, List.nil_append, ne_eq, List.cons.injEq, and_true]
  intro h
  cases h

/-! ### Domain Separation Property Tests -/

-- Different labels → different absorption histories
example : ∀ (st : TranscriptState) (data : ByteArray),
    (absorb st Label.vm_state data).absorbed ≠ (absorb st Label.challenge data).absorbed :=
  fun st data => absorb_ne_of_label_ne st Label.vm_state Label.challenge data (by decide)

-- Different data → different absorption histories
example : ∀ (st : TranscriptState) (label : Label) (d1 d2 : ByteArray),
    d1 ≠ d2 →
    (absorb st label d1).absorbed ≠ (absorb st label d2).absorbed :=
  absorb_ne_of_data_ne

-- Domain separation theorem instantiation
example : ∀ (data : ByteArray),
    transcript_digest (absorb TranscriptState.empty Label.vm_state data) ≠
    transcript_digest (absorb TranscriptState.empty Label.smt_page data) :=
  fun data => domain_separation TranscriptState.empty Label.vm_state Label.smt_page data (by decide)

/-! ### Absorption Order Tests -/

-- Different orders produce different histories
example : ∀ (st : TranscriptState) (d1 d2 : ByteArray),
    d1 ≠ d2 →
    (absorb (absorb st Label.vm_state d1) Label.smt_page d2).absorbed ≠
    (absorb (absorb st Label.smt_page d2) Label.vm_state d1).absorbed := by
  intro st d1 d2 h_ne
  apply absorb_order_ne
  intro h_eq
  simp only [Prod.mk.injEq] at h_eq
  exact absurd h_eq.2 h_ne

-- Order affects digest (from axiom)
example : ∀ (d1 d2 : ByteArray),
    d1 ≠ d2 →
    transcript_digest (absorb (absorb TranscriptState.empty Label.vm_state d1) Label.smt_page d2) ≠
    transcript_digest (absorb (absorb TranscriptState.empty Label.smt_page d2) Label.vm_state d1) := by
  intro d1 d2 h_ne
  apply absorption_order_matters
  intro h_eq
  simp only [Prod.mk.injEq] at h_eq
  exact absurd h_eq.2 h_ne

/-! ### Fresh Transcript Tests -/

-- Empty transcript theorem
example : TranscriptState.empty.absorbed = [] := empty_absorbed

-- Init transcript theorem
example : (TranscriptState.init 42).absorbed = [] := init_absorbed 42

-- Absorb into empty creates single entry
example : (absorb TranscriptState.empty Label.vm_state ByteArray.empty).absorbed =
          [{ label := Label.vm_state, data := ByteArray.empty }] :=
  absorb_empty Label.vm_state ByteArray.empty

end Tests.Transcript
