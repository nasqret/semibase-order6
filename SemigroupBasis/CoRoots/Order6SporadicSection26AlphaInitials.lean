import SemigroupBasis.CoRoots.Order6SporadicSection26AlphaReduction
import SemigroupBasis.Examples.LeftRegularBandThree

/-! The computed normalizer retains exactly the original first-occurrence
sequence. This supplies the head equality used in canonical uniqueness. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection26.F7
open SemigroupBasis SemigroupBasis.Examples

theorem firstOccurrenceSequence_append_one (before : List Nat) (x : Nat) :
    firstOccurrenceSequence (before ++ [x]) =
      if x ∈ before then firstOccurrenceSequence before else firstOccurrenceSequence before ++ [x] := by
  induction before with
  | nil => simp [firstOccurrenceSequence]
  | cons head tail ih =>
      by_cases old : x ∈ tail
      · simp [List.cons_append, firstOccurrenceSequence, ih, old]
      · by_cases same : x = head
        · subst head
          simp [List.cons_append, firstOccurrenceSequence, ih, old, List.filter_append]
        · simp [List.cons_append, firstOccurrenceSequence, ih, old, same, List.filter_append]

namespace AlphaForm

theorem heads_insertAll (form : AlphaForm) (before letters : List Nat)
    (known : form.heads = firstOccurrenceSequence before) :
    (form.insertAll letters).heads = firstOccurrenceSequence (before ++ letters) := by
  induction letters generalizing form before with
  | nil => simpa [insertAll] using known
  | cons x rest ih =>
      have next : (form.push x).heads = firstOccurrenceSequence (before ++ [x]) := by
        rw [heads_push, known, firstOccurrenceSequence_append_one]
        simp only [mem_firstOccurrenceSequence_iff]
      have remaining := ih (form.push x) (before ++ [x]) next
      simpa [insertAll, List.append_assoc] using remaining

end AlphaForm

theorem normalizeAlpha_heads (letters : List Nat) :
    (normalizeAlpha letters).heads = firstOccurrenceSequence letters := by
  simpa only [normalizeAlpha, List.nil_append] using
    AlphaForm.heads_insertAll AlphaForm.nil [] letters rfl

theorem normalizeCanonical_heads (letters : List Nat) :
    (normalizeCanonical letters).heads = firstOccurrenceSequence letters := by
  unfold normalizeCanonical
  rw [AlphaForm.heads_tighten, normalizeAlpha_heads]

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.firstOccurrenceSequence_append_one
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.heads_insertAll
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.normalizeAlpha_heads
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.normalizeCanonical_heads
end SemigroupBasis.CoRoots.Order6SporadicSection26.F7
