import SemigroupBasis.CoRoots.S5_107BlockCombinatorics
import SemigroupBasis.CoRoots.S5_107Extraction

namespace SemigroupBasis.CoRoots.S5_107

/-- The canonical list of multiple labels contains no duplicate. -/
theorem sortedMultipleLetters_nodup
    (letters : List Nat) :
    (sortedMultipleLetters letters).Nodup := by
  unfold sortedMultipleLetters
  exact
    (List.mergeSort_perm
      ((distinctLetters letters).filter
        (fun letter =>
          decide (2 ≤ letters.count letter)))
      (fun left right : Nat =>
        decide (left ≤ right))).nodup_iff.mpr <|
      (distinctLetters_nodup letters).filter
        (fun letter =>
          decide (2 ≤ letters.count letter))

/-- Deduplicated scanner markers and canonical multiple labels have the same
support, hence are permutations of one another. -/
theorem distinctTerminatedMarkers_perm_sortedMultipleLetters
    (letters : List Nat) :
    (distinctLetters
        (terminatedFactorMarkers
          (terminatedBlocks letters))).Perm
      (sortedMultipleLetters letters) := by
  have sourceNodup :
      (distinctLetters
        (terminatedFactorMarkers
          (terminatedBlocks letters))).Nodup :=
    distinctLetters_nodup _
  have targetNodup :
      (sortedMultipleLetters letters).Nodup :=
    sortedMultipleLetters_nodup letters
  rw [List.perm_iff_count]
  intro letter
  rw [sourceNodup.count, targetNodup.count]
  simp only [distinctLetters_mem_iff,
    mem_terminatedFactorMarkers_iff,
    sortedMultipleLetters_mem_iff]

end SemigroupBasis.CoRoots.S5_107
