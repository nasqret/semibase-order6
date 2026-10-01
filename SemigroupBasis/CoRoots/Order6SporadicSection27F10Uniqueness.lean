import SemigroupBasis.CoRoots.Order6SporadicSection27F10Separation

namespace SemigroupBasis.CoRoots.Order6SporadicSection27.F10

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_870

theorem alphaCanonicalBlocks_eq {left right : List FirstOccurrenceGapBlock}
    (leftCanonical : AlphaCanonicalBlocks left) (rightCanonical : AlphaCanonicalBlocks right)
    (same : Observations (renderGapBlocks left) (renderGapBlocks right)) : left = right := by
  classical
  have sameMarkers : gapBlockMarkers left = gapBlockMarkers right := by
    rw [← firstOccurrenceSequenceList_renderGapBlocks leftCanonical.sparse.wellFormed,
      ← firstOccurrenceSequenceList_renderGapBlocks rightCanonical.sparse.wellFormed]
    exact same.ini
  apply Classical.byContradiction
  intro different
  obtain ⟨d⟩ := exists_leastDifferingSparseBlocks leftCanonical.sparse rightCanonical.sparse
    sameMarkers different
  rcases d.orientedChoiceDifference with forward | backward
  · obtain ⟨v, lv, rv⟩ := oriented_difference_separates d rightCanonical.noCrossing forward
    have equal := same.probes v
    rw [lv, rv] at equal
    exact (by decide : (0 : Fin 6) ≠ 2) equal
  · let swapped := swap_difference d
    have reverse : OrientedChoiceDifference (gapBlockMarkers right) swapped.leftBlock.marker
        swapped.leftBlock.seconds swapped.rightBlock.seconds := by
      change OrientedChoiceDifference (gapBlockMarkers right) d.rightBlock.marker
        d.rightBlock.seconds d.leftBlock.seconds
      rw [← sameMarkers, ← d.sameMarker]
      exact backward
    obtain ⟨v, rv, lv⟩ := oriented_difference_separates swapped leftCanonical.noCrossing reverse
    have equal := same.probes v
    rw [lv, rv] at equal
    exact (by decide : (2 : Fin 6) ≠ 0) equal

/-- Full, unbounded F10 completeness for the eighteen A-D laws. -/
theorem complete (e : Identity Nat) (valid : e.SatisfiedBy table.semigroup) :
    Derives basis e.lhs e.rhs := by
  obtain ⟨left, lc, _, ld⟩ := listDerivesToAlphaCanonicalBlocks e.lhs.toList
  obtain ⟨right, rc, _, rd⟩ := listDerivesToAlphaCanonicalBlocks e.rhs.toList
  have same : Observations (renderGapBlocks left) (renderGapBlocks right) :=
    (observations_of_listDerives ld).symm.trans
      ((valid_observations e valid).trans (observations_of_listDerives rd))
  have equal := alphaCanonicalBlocks_eq lc rc same
  subst right
  exact (ld.trans rd.symm).toWord

theorem paper_basis : BasisFor table.semigroup basis := ⟨models, complete⟩

end SemigroupBasis.CoRoots.Order6SporadicSection27.F10

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.alphaCanonicalBlocks_eq
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.complete
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.paper_basis
