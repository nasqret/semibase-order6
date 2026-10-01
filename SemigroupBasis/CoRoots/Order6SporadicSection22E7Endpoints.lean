import SemigroupBasis.CoRoots.Order6SporadicSection22E7Uniqueness

/-! Unconditional E7/S6_13185 basis theorem, Lee-Zhang2015 Proposition22.9.
Both halves are proved: exact finite soundness and unrestricted completeness
through actual canonical derivations and proved semantic uniqueness. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection22.E7
open SemigroupBasis

theorem derives_of_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) : Derives basis identity.lhs identity.rhs := by
  obtain ⟨leftFirst,leftRest,leftGood,leftDerives⟩ := existsCanonicalWord identity.lhs
  obtain ⟨rightFirst,rightRest,rightGood,rightDerives⟩ := existsCanonicalWord identity.rhs
  let canonicalIdentity : Identity Nat :=
    ⟨canonicalWord leftFirst leftRest,canonicalWord rightFirst rightRest⟩
  have canonicalValid : canonicalIdentity.SatisfiedBy table.semigroup := by
    intro valuation
    exact (leftDerives.sound models valuation).symm.trans
      ((valid valuation).trans (rightDerives.sound models valuation))
  have labels : (leftFirst :: leftRest).map CanonicalBlock.letter =
      (rightFirst :: rightRest).map CanonicalBlock.letter := by
    have same := valid_ini canonicalIdentity canonicalValid
    change Examples.firstOccurrenceSequence (renderBlocks (leftFirst :: leftRest)) =
      Examples.firstOccurrenceSequence (renderBlocks (rightFirst :: rightRest)) at same
    rw [ini_render _ leftGood,ini_render _ rightGood] at same
    exact same
  have sameBlocks := render_unique (leftFirst :: leftRest) (rightFirst :: rightRest) [] []
    leftGood rightGood labels (by simp)
    (fun valuation => sandwich_valid canonicalIdentity canonicalValid valuation)
  have sameWords : canonicalWord leftFirst leftRest = canonicalWord rightFirst rightRest := by
    apply Word.toList_injective
    exact congrArg renderBlocks sameBlocks
  rw [sameWords] at leftDerives
  exact leftDerives.trans rightDerives.symm

theorem basisFor : BasisFor table.semigroup basis := ⟨models,derives_of_valid⟩

namespace S6_13185

theorem representative_basis : BasisFor table.semigroup basis := basisFor

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_13185

#print axioms derives_of_valid
#print axioms basisFor
#print axioms S6_13185.representative_basis
#print axioms S6_13185.opposite_basis

end SemigroupBasis.CoRoots.Order6SporadicSection22.E7
