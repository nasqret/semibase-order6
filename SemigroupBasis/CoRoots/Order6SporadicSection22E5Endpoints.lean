import SemigroupBasis.CoRoots.Order6SporadicSection22E5Uniqueness
import SemigroupBasis.Opposite

/-! Unconditional E5/S6_8276 basis theorem, Lee-Zhang2015 Proposition22.1.
The exact published five-law basis is unchanged. Completeness uses actual
square expansion, descending-content saturation, semantic observations,
and protected-head block derivations for arbitrary nonempty words. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection22.E5
open SemigroupBasis

theorem derives_of_valid (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  (sameEval_derives identity.lhs.toList identity.rhs.toList (sameEval_valid identity valid)).toWord

theorem basisFor : BasisFor table.semigroup basis := ⟨models,derives_of_valid⟩

namespace S6_8276

theorem representative_basis : BasisFor table.semigroup basis := basisFor

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8276

#print axioms derives_of_valid
#print axioms basisFor
#print axioms S6_8276.representative_basis
#print axioms S6_8276.opposite_basis

end SemigroupBasis.CoRoots.Order6SporadicSection22.E5
