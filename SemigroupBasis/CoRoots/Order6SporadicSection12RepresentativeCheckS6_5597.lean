import SemigroupBasis.CoRoots.Order6SporadicSection12CheckS6_5597Part01
import SemigroupBasis.CoRoots.Order6SporadicSection12CheckS6_5597Part02

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis

namespace S6_5597

theorem models : Models table.semigroup a2Basis :=
  by
    rw [a2Basis_eq_parts]
    exact modelsAppend (modelsPart01) modelsPart02

theorem oppositeModels :
    Models table.semigroup.opposite a2OppositeBasis :=
  models.oppositeReversed

theorem basisFor_of_canonicalProof
    (proof : UnrestrictedCanonicalProof table a2Basis) :
    BasisFor table.semigroup a2Basis :=
  basisFor_of_unrestrictedCanonical table a2Basis models proof

theorem oppositeBasisFor_of_canonicalProof
    (proof : UnrestrictedCanonicalProof table a2Basis) :
    BasisFor table.semigroup.opposite a2OppositeBasis := by
  simpa [a2OppositeBasis] using
    (basisFor_of_canonicalProof proof).oppositeReversed

end S6_5597

end SemigroupBasis.CoRoots.Order6SporadicSection12
