import SemigroupBasis.CoRoots.Order6SporadicSection12CheckS6_5626Part01
import SemigroupBasis.CoRoots.Order6SporadicSection12CheckS6_5626Part02
import SemigroupBasis.CoRoots.Order6SporadicSection12CheckS6_5626Part03
import SemigroupBasis.CoRoots.Order6SporadicSection12CheckS6_5626Part04
import SemigroupBasis.CoRoots.Order6SporadicSection12CheckS6_5626Part05

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis

namespace S6_5626

theorem models : Models table.semigroup b8Basis :=
  by
    rw [b8Basis_eq_parts]
    exact modelsAppend (modelsAppend (modelsAppend (modelsAppend (modelsPart01) modelsPart02) modelsPart03) modelsPart04) modelsPart05

theorem oppositeModels :
    Models table.semigroup.opposite b8OppositeBasis :=
  models.oppositeReversed

theorem basisFor_of_canonicalProof
    (reduction : RestrictedBasisReduction table Connected)
    (proof : RestrictedCanonicalProof table b8Basis Connected) :
    BasisFor table.semigroup b8Basis :=
  basisFor_of_restrictedCanonical table b8Basis Connected models reduction proof

theorem oppositeBasisFor_of_canonicalProof
    (reduction : RestrictedBasisReduction table Connected)
    (proof : RestrictedCanonicalProof table b8Basis Connected) :
    BasisFor table.semigroup.opposite b8OppositeBasis := by
  simpa [b8OppositeBasis] using
    (basisFor_of_canonicalProof reduction proof).oppositeReversed

end S6_5626

end SemigroupBasis.CoRoots.Order6SporadicSection12
