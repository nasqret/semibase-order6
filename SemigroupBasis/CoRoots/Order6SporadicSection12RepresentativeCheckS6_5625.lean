import SemigroupBasis.CoRoots.Order6SporadicSection12CheckS6_5625Part01
import SemigroupBasis.CoRoots.Order6SporadicSection12CheckS6_5625Part02
import SemigroupBasis.CoRoots.Order6SporadicSection12CheckS6_5625Part03
import SemigroupBasis.CoRoots.Order6SporadicSection12CheckS6_5625Part04
import SemigroupBasis.CoRoots.Order6SporadicSection12CheckS6_5625Part05
import SemigroupBasis.CoRoots.Order6SporadicSection12CheckS6_5625Part06

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis

namespace S6_5625

theorem models : Models table.semigroup b7Basis :=
  by
    rw [b7Basis_eq_parts]
    exact modelsAppend (modelsAppend (modelsAppend (modelsAppend (modelsAppend (modelsPart01) modelsPart02) modelsPart03) modelsPart04) modelsPart05) modelsPart06

theorem oppositeModels :
    Models table.semigroup.opposite b7OppositeBasis :=
  models.oppositeReversed

theorem basisFor_of_canonicalProof
    (reduction :
      RestrictedBasisReduction table PairwiseDisjointConnectedProduct)
    (proof :
      RestrictedCanonicalProof table b7Basis
        PairwiseDisjointConnectedProduct) :
    BasisFor table.semigroup b7Basis :=
  basisFor_of_restrictedCanonical table b7Basis
    PairwiseDisjointConnectedProduct models reduction proof

theorem oppositeBasisFor_of_canonicalProof
    (reduction :
      RestrictedBasisReduction table PairwiseDisjointConnectedProduct)
    (proof :
      RestrictedCanonicalProof table b7Basis
        PairwiseDisjointConnectedProduct) :
    BasisFor table.semigroup.opposite b7OppositeBasis := by
  simpa [b7OppositeBasis] using
    (basisFor_of_canonicalProof reduction proof).oppositeReversed

end S6_5625

end SemigroupBasis.CoRoots.Order6SporadicSection12
