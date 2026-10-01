import SemigroupBasis.CoRoots.Order6SporadicSection13Tables

namespace SemigroupBasis.CoRoots.Order6SporadicSection13

open SemigroupBasis

namespace S6_9062

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem representativeModels : Models table.semigroup oppositeBasis :=
  modelsOpposite_of_finite_checks table (by decide)

theorem publishedModels : Models publishedSemigroup basis :=
  by
  simpa [publishedSemigroup, oppositeBasis] using
    representativeModels.oppositeReversed

end S6_9062

end SemigroupBasis.CoRoots.Order6SporadicSection13
