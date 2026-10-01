import SemigroupBasis.CoRoots.Order6SporadicSection13Tables

namespace SemigroupBasis.CoRoots.Order6SporadicSection13

open SemigroupBasis

namespace S6_10410

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem representativeModels : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

theorem publishedModels : Models publishedSemigroup basis :=
  representativeModels

end S6_10410

end SemigroupBasis.CoRoots.Order6SporadicSection13
