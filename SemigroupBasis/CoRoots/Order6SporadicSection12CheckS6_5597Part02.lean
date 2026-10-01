import SemigroupBasis.CoRoots.Order6SporadicSection12Data

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis

namespace S6_5597

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem modelsPart02 : Models table.semigroup a2Part02Basis :=
  modelsA2Part02_of_finite_checks table (by decide)

end S6_5597

end SemigroupBasis.CoRoots.Order6SporadicSection12
