import SemigroupBasis.CoRoots.Order6SporadicSection12Data

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis

namespace S6_5625

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem modelsPart06 : Models table.semigroup b7Part06Basis :=
  modelsB7Part06_of_finite_checks table (by decide)

end S6_5625

end SemigroupBasis.CoRoots.Order6SporadicSection12
