import SemigroupBasis.CoRoots.Order6SporadicSection12Data

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis

namespace S6_5625

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem modelsPart05 : Models table.semigroup b7Part05Basis :=
  modelsB7Part05_of_finite_checks table (by decide)

end S6_5625

end SemigroupBasis.CoRoots.Order6SporadicSection12
