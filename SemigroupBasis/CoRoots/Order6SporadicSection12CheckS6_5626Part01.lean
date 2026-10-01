import SemigroupBasis.CoRoots.Order6SporadicSection12Data

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis

namespace S6_5626

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem modelsPart01 : Models table.semigroup b8Part01Basis :=
  modelsB8Part01_of_finite_checks table (by decide)

end S6_5626

end SemigroupBasis.CoRoots.Order6SporadicSection12
