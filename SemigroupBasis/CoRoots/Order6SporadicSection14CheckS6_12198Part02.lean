import SemigroupBasis.CoRoots.Order6SporadicSection14Data

namespace SemigroupBasis.CoRoots.Order6SporadicSection14

open SemigroupBasis

namespace S6_12198

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem modelsPart02 : Models table.semigroup betaPart02Basis :=
  modelsBetaPart02_of_finite_checks table (by decide)

end S6_12198

end SemigroupBasis.CoRoots.Order6SporadicSection14
