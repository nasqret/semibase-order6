import SemigroupBasis.CoRoots.Order6SporadicSection14Data

namespace SemigroupBasis.CoRoots.Order6SporadicSection14

open SemigroupBasis

namespace S6_14467

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem modelsPart03 : Models table.semigroup oppositeBetaPart03Basis :=
  modelsOppositeBetaPart03_of_finite_checks table (by decide)

end S6_14467

end SemigroupBasis.CoRoots.Order6SporadicSection14
