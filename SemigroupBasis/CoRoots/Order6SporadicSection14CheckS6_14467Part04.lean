import SemigroupBasis.CoRoots.Order6SporadicSection14Data

namespace SemigroupBasis.CoRoots.Order6SporadicSection14

open SemigroupBasis

namespace S6_14467

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem modelsPart04 : Models table.semigroup oppositeBetaPart04Basis :=
  modelsOppositeBetaPart04_of_finite_checks table (by decide)

end S6_14467

end SemigroupBasis.CoRoots.Order6SporadicSection14
