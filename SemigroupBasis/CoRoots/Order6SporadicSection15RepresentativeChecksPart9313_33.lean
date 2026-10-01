import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart9313_32

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_9313

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom23 :
    (finiteBasis.drop 23).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom24

end Checks

end S6_9313
end SemigroupBasis.CoRoots.Order6SporadicSection15
