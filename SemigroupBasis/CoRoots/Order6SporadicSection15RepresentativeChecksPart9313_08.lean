import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart9313_07

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_9313

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom48 :
    (finiteBasis.drop 48).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom49

end Checks

end S6_9313
end SemigroupBasis.CoRoots.Order6SporadicSection15
