import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5241_18

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_5241

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom37 :
    (finiteBasis.drop 37).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom38

end Checks

end S6_5241
end SemigroupBasis.CoRoots.Order6SporadicSection15
