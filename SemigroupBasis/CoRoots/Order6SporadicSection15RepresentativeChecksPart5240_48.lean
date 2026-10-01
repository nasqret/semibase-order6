import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5240_47

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_5240

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom8 :
    (finiteBasis.drop 8).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom9

end Checks

end S6_5240
end SemigroupBasis.CoRoots.Order6SporadicSection15
