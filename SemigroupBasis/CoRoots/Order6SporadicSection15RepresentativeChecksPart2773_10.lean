import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2773_09

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2773

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom46 :
    (finiteBasis.drop 46).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom47

end Checks

end S6_2773
end SemigroupBasis.CoRoots.Order6SporadicSection15
