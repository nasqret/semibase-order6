import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2773_43

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2773

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom12 :
    (finiteBasis.drop 12).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom13

end Checks

end S6_2773
end SemigroupBasis.CoRoots.Order6SporadicSection15
