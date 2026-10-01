import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2773_31

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2773

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom24 :
    (finiteBasis.drop 24).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom25

end Checks

end S6_2773
end SemigroupBasis.CoRoots.Order6SporadicSection15
