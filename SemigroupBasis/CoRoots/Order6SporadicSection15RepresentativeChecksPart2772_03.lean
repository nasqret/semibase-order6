import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_02

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom49 :
    (finiteBasis.drop 49).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom50

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom48 :
    (finiteBasis.drop 48).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom49

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom47 :
    (finiteBasis.drop 47).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom48

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

