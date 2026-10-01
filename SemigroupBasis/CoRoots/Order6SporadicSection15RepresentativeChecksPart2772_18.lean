import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_17

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom4 :
    (finiteBasis.drop 4).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom5

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom3 :
    (finiteBasis.drop 3).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom4

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom2 :
    (finiteBasis.drop 2).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom3

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

