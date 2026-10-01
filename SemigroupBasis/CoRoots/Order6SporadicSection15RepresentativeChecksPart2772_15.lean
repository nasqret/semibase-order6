import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_14

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom13 :
    (finiteBasis.drop 13).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom14

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom12 :
    (finiteBasis.drop 12).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom13

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom11 :
    (finiteBasis.drop 11).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom12

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

