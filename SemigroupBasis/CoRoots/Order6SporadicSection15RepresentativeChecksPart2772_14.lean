import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_13

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom16 :
    (finiteBasis.drop 16).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom17

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom15 :
    (finiteBasis.drop 15).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom16

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom14 :
    (finiteBasis.drop 14).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom15

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

