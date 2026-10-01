import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_04

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom43 :
    (finiteBasis.drop 43).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom44

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom42 :
    (finiteBasis.drop 42).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom43

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom41 :
    (finiteBasis.drop 41).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom42

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

