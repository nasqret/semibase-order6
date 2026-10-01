import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_09

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom28 :
    (finiteBasis.drop 28).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom29

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom27 :
    (finiteBasis.drop 27).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom28

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom26 :
    (finiteBasis.drop 26).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom27

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

