import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_15

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom10 :
    (finiteBasis.drop 10).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom11

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom9 :
    (finiteBasis.drop 9).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom10

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom8 :
    (finiteBasis.drop 8).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom9

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

