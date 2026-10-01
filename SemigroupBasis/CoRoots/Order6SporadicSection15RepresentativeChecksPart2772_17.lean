import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_16

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom7 :
    (finiteBasis.drop 7).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom8

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom6 :
    (finiteBasis.drop 6).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom7

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom5 :
    (finiteBasis.drop 5).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom6

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

