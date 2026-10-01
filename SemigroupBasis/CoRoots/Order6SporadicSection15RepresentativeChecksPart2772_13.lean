import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_12

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom19 :
    (finiteBasis.drop 19).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom20

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom18 :
    (finiteBasis.drop 18).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom19

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom17 :
    (finiteBasis.drop 17).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom18

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

