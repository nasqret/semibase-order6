import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_11

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom22 :
    (finiteBasis.drop 22).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom23

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom21 :
    (finiteBasis.drop 21).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom22

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom20 :
    (finiteBasis.drop 20).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom21

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

