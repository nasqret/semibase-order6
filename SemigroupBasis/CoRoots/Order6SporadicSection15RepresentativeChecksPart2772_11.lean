import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_10

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom25 :
    (finiteBasis.drop 25).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom26

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom24 :
    (finiteBasis.drop 24).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom25

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom23 :
    (finiteBasis.drop 23).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom24

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

