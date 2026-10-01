import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_05

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom40 :
    (finiteBasis.drop 40).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom41

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom39 :
    (finiteBasis.drop 39).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom40

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom38 :
    (finiteBasis.drop 38).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom39

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

