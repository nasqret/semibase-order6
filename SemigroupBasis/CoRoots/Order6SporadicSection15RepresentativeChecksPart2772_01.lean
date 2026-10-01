import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_00

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom55 :
    (finiteBasis.drop 55).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom56

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom54 :
    (finiteBasis.drop 54).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom55

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom53 :
    (finiteBasis.drop 53).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom54

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

