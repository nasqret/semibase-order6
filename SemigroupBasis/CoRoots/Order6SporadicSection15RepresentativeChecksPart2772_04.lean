import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_03

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom46 :
    (finiteBasis.drop 46).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom47

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom45 :
    (finiteBasis.drop 45).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom46

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom44 :
    (finiteBasis.drop 44).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom45

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

