import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_07

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom34 :
    (finiteBasis.drop 34).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom35

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom33 :
    (finiteBasis.drop 33).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom34

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom32 :
    (finiteBasis.drop 32).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom33

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

