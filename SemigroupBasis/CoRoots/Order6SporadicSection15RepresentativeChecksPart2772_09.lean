import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_08

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom31 :
    (finiteBasis.drop 31).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom32

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom30 :
    (finiteBasis.drop 30).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom31

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom29 :
    (finiteBasis.drop 29).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom30

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

