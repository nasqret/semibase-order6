import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_01

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom52 :
    (finiteBasis.drop 52).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom53

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom51 :
    (finiteBasis.drop 51).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom52

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom50 :
    (finiteBasis.drop 50).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom51

end Checks

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

