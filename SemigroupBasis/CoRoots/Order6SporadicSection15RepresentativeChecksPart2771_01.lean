import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2771_00

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2771

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom49 :
    (finiteBasis.drop 49).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom50

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom48 :
    (finiteBasis.drop 48).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom49

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom47 :
    (finiteBasis.drop 47).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom48

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

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom43 :
    (finiteBasis.drop 43).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom44

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom42 :
    (finiteBasis.drop 42).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom43

end Checks

end S6_2771
end SemigroupBasis.CoRoots.Order6SporadicSection15

