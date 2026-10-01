import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2771_01

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2771

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom41 :
    (finiteBasis.drop 41).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom42

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

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom37 :
    (finiteBasis.drop 37).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom38

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom36 :
    (finiteBasis.drop 36).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom37

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom35 :
    (finiteBasis.drop 35).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom36

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom34 :
    (finiteBasis.drop 34).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom35

end Checks

end S6_2771
end SemigroupBasis.CoRoots.Order6SporadicSection15

