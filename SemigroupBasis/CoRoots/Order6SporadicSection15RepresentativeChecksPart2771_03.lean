import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2771_02

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2771

namespace Checks

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

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom28 :
    (finiteBasis.drop 28).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom29

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom27 :
    (finiteBasis.drop 27).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom28

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom26 :
    (finiteBasis.drop 26).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom27

end Checks

end S6_2771
end SemigroupBasis.CoRoots.Order6SporadicSection15

