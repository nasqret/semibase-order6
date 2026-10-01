import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2771_04

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2771

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom17 :
    (finiteBasis.drop 17).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom18

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom16 :
    (finiteBasis.drop 16).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom17

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom15 :
    (finiteBasis.drop 15).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom16

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom14 :
    (finiteBasis.drop 14).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom15

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom13 :
    (finiteBasis.drop 13).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom14

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom12 :
    (finiteBasis.drop 12).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom13

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom11 :
    (finiteBasis.drop 11).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom12

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom10 :
    (finiteBasis.drop 10).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom11

end Checks

end S6_2771
end SemigroupBasis.CoRoots.Order6SporadicSection15

