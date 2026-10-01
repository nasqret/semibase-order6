import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2771_05

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2771

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom9 :
    (finiteBasis.drop 9).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom10

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom8 :
    (finiteBasis.drop 8).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom9

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom7 :
    (finiteBasis.drop 7).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom8

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom6 :
    (finiteBasis.drop 6).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom7

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom5 :
    (finiteBasis.drop 5).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom6

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom4 :
    (finiteBasis.drop 4).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom5

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom3 :
    (finiteBasis.drop 3).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom4

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom2 :
    (finiteBasis.drop 2).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom3

end Checks

end S6_2771
end SemigroupBasis.CoRoots.Order6SporadicSection15

