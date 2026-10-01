import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2771_03

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2771

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom25 :
    (finiteBasis.drop 25).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom26

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom24 :
    (finiteBasis.drop 24).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom25

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom23 :
    (finiteBasis.drop 23).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom24

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom22 :
    (finiteBasis.drop 22).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom23

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom21 :
    (finiteBasis.drop 21).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom22

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom20 :
    (finiteBasis.drop 20).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom21

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom19 :
    (finiteBasis.drop 19).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom20

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom18 :
    (finiteBasis.drop 18).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom19

end Checks

end S6_2771
end SemigroupBasis.CoRoots.Order6SporadicSection15

