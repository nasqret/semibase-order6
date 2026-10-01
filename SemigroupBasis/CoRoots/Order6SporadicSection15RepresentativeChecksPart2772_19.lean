import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2772_18

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2772

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom1 :
    (finiteBasis.drop 1).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa [List.drop_drop] using finiteBasisCheckedFrom2

set_option maxHeartbeats 0 in
theorem finiteBasisChecked :
    finiteBasis.all (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · decide
  · simpa using finiteBasisCheckedFrom1

end Checks

theorem representativeModels : Models table.semigroup basis :=
  models_of_bounded_checks table Checks.defaultValue Checks.finiteBasisChecked

/-- The published Section 15 table transported to catalogue labels. -/
abbrev publishedSemigroup : Semigroup (Fin 6) :=
  table.semigroup

theorem publishedModels : Models publishedSemigroup basis :=
  representativeModels

end S6_2772
end SemigroupBasis.CoRoots.Order6SporadicSection15

