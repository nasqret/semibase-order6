import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5240_28
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5240_37At0
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5240_37At1
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5240_37At2
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5240_37At3
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5240_37At4
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5240_37At5

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_5240

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom27 :
    (finiteBasis.drop 27).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · rw [identity27_slice]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [checkIdentity27_decompose, tableValues]
    simp only [List.all_cons, List.all_nil, Bool.and_true,
      checkIdentity27At0_0, checkIdentity27At0_1, checkIdentity27At0_2,
      checkIdentity27At0_3, checkIdentity27At0_4, checkIdentity27At0_5]
  · simpa [List.drop_drop] using finiteBasisCheckedFrom28

end Checks

end S6_5240
end SemigroupBasis.CoRoots.Order6SporadicSection15
