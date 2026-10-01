import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5240_36
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
theorem finiteBasisCheckedFrom19 :
    (finiteBasis.drop 19).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · rw [identity19_slice]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [checkIdentity19_decompose, tableValues]
    simp only [List.all_cons, List.all_nil, Bool.and_true,
      checkIdentity19At0_0, checkIdentity19At0_1, checkIdentity19At0_2,
      checkIdentity19At0_3, checkIdentity19At0_4, checkIdentity19At0_5]
  · simpa [List.drop_drop] using finiteBasisCheckedFrom20

end Checks

end S6_5240
end SemigroupBasis.CoRoots.Order6SporadicSection15
