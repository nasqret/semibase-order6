import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5241_36
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5241HeavyAt0
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5241HeavyAt1
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5241HeavyAt2
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5241HeavyAt3
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5241HeavyAt4
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart5241HeavyAt5

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_5241

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

end S6_5241
end SemigroupBasis.CoRoots.Order6SporadicSection15
