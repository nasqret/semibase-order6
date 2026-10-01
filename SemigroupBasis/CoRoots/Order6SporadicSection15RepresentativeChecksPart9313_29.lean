import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart9313_28
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart9313_29At0
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart9313_29At1
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart9313_29At2
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart9313_29At3
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart9313_29At4
import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart9313_29At5

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_9313

namespace Checks

set_option maxHeartbeats 0 in
theorem finiteBasisCheckedFrom27 :
    (finiteBasis.drop 27).all
      (checkIdentityOnSupport table defaultValue) = true := by
  apply all_of_take_drop (count := 1)
  · rw [identity27_slice]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [checkIdentity27_decompose]
    rw [tableValues]
    simp only [List.all_cons, List.all_nil, Bool.and_true,
      checkIdentity27At0_0, checkIdentity27At0_1, checkIdentity27At0_2,
      checkIdentity27At0_3, checkIdentity27At0_4, checkIdentity27At0_5]
  · simpa [List.drop_drop] using finiteBasisCheckedFrom28

end Checks

end S6_9313
end SemigroupBasis.CoRoots.Order6SporadicSection15
