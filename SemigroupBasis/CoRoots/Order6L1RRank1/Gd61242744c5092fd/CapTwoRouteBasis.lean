import SemigroupBasis.CoRoots.Order6L1RRank1.Common

/-!
# Route-local eleven-law basis for Gd cap-two RTC

This is the dependency-clean spelling of the accepted displayed basis.  It
contains no factor-table import or semantic completeness claim.  The list is
token-for-token identical to the basis block in the frozen provenance module.

Static off-tree source; not locally elaborated.
-/

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6L1RRank1

def basis : List (Identity Nat) :=
  [ law [0, 0]          [0, 0, 0],
    law [0, 0, 1, 0]    [0, 1, 0],
    law [0, 1, 0]       [0, 1, 0, 0],
    law [0, 1, 0, 1]    [0, 1, 1, 0],
    law [0, 1, 0, 1]    [1, 0, 0, 1],
    law [0, 1, 0, 2, 0] [0, 1, 2, 0],
    law [0, 1, 0, 2, 1] [1, 0, 0, 2, 1],
    law [0, 1, 2, 0, 1] [0, 1, 2, 1, 0],
    law [0, 1, 2, 0, 1] [0, 2, 1, 0, 1],
    law [0, 1, 2, 0, 1] [0, 2, 1, 1, 0],
    law [0, 1, 2, 0, 1] [1, 0, 2, 0, 1] ]

theorem basis_length : basis.length = 11 := by
  decide

end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
