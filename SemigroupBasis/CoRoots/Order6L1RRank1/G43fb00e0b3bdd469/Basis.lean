import SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469.SelectedFactorTables

/-!
# Stage-1 basis for L1R group 0603

Accepted packet `msg-0603-43fb00e0b3bdd469-design`, fingerprint
`43fb00e0b3bdd469`, selected factor pair `S4_116op x S4_64`, selected anchor
`S6_12185`, and displayed-basis SHA-256
`29d21e16b9abee63ac4b374fc5837ab7b0c089e7aa33a192ec2b773e952a06ac`.

The exact displayed basis is:

* `xx = xxx`
* `xxy = xy`
* `xyx = xyxx`
* `xyxzx = xyzx`
* `xyxzy = xyzy`
* `xyxzz = xyzxz`
* `xyzyz = xyzz`

This module certifies factor soundness only; it makes no completeness claim.
-/

namespace SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6L1RRank1

def basis : List (Identity Nat) :=
  [ law [0, 0]          [0, 0, 0],
    law [0, 0, 1]       [0, 1],
    law [0, 1, 0]       [0, 1, 0, 0],
    law [0, 1, 0, 2, 0] [0, 1, 2, 0],
    law [0, 1, 0, 2, 1] [0, 1, 2, 1],
    law [0, 1, 0, 2, 2] [0, 1, 2, 0, 2],
    law [0, 1, 2, 1, 2] [0, 1, 2, 2] ]

theorem basis_length : basis.length = 7 := by
  decide

theorem left_models :
    Models FactorTables.s4_116op.semigroup basis :=
  FiniteCertificate.checkModels_sound
    FactorTables.s4_116op basis toFinThree (by decide)

theorem right_models :
    Models FactorTables.s4_64.semigroup basis :=
  FiniteCertificate.checkModels_sound
    FactorTables.s4_64 basis toFinThree (by decide)

end SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469
