import SemigroupBasis.CoRoots.Order6L1RRank1.Gca80a5da838636f5.SelectedFactorTables

/-!
# Stage-1 basis for L1R group 0604

Accepted packet `msg-0604-ca80a5da838636f5-design`, fingerprint
`ca80a5da838636f5`, selected factor pair `S4_116op x S4_73`, selected anchor
`S6_12774`, and displayed-basis SHA-256
`f92726c4ea660efd9180c6910d04ccb32e2dcd67a840db0029c7a255ff4926fb`.

The exact displayed basis is:

* `xx = xxx`
* `xxy = xyxy`
* `xxyxz = xyxz`
* `xxyzx = xyzx`
* `xxyzy = xyxzy`
* `xy = xyy`
* `xyxz = xyzxz`
* `xyxzx = xyzx`

This module certifies factor soundness only; it makes no completeness claim.
-/

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gca80a5da838636f5

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6L1RRank1

def basis : List (Identity Nat) :=
  [ law [0, 0]          [0, 0, 0],
    law [0, 0, 1]       [0, 1, 0, 1],
    law [0, 0, 1, 0, 2] [0, 1, 0, 2],
    law [0, 0, 1, 2, 0] [0, 1, 2, 0],
    law [0, 0, 1, 2, 1] [0, 1, 0, 2, 1],
    law [0, 1]          [0, 1, 1],
    law [0, 1, 0, 2]    [0, 1, 2, 0, 2],
    law [0, 1, 0, 2, 0] [0, 1, 2, 0] ]

theorem basis_length : basis.length = 8 := by
  decide

theorem left_models :
    Models FactorTables.s4_116op.semigroup basis :=
  FiniteCertificate.checkModels_sound
    FactorTables.s4_116op basis toFinThree (by decide)

theorem right_models :
    Models FactorTables.s4_73.semigroup basis :=
  FiniteCertificate.checkModels_sound
    FactorTables.s4_73 basis toFinThree (by decide)

end SemigroupBasis.CoRoots.Order6L1RRank1.Gca80a5da838636f5
