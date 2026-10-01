import SemigroupBasis.CoRoots.Order6S4_96OppositeCubeIntersectionCounterexample
import SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupCompleteness

namespace SemigroupBasis.Order6.S6_14897

open SemigroupBasis

abbrev table : FiniteTable :=
  SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.table

/-- The previously recorded singleton candidate. -/
def cubeCandidate : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.basis

theorem cubeCandidate_models :
    Models table.semigroup cubeCandidate := by
  simpa [table, cubeCandidate] using
    SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.basis_models

/-- Terminal rejection of the false singleton endpoint. -/
theorem cubeCandidate_not_basisFor :
    ¬ BasisFor table.semigroup cubeCandidate := by
  simpa [table, cubeCandidate] using
    SemigroupBasis.CoRoots.Order6S4_96OppositeCubeIntersectionCounterexample.cubeBasis_not_basisFor_target

/-- The precise common-factor completeness claim rejected by the finite
countermodel. -/
theorem cubeCandidate_not_intersectionBasis :
    ¬ IntersectionBasis
      SemigroupBasis.Examples.affineParityFour.semigroup
      SemigroupBasis.Examples.affineParityFour.semigroup.opposite
      cubeCandidate := by
  simpa [cubeCandidate] using
    SemigroupBasis.CoRoots.Order6S4_96OppositeCubeIntersectionCounterexample.cubeBasis_not_intersectionBasis

/-- Complete two-law basis `x = x³`, `xyzx = xyxxzx`. -/
abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.basis

def oppositeBasis : List (Identity Nat) := reversedBasis basis

def tableSHA256 : String :=
  "c1658d72366bc69986ae0ce27042416d25bde6d6623d983b079f3eaa20963f6a"

def tableRowsOneBased : List (List Nat) :=
  SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.tableOneBased

/-- The endpoint table is exactly the committed Smallsemi representative. -/
theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 2, 3, 4, 5, 6],
       [2, 1, 4, 3, 6, 5],
       [3, 5, 3, 3, 5, 5],
       [4, 6, 4, 4, 6, 6],
       [5, 3, 3, 3, 5, 5],
       [6, 4, 4, 4, 6, 6]] :=
  SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.tableOneBased_certificate

theorem basis_models :
    Models table.semigroup basis := by
  simpa [table, basis] using
    SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.basis_models

theorem representative_basis :
    BasisFor table.semigroup basis := by
  simpa [table, basis] using
    SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.basis_complete

/-- Compatibility name used by the original completeness development. -/
theorem basisFor : BasisFor table.semigroup basis :=
  representative_basis

/-- Reversal gives the corresponding endpoint for the opposite table. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end SemigroupBasis.Order6.S6_14897
