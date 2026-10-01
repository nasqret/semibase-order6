import SemigroupBasis.CoRoots.Order6FordLordAe8DualTransfer
import SemigroupBasis.Generated.Order6FordLordInvariantWrapperSkeletons

/-!
# Unconditional ae8 order-six endpoints

The five wrapper tables share the three factor intersections constructed by
`Order6FordLordAe8DualTransfer`.  Both representative and opposite basis
theorems are exposed here without conditional arguments.
-/

namespace SemigroupBasis.Generated.Order6FordLordInvariantWrapperSkeletons

open SemigroupBasis

private abbrev I794 :=
  SemigroupBasis.CoRoots.Order6FordLordAe8DualTransfer.intersectionBasisS5_794

private abbrev I802 :=
  SemigroupBasis.CoRoots.Order6FordLordAe8DualTransfer.intersectionBasisS5_802

private abbrev I810 :=
  SemigroupBasis.CoRoots.Order6FordLordAe8DualTransfer.intersectionBasisS5_810

namespace S6_12965

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of I794

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of I794

end S6_12965

namespace S6_13056

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of I810

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of I810

end S6_13056

namespace S6_13366

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of I794

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of I794

end S6_13366

namespace S6_13401

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of I802

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of I802

end S6_13401

namespace S6_13433

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of I810

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of I810

end S6_13433

end SemigroupBasis.Generated.Order6FordLordInvariantWrapperSkeletons
