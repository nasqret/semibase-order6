import SemigroupBasis.CoRoots.Order6FordLord1ccaRelativeTransfer
import SemigroupBasis.Generated.Order6FordLordInvariantWrapperSkeletons

/-!
# Unconditional `1ccaef90de83de0a` order-six endpoints

The six generated wrappers share the three factor intersections constructed
by `Order6FordLord1ccaRelativeTransfer`.  Both orientations are exposed here
without conditional intersection arguments.
-/

namespace SemigroupBasis.Generated.Order6FordLordInvariantWrapperSkeletons

open SemigroupBasis

private abbrev I788 :=
  SemigroupBasis.CoRoots.Order6FordLord1ccaRelativeTransfer.intersectionBasisS5_788

private abbrev I805 :=
  SemigroupBasis.CoRoots.Order6FordLord1ccaRelativeTransfer.intersectionBasisS5_805

private abbrev I811 :=
  SemigroupBasis.CoRoots.Order6FordLord1ccaRelativeTransfer.intersectionBasisS5_811

namespace S6_12950

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of I788

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of I788

end S6_12950

namespace S6_13045

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of I805

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of I805

end S6_13045

namespace S6_13061

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of I811

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of I811

end S6_13061

namespace S6_13330

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of I788

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of I788

end S6_13330

namespace S6_13407

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of I805

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of I805

end S6_13407

namespace S6_13438

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of I811

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of I811

end S6_13438

end SemigroupBasis.Generated.Order6FordLordInvariantWrapperSkeletons
