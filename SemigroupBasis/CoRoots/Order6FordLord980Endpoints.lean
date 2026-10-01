import SemigroupBasis.CoRoots.Order6FordLord980RelativeTransfer
import SemigroupBasis.Generated.Order6FordLordInvariantWrapperSkeletons

/-!
# Unconditional `9808750adcf41d94` order-six endpoint

The relative transfer supplies the preferred `S3_15^op x S5_840`
intersection for the generated `S6_13411` wrapper.
-/

namespace SemigroupBasis.Generated.Order6FordLordInvariantWrapperSkeletons

open SemigroupBasis

private abbrev intersection :=
  SemigroupBasis.CoRoots.Order6FordLord980RelativeTransfer.intersectionBasis

namespace S6_13411

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of intersection

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of intersection

end S6_13411

end SemigroupBasis.Generated.Order6FordLordInvariantWrapperSkeletons
