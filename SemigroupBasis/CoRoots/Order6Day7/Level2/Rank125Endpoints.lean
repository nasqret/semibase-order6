import SemigroupBasis.CoRoots.Order6Day7.Level2.Rank125FiniteFanout

/-!
# Four unconditional rank125 endpoints from the certified factor transport

The imported seed reuses the existing unrestricted Layer-C theorem, then
transports its actual S5_791 theory to the S5_807 maps of these two classes.
No completeness, owner or finite-search premise remains on an endpoint.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.Level2.Rank125.Endpoints

open SemigroupBasis

namespace S6_13051

theorem representative_basis :
    BasisFor FiniteFanout.S6_13051.table.semigroup basis :=
  IntersectionNormalizer.basisFor normalizer leftModels rightModels FiniteFanout.S6_13051.pair

theorem opposite_basis :
    BasisFor FiniteFanout.S6_13051.table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_13051

namespace S6_13419

theorem representative_basis :
    BasisFor FiniteFanout.S6_13419.table.semigroup basis :=
  IntersectionNormalizer.basisFor normalizer leftModels rightModels FiniteFanout.S6_13419.pair

theorem opposite_basis :
    BasisFor FiniteFanout.S6_13419.table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_13419

end SemigroupBasis.CoRoots.Order6Day7.Level2.Rank125.Endpoints
