import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_379
import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank105FiniteFanout

/-!
# Twelve unconditional rank105 class endpoints

The unrestricted nine-law seed is already proved in `SeedS5_379`.
The kernel-green shared transportNormalizer preserves that actual seed and
uses the proved right-opposite theory implication for the three targets
requiring it. The finite subdirect maps are exact catalogue-coordinate maps.
No endpoint retains a normalizer, derivability, or completeness hypothesis.
This warm source does not itself assert independent carrier review, WMI
acceptance, sealing, or a census movement.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank105.Endpoints

open SemigroupBasis
open SemigroupBasis.CoRoots
open FiniteFanout

/-- Reuse the approved shared transport API with the same exact nine laws. -/
noncomputable def rightOppositeNormalizer :
    IntersectionNormalizer leftTable.semigroup rightOppositeTable.semigroup basis :=
  Order6L3HeavyRank2.LayerCCommon.transportNormalizer Seed.normalizer
    (fun _ member => Derives.fromBasis member)
    (fun _ valid => valid) rightTheoryFromOpposite

namespace S6_7954

theorem representative_basis : BasisFor FiniteFanout.S6_7954.table.semigroup basis :=
  IntersectionNormalizer.basisFor Seed.normalizer leftModels rightModels
    FiniteFanout.S6_7954.pair

theorem opposite_basis :
    BasisFor FiniteFanout.S6_7954.table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_7954

namespace S6_7984

theorem representative_basis : BasisFor FiniteFanout.S6_7984.table.semigroup basis :=
  IntersectionNormalizer.basisFor Seed.normalizer leftModels rightModels
    FiniteFanout.S6_7984.pair

theorem opposite_basis :
    BasisFor FiniteFanout.S6_7984.table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_7984

namespace S6_8134

theorem representative_basis : BasisFor FiniteFanout.S6_8134.table.semigroup basis :=
  IntersectionNormalizer.basisFor rightOppositeNormalizer leftModels rightOppositeModels
    FiniteFanout.S6_8134.pair

theorem opposite_basis :
    BasisFor FiniteFanout.S6_8134.table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8134

namespace S6_8140

theorem representative_basis : BasisFor FiniteFanout.S6_8140.table.semigroup basis :=
  IntersectionNormalizer.basisFor rightOppositeNormalizer leftModels rightOppositeModels
    FiniteFanout.S6_8140.pair

theorem opposite_basis :
    BasisFor FiniteFanout.S6_8140.table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8140

namespace S6_11028

theorem representative_basis : BasisFor FiniteFanout.S6_11028.table.semigroup basis :=
  IntersectionNormalizer.basisFor Seed.normalizer leftModels rightModels
    FiniteFanout.S6_11028.pair

theorem opposite_basis :
    BasisFor FiniteFanout.S6_11028.table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_11028

namespace S6_11086

theorem representative_basis : BasisFor FiniteFanout.S6_11086.table.semigroup basis :=
  IntersectionNormalizer.basisFor rightOppositeNormalizer leftModels rightOppositeModels
    FiniteFanout.S6_11086.pair

theorem opposite_basis :
    BasisFor FiniteFanout.S6_11086.table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_11086

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank105.Endpoints
