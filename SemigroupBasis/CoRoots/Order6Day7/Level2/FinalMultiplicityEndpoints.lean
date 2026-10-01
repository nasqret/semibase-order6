import SemigroupBasis.CoRoots.Order6Day7.Level2.SeedRank127
import SemigroupBasis.CoRoots.Order6Day7.Level2.FinalMultiplicityFiniteFanout

/-!
# Eight unconditional endpoints for four owned C6 classes

Both unrestricted joint proofs are complete before applying the standard
split-subdirect endpoint API. Opposite orientations use literal basis
reversal. S6_8254 additionally uses the genuine shared normalizer transport
through the already proved opposite-to-direct S5_379 theory implication.
No endpoint retains an owner or completeness hypothesis.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.Level2.FinalMultiplicityEndpoints

open SemigroupBasis

namespace S6_7975

theorem representative_basis :
    BasisFor FinalMultiplicityFiniteFanout.S6_7975.table.semigroup Rank109.basis :=
  IntersectionNormalizer.basisFor Rank109.Seed.normalizer
    Rank109.leftModels Rank109.rightModels FinalMultiplicityFiniteFanout.S6_7975.pair

theorem opposite_basis :
    BasisFor FinalMultiplicityFiniteFanout.S6_7975.table.semigroup.opposite
      (reversedBasis Rank109.basis) :=
  representative_basis.oppositeReversed

end S6_7975

namespace S6_8253

theorem representative_basis :
    BasisFor FinalMultiplicityFiniteFanout.S6_8253.table.semigroup Rank109.basis :=
  IntersectionNormalizer.basisFor Rank109.Seed.normalizer
    Rank109.leftModels Rank109.rightModels FinalMultiplicityFiniteFanout.S6_8253.pair

theorem opposite_basis :
    BasisFor FinalMultiplicityFiniteFanout.S6_8253.table.semigroup.opposite
      (reversedBasis Rank109.basis) :=
  representative_basis.oppositeReversed

end S6_8253

namespace S6_7980

theorem representative_basis :
    BasisFor FinalMultiplicityFiniteFanout.S6_7980.table.semigroup Rank127.basis :=
  IntersectionNormalizer.basisFor Rank127.Seed.normalizer
    Rank127.leftModels Rank127.rightModels FinalMultiplicityFiniteFanout.S6_7980.pair

theorem opposite_basis :
    BasisFor FinalMultiplicityFiniteFanout.S6_7980.table.semigroup.opposite
      (reversedBasis Rank127.basis) :=
  representative_basis.oppositeReversed

end S6_7980

namespace S6_8254

theorem representative_basis :
    BasisFor FinalMultiplicityFiniteFanout.S6_8254.table.semigroup Rank127.basis :=
  IntersectionNormalizer.basisFor Rank127.Seed.rightOppositeNormalizer
    Rank127.leftModels Rank127.rightOppositeModels FinalMultiplicityFiniteFanout.S6_8254.pair

theorem opposite_basis :
    BasisFor FinalMultiplicityFiniteFanout.S6_8254.table.semigroup.opposite
      (reversedBasis Rank127.basis) :=
  representative_basis.oppositeReversed

end S6_8254

end SemigroupBasis.CoRoots.Order6Day7.Level2.FinalMultiplicityEndpoints
