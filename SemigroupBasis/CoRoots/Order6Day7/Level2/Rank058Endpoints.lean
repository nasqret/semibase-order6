import SemigroupBasis.CoRoots.Order6Day7.Level2.Rank058FiniteFanout

/-!
# Workload58: unconditional S6_5579 endpoints

The actual class is subdirect in S3_15 and S5_203.  The unrestricted
intersection comes from the established Rank044 seed through the genuine
left-factor embedding, not from the bounded right-extension certificate.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.Level2.Rank058.S6_5579

open SemigroupBasis

abbrev table : FiniteTable := FiniteFanout.S6_5579.table

theorem representative_basis : BasisFor table.semigroup basis :=
  normalizer.basisFor leftModels rightModels FiniteFanout.S6_5579.pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.Order6Day7.Level2.Rank058.S6_5579
