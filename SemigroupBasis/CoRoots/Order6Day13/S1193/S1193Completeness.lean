import SemigroupBasis.CoRoots.Order6Day13.S1193.S1193Bridge
import SemigroupBasis.CoRoots.Order6Day13.S1193.S1193Factors
import SemigroupBasis.CoRoots.Order6FactorPairS3_6S5_110Normal

/-! Unrestricted S6_1193 completeness from the proved reversed intersection,
the actual split factor maps, and four explicit displayed-law bridges.
No rank, length, search, reach, renderer or normalizer premise remains. -/

namespace SemigroupBasis.CoRoots.Order6Day13.S1193

open SemigroupBasis

def sourceIntersection : IntersectionBasis leftTable.semigroup rightTable.semigroup sourceBasis :=
  Order6FactorPairS3_6S5_110.intersectionBasis.oppositeReversed

namespace S6_1193

theorem sourceBasisFor : BasisFor table.semigroup sourceBasis :=
  sourceIntersection.basisFor pair

theorem basisFor : BasisFor table.semigroup basis :=
  sourceBasisFor.replace models sourceLawDerives

theorem oppositeBasisFor : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem valid_iff_derives (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ Derives basis identity.lhs identity.rhs := by
  constructor
  · exact basisFor.2 identity
  · intro derived
    exact derived.sound models

theorem opposite_valid_iff_derives (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup.opposite ↔
      Derives (reversedBasis basis) identity.lhs identity.rhs := by
  constructor
  · exact oppositeBasisFor.2 identity
  · intro derived
    exact derived.sound oppositeBasisFor.1

end S6_1193
end SemigroupBasis.CoRoots.Order6Day13.S1193
