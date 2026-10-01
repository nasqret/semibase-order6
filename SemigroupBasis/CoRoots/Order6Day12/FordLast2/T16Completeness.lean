import SemigroupBasis.CoRoots.Order6Day12.FordLast2.T16LastAlignment
import SemigroupBasis.CoRoots.Order6Day12.FordLast2.T16Factors

/-! One complete factor intersection yields both actual B9 bases and their
literal opposites. No normalizer, reach, rank or length premise remains. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day12.FordLast2

open SemigroupBasis

def intersectionBasis : IntersectionBasis finalTable.semigroup coreTable.semigroup basis where
  leftModels := finalModels
  rightModels := coreModels
  complete := by
    intro identity finalValid coreValid
    exact derivesOfLastAndCoreValid identity.lhs identity.rhs
      (lastOfFinalValid identity finalValid) coreValid

namespace S6_10934

theorem basisFor : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor pair

theorem oppositeBasisFor : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem valid_iff_derives (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ Derives basis identity.lhs identity.rhs := by
  constructor
  · exact basisFor.2 identity
  · intro derived
    exact derived.sound models

end S6_10934

namespace S6_11222

theorem basisFor : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor pair

theorem oppositeBasisFor : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem valid_iff_derives (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ Derives basis identity.lhs identity.rhs := by
  constructor
  · exact basisFor.2 identity
  · intro derived
    exact derived.sound models

end S6_11222

end SemigroupBasis.CoRoots.Order6Day12.FordLast2
