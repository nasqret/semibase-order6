import SemigroupBasis.CoRoots.Order6Day14.S15931.S15931Inflation
import SemigroupBasis.CoRoots.Order6Day14.S15931.S15931Factors

/-! Unconditional completeness for the actual S6_15931 table. The two
factor-validity hypotheses are discharged by the literal subdirect pair.
Neither a finite-screen bound nor an unproved reach statement is a premise. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day14.S15931

open SemigroupBasis

theorem complete (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have heads : identity.lhs.head = identity.rhs.head :=
    Examples.leftNormalBandFifteenValid_head_eq identity leftValid
  have signature : SemigroupBasis.CoRoots.S5_1155.SameSemanticSignature
      identity.lhs identity.rhs :=
    SemigroupBasis.CoRoots.S5_1155.sameSemanticSignature_of_valid identity rightValid
  exact derivesOfHeadAndSignature identity.lhs identity.rhs heads signature

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := complete

namespace S6_15931

theorem basisFor : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor pair

theorem oppositeBasisFor : BasisFor table.semigroup.opposite dualBasis :=
  basisFor.oppositeReversed

theorem valid_iff_derives (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ Derives basis identity.lhs identity.rhs := by
  constructor
  · exact basisFor.2 identity
  · intro derivation valuation
    exact derivation.sound basisFor.1 valuation

theorem opposite_valid_iff_derives (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup.opposite ↔ Derives dualBasis identity.lhs identity.rhs := by
  constructor
  · exact oppositeBasisFor.2 identity
  · intro derivation valuation
    exact derivation.sound oppositeBasisFor.1 valuation

end S6_15931

theorem isBasisFor_15931_direct : BasisFor S6_15931.table.semigroup basis :=
  S6_15931.basisFor

theorem isBasisFor_15931_opposite : BasisFor S6_15931.table.semigroup.opposite dualBasis :=
  S6_15931.oppositeBasisFor

end SemigroupBasis.CoRoots.Order6Day14.S15931
