import SemigroupBasis.CoRoots.Order6Day14.S9498.S9498Padding
import SemigroupBasis.CoRoots.Order6Day14.S9498.S9498Factors

/-! Unconditional completeness for the actual S6_9498 table and its
standard reversed-basis opposite. No bounded screen or finite orbit is
used as a premise of these arbitrary-word theorems. -/

namespace SemigroupBasis.CoRoots.Order6Day14.S9498

open SemigroupBasis

theorem complete (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have invariant := factors_imply_invariant identity leftValid rightValid
  exact derivesOfHeadAndInvariant identity.lhs identity.rhs invariant.1 invariant.2

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := complete

namespace S6_9498

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

end S6_9498

theorem isBasisFor_9498_direct : BasisFor S6_9498.table.semigroup basis :=
  S6_9498.basisFor

theorem isBasisFor_9498_opposite : BasisFor S6_9498.table.semigroup.opposite dualBasis :=
  S6_9498.oppositeBasisFor

end SemigroupBasis.CoRoots.Order6Day14.S9498
