import SemigroupBasis.CoRoots.Order6Day13.FordLord2.FL2LastAlignment
import SemigroupBasis.CoRoots.Order6Day13.FordLord2.FL2Factors

/-! One unrestricted factor-intersection calculus yields both literal B9
bases and their opposites. The sibling uses a core embedding into its
square, not an unavailable quotient. No rank, length, reach, classification,
normalizer, or unit premise remains in an endpoint. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day13.FordLord2

open SemigroupBasis

theorem derivesOfFactorValid (identity : Identity Nat)
    (finalValid : identity.SatisfiedBy finalTable.semigroup)
    (coreValid : identity.SatisfiedBy coreTable.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfLastAndCoreValid identity.lhs identity.rhs
    (lastOfFinalValid identity finalValid) coreValid

def intersectionBasis : IntersectionBasis finalTable.semigroup coreTable.semigroup basis where
  leftModels := finalModels
  rightModels := coreModels
  complete := derivesOfFactorValid

theorem derives_iff_last_core (identity : Identity Nat) :
    Derives basis identity.lhs identity.rhs ↔
      identity.lhs.reverse.head = identity.rhs.reverse.head ∧
        identity.SatisfiedBy coreTable.semigroup := by
  constructor
  · intro derived
    exact ⟨lastOfFinalValid identity (derived.sound finalModels), derived.sound coreModels⟩
  · rintro ⟨lasts, valid⟩
    exact derivesOfLastAndCoreValid identity.lhs identity.rhs lasts valid

namespace S6_7974

theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfFactorValid identity (validFinal identity valid) (validCore identity valid)

theorem oppositeBasisFor : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem valid_iff_derives (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ Derives basis identity.lhs identity.rhs := by
  constructor
  · exact basisFor.2 identity
  · intro derived
    exact derived.sound models

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      identity.SatisfiedBy finalTable.semigroup ∧ identity.SatisfiedBy coreTable.semigroup := by
  constructor
  · intro valid
    exact ⟨validFinal identity valid, validCore identity valid⟩
  · rintro ⟨finalValid, coreValid⟩
    exact (derivesOfFactorValid identity finalValid coreValid).sound models

end S6_7974

namespace S6_8252

theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfFactorValid identity (validFinal identity valid) (validCore identity valid)

theorem oppositeBasisFor : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem valid_iff_derives (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ Derives basis identity.lhs identity.rhs := by
  constructor
  · exact basisFor.2 identity
  · intro derived
    exact derived.sound models

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      identity.SatisfiedBy finalTable.semigroup ∧ identity.SatisfiedBy coreTable.semigroup := by
  constructor
  · intro valid
    exact ⟨validFinal identity valid, validCore identity valid⟩
  · rintro ⟨finalValid, coreValid⟩
    exact (derivesOfFactorValid identity finalValid coreValid).sound models

end S6_8252

end SemigroupBasis.CoRoots.Order6Day13.FordLord2
