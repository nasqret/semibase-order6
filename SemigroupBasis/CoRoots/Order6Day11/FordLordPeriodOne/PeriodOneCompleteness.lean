import SemigroupBasis.CoRoots.Order6Day11.FordLordPeriodOne.PeriodOneBridges
import SemigroupBasis.CoRoots.Order6Day11.FordLordPeriodOne.PeriodOneFactors
import SemigroupBasis.CoRoots.Order6FordLord980RelativeTransfer

/-! Unrestricted B11 completeness by reversed rigid-endpoint transport. No conditional reach premise. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordPeriodOne

open SemigroupBasis

theorem derivesOfFactorValid (identity : Identity Nat)
    (initialValid : identity.SatisfiedBy initialTable.semigroup)
    (coreValid : identity.SatisfiedBy core840Table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have initialReversed : identity.reversed.SatisfiedBy initialTable.semigroup.opposite :=
    (Identity.satisfiedBy_opposite_iff_reversed identity.reversed initialTable.semigroup).mpr
      (by simpa only [Identity.reversed_reversed] using initialValid)
  have coreOpposite : identity.SatisfiedBy core840Table.semigroup.opposite :=
    Generated.S5_400PublishedRoots.S5_840.selfDualEmbedding.pullback_identity identity coreValid
  have coreReversed : identity.reversed.SatisfiedBy core840Table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed identity core840Table.semigroup).mp coreOpposite
  have reversedDerived :=
    CoRoots.Order6FordLord980RelativeTransfer.smallIntersectionBasis.complete
      identity.reversed initialReversed coreReversed
  have replayed := replayReversed980 reversedDerived.reverse
  simpa only [Identity.reversed, Word.reverse_reverse] using replayed

def intersectionBasis :
    IntersectionBasis initialTable.semigroup core840Table.semigroup basis where
  leftModels := initialModels
  rightModels := core840Models
  complete := derivesOfFactorValid

namespace S6_8206

theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfFactorValid identity (validInitial identity valid) (validCore identity valid)

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
      identity.SatisfiedBy initialTable.semigroup ∧ identity.SatisfiedBy core840Table.semigroup := by
  constructor
  · intro valid
    exact ⟨validInitial identity valid, validCore identity valid⟩
  · rintro ⟨initialValid, coreValid⟩
    exact (derivesOfFactorValid identity initialValid coreValid).sound models

end S6_8206

namespace S6_8264

theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfFactorValid identity (validInitial identity valid) (validCore identity valid)

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
      identity.SatisfiedBy initialTable.semigroup ∧ identity.SatisfiedBy core840Table.semigroup := by
  constructor
  · intro valid
    exact ⟨validInitial identity valid, validCore identity valid⟩
  · rintro ⟨initialValid, coreValid⟩
    exact (derivesOfFactorValid identity initialValid coreValid).sound models

end S6_8264

namespace S6_8486

theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfFactorValid identity (validInitial identity valid) (validCore identity valid)

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
      identity.SatisfiedBy initialTable.semigroup ∧ identity.SatisfiedBy core840Table.semigroup := by
  constructor
  · intro valid
    exact ⟨validInitial identity valid, validCore identity valid⟩
  · rintro ⟨initialValid, coreValid⟩
    exact (derivesOfFactorValid identity initialValid coreValid).sound models

end S6_8486

namespace S6_13340

theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfFactorValid identity (validInitial identity valid) (validCore identity valid)

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
      identity.SatisfiedBy initialTable.semigroup ∧ identity.SatisfiedBy core840Table.semigroup := by
  constructor
  · intro valid
    exact ⟨validInitial identity valid, validCore identity valid⟩
  · rintro ⟨initialValid, coreValid⟩
    exact (derivesOfFactorValid identity initialValid coreValid).sound models

end S6_13340

namespace S6_13376

theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfFactorValid identity (validInitial identity valid) (validCore identity valid)

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
      identity.SatisfiedBy initialTable.semigroup ∧ identity.SatisfiedBy core840Table.semigroup := by
  constructor
  · intro valid
    exact ⟨validInitial identity valid, validCore identity valid⟩
  · rintro ⟨initialValid, coreValid⟩
    exact (derivesOfFactorValid identity initialValid coreValid).sound models

end S6_13376

namespace S6_13610

theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfFactorValid identity (validInitial identity valid) (validCore identity valid)

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
      identity.SatisfiedBy initialTable.semigroup ∧ identity.SatisfiedBy core840Table.semigroup := by
  constructor
  · intro valid
    exact ⟨validInitial identity valid, validCore identity valid⟩
  · rintro ⟨initialValid, coreValid⟩
    exact (derivesOfFactorValid identity initialValid coreValid).sound models

end S6_13610


end SemigroupBasis.CoRoots.Order6Day11.FordLordPeriodOne
