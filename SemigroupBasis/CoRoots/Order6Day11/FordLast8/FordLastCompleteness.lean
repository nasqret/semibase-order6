import SemigroupBasis.CoRoots.Order6Day11.FordLast8.FordLastHeadAlignment
import SemigroupBasis.CoRoots.Order6Day11.FordLast8.FordLastFactors
import SemigroupBasis.Subdirect

/-! Eight unconditional B9 bases and literal opposites, using exact head and lower-core validity. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLast8

open SemigroupBasis

theorem initialValid_head (identity : Identity Nat)
    (valid : identity.SatisfiedBy initialTable.semigroup) : identity.lhs.head = identity.rhs.head := by
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 := fun letter => if letter = identity.lhs.head then 0 else 1
  have tested := valid valuation
  rw [Examples.leftZeroTwo_eval, Examples.leftZeroTwo_eval] at tested
  simp [valuation, Ne.symm different] at tested

theorem derivesOfFactorValid (identity : Identity Nat)
    (initialValid : identity.SatisfiedBy initialTable.semigroup)
    (coreValid : identity.SatisfiedBy coreTable.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfHeadAndLowerValid identity.lhs identity.rhs (initialValid_head identity initialValid) coreValid

def intersectionBasis : IntersectionBasis initialTable.semigroup coreTable.semigroup basis where
  leftModels := initialModels
  rightModels := coreModels
  complete := derivesOfFactorValid

theorem derives_iff_head_lower (identity : Identity Nat) :
    Derives basis identity.lhs identity.rhs ↔
      identity.lhs.head = identity.rhs.head ∧ identity.SatisfiedBy coreTable.semigroup := by
  constructor
  · intro derived
    exact ⟨initialValid_head identity (derived.sound initialModels), derived.sound coreModels⟩
  · rintro ⟨heads, valid⟩
    exact derivesOfHeadAndLowerValid identity.lhs identity.rhs heads valid

namespace S6_7628

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
      identity.SatisfiedBy initialTable.semigroup ∧ identity.SatisfiedBy coreTable.semigroup := by
  constructor
  · intro valid
    exact ⟨validInitial identity valid, validCore identity valid⟩
  · rintro ⟨initialValid, coreValid⟩
    exact (derivesOfFactorValid identity initialValid coreValid).sound models

end S6_7628

namespace S6_7653

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
      identity.SatisfiedBy initialTable.semigroup ∧ identity.SatisfiedBy coreTable.semigroup := by
  constructor
  · intro valid
    exact ⟨validInitial identity valid, validCore identity valid⟩
  · rintro ⟨initialValid, coreValid⟩
    exact (derivesOfFactorValid identity initialValid coreValid).sound models

end S6_7653

namespace S6_7682

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
      identity.SatisfiedBy initialTable.semigroup ∧ identity.SatisfiedBy coreTable.semigroup := by
  constructor
  · intro valid
    exact ⟨validInitial identity valid, validCore identity valid⟩
  · rintro ⟨initialValid, coreValid⟩
    exact (derivesOfFactorValid identity initialValid coreValid).sound models

end S6_7682

namespace S6_7688

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
      identity.SatisfiedBy initialTable.semigroup ∧ identity.SatisfiedBy coreTable.semigroup := by
  constructor
  · intro valid
    exact ⟨validInitial identity valid, validCore identity valid⟩
  · rintro ⟨initialValid, coreValid⟩
    exact (derivesOfFactorValid identity initialValid coreValid).sound models

end S6_7688

namespace S6_7715

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
      identity.SatisfiedBy initialTable.semigroup ∧ identity.SatisfiedBy coreTable.semigroup := by
  constructor
  · intro valid
    exact ⟨validInitial identity valid, validCore identity valid⟩
  · rintro ⟨initialValid, coreValid⟩
    exact (derivesOfFactorValid identity initialValid coreValid).sound models

end S6_7715

namespace S6_7718

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
      identity.SatisfiedBy initialTable.semigroup ∧ identity.SatisfiedBy coreTable.semigroup := by
  constructor
  · intro valid
    exact ⟨validInitial identity valid, validCore identity valid⟩
  · rintro ⟨initialValid, coreValid⟩
    exact (derivesOfFactorValid identity initialValid coreValid).sound models

end S6_7718

namespace S6_8332

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
      identity.SatisfiedBy initialTable.semigroup ∧ identity.SatisfiedBy coreTable.semigroup := by
  constructor
  · intro valid
    exact ⟨validInitial identity valid, validCore identity valid⟩
  · rintro ⟨initialValid, coreValid⟩
    exact (derivesOfFactorValid identity initialValid coreValid).sound models

end S6_8332

namespace S6_11425

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
      identity.SatisfiedBy initialTable.semigroup ∧ identity.SatisfiedBy coreTable.semigroup := by
  constructor
  · intro valid
    exact ⟨validInitial identity valid, validCore identity valid⟩
  · rintro ⟨initialValid, coreValid⟩
    exact (derivesOfFactorValid identity initialValid coreValid).sound models

end S6_11425


end SemigroupBasis.CoRoots.Order6Day11.FordLast8
