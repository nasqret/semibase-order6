import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415.Profile1415GoodSignature

/-! Four unrestricted literal-table B32 endpoints and their reversals. -/

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415

open SemigroupBasis

theorem derivesOfFactorValid (identity : Identity Nat)
    (cyclicValid : identity.SatisfiedBy cyclicTable.semigroup)
    (separatorValid : identity.SatisfiedBy separatorTable.semigroup)
    (initialValid : identity.SatisfiedBy initialTable.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameSignature
    (sameSignatureOfFactorValid identity cyclicValid separatorValid initialValid)

namespace S6_10967

theorem valid_sameSignature (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSignature identity.lhs identity.rhs :=
  sameSignatureOfFactorValid identity (validCyclic identity valid)
    (validSeparator identity valid) (validInitial identity valid)

theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfSameSignature (valid_sameSignature identity valid)

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem valid_iff_signature (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ SameSignature identity.lhs identity.rhs :=
  ⟨valid_sameSignature identity, fun same => (derivesOfSameSignature same).sound models⟩

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      identity.SatisfiedBy cyclicTable.semigroup ∧
      identity.SatisfiedBy separatorTable.semigroup ∧
      identity.SatisfiedBy initialTable.semigroup := by
  constructor
  · intro valid
    exact ⟨validCyclic identity valid, validSeparator identity valid, validInitial identity valid⟩
  · rintro ⟨cyclic, separator, initial⟩
    exact (derivesOfFactorValid identity cyclic separator initial).sound models

end S6_10967

namespace S6_10976

theorem valid_sameSignature (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSignature identity.lhs identity.rhs :=
  sameSignatureOfFactorValid identity (validCyclic identity valid)
    (validSeparator identity valid) (validInitial identity valid)

theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfSameSignature (valid_sameSignature identity valid)

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem valid_iff_signature (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ SameSignature identity.lhs identity.rhs :=
  ⟨valid_sameSignature identity, fun same => (derivesOfSameSignature same).sound models⟩

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      identity.SatisfiedBy cyclicTable.semigroup ∧
      identity.SatisfiedBy separatorTable.semigroup ∧
      identity.SatisfiedBy initialTable.semigroup := by
  constructor
  · intro valid
    exact ⟨validCyclic identity valid, validSeparator identity valid, validInitial identity valid⟩
  · rintro ⟨cyclic, separator, initial⟩
    exact (derivesOfFactorValid identity cyclic separator initial).sound models

end S6_10976

namespace S6_11300

theorem valid_sameSignature (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSignature identity.lhs identity.rhs :=
  sameSignatureOfFactorValid identity (validCyclic identity valid)
    (validSeparator identity valid) (validInitial identity valid)

theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfSameSignature (valid_sameSignature identity valid)

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem valid_iff_signature (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ SameSignature identity.lhs identity.rhs :=
  ⟨valid_sameSignature identity, fun same => (derivesOfSameSignature same).sound models⟩

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      identity.SatisfiedBy cyclicTable.semigroup ∧
      identity.SatisfiedBy separatorTable.semigroup ∧
      identity.SatisfiedBy initialTable.semigroup := by
  constructor
  · intro valid
    exact ⟨validCyclic identity valid, validSeparator identity valid, validInitial identity valid⟩
  · rintro ⟨cyclic, separator, initial⟩
    exact (derivesOfFactorValid identity cyclic separator initial).sound models

end S6_11300

namespace S6_11412

theorem valid_sameSignature (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSignature identity.lhs identity.rhs :=
  sameSignatureOfFactorValid identity (validCyclic identity valid)
    (validSeparator identity valid) (validInitial identity valid)

theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfSameSignature (valid_sameSignature identity valid)

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem valid_iff_signature (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ SameSignature identity.lhs identity.rhs :=
  ⟨valid_sameSignature identity, fun same => (derivesOfSameSignature same).sound models⟩

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      identity.SatisfiedBy cyclicTable.semigroup ∧
      identity.SatisfiedBy separatorTable.semigroup ∧
      identity.SatisfiedBy initialTable.semigroup := by
  constructor
  · intro valid
    exact ⟨validCyclic identity valid, validSeparator identity valid, validInitial identity valid⟩
  · rintro ⟨cyclic, separator, initial⟩
    exact (derivesOfFactorValid identity cyclic separator initial).sound models

end S6_11412

end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415
