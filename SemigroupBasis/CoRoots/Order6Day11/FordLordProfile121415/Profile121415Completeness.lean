import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile121415.Profile121415SeedBridge
import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile121415.Profile121415Factors

/-! Seven unconditional C/25 class endpoints and their literal reversals.
The full exact signature is parity, support, exact separator cuts, and first.
No skeleton equality, finite bound, or owner obligation enters an endpoint. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile121415

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day7.S3_11

abbrev SameSignature (left right : Word Nat) : Prop :=
  SeedS5_796Opposite.SameFixedHeadParitySeparatorSignature left right

/-- The three actual factor theories give precisely the reused signature. -/
theorem sameSignatureOfFactorValid (identity : Identity Nat)
    (cyclicValid : identity.SatisfiedBy cyclicTable.semigroup)
    (separatorValid : identity.SatisfiedBy separatorTable.semigroup)
    (firstValid : identity.SatisfiedBy firstTable.semigroup) :
    SameSignature identity.lhs identity.rhs := by
  have lower := SemigroupBasis.CoRoots.S5_787Invariant.sameSignature_of_s4_69_s2_4_valid
    identity separatorValid firstValid
  exact ⟨⟨lower.support, lower.exactCuts,
    Examples.cyclicValid_parity_eq identity cyclicValid⟩, lower.first⟩

theorem derivesOfFactorValid (identity : Identity Nat)
    (cyclicValid : identity.SatisfiedBy cyclicTable.semigroup)
    (separatorValid : identity.SatisfiedBy separatorTable.semigroup)
    (firstValid : identity.SatisfiedBy firstTable.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameSignature (sameSignatureOfFactorValid identity cyclicValid separatorValid firstValid)

namespace S6_8856

theorem valid_sameSignature (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSignature identity.lhs identity.rhs :=
  sameSignatureOfFactorValid identity (validCyclic identity valid)
    (validSeparator identity valid) (validFirst identity valid)

/-- Every valid Identity Nat, with no rank or word-length restriction. -/
theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfSameSignature (valid_sameSignature identity valid)

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem valid_iff_signature (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ SameSignature identity.lhs identity.rhs := by
  constructor
  · exact valid_sameSignature identity
  · intro same
    exact (derivesOfSameSignature same).sound models

end S6_8856

namespace S6_9004

theorem valid_sameSignature (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSignature identity.lhs identity.rhs :=
  sameSignatureOfFactorValid identity (validCyclic identity valid)
    (validSeparator identity valid) (validFirst identity valid)

/-- Every valid Identity Nat, with no rank or word-length restriction. -/
theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfSameSignature (valid_sameSignature identity valid)

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem valid_iff_signature (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ SameSignature identity.lhs identity.rhs := by
  constructor
  · exact valid_sameSignature identity
  · intro same
    exact (derivesOfSameSignature same).sound models

end S6_9004

namespace S6_10949

theorem valid_sameSignature (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSignature identity.lhs identity.rhs :=
  sameSignatureOfFactorValid identity (validCyclic identity valid)
    (validSeparator identity valid) (validFirst identity valid)

/-- Every valid Identity Nat, with no rank or word-length restriction. -/
theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfSameSignature (valid_sameSignature identity valid)

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem valid_iff_signature (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ SameSignature identity.lhs identity.rhs := by
  constructor
  · exact valid_sameSignature identity
  · intro same
    exact (derivesOfSameSignature same).sound models

end S6_10949

namespace S6_10951

theorem valid_sameSignature (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSignature identity.lhs identity.rhs :=
  sameSignatureOfFactorValid identity (validCyclic identity valid)
    (validSeparator identity valid) (validFirst identity valid)

/-- Every valid Identity Nat, with no rank or word-length restriction. -/
theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfSameSignature (valid_sameSignature identity valid)

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem valid_iff_signature (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ SameSignature identity.lhs identity.rhs := by
  constructor
  · exact valid_sameSignature identity
  · intro same
    exact (derivesOfSameSignature same).sound models

end S6_10951

namespace S6_11227

theorem valid_sameSignature (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSignature identity.lhs identity.rhs :=
  sameSignatureOfFactorValid identity (validCyclic identity valid)
    (validSeparator identity valid) (validFirst identity valid)

/-- Every valid Identity Nat, with no rank or word-length restriction. -/
theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfSameSignature (valid_sameSignature identity valid)

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem valid_iff_signature (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ SameSignature identity.lhs identity.rhs := by
  constructor
  · exact valid_sameSignature identity
  · intro same
    exact (derivesOfSameSignature same).sound models

end S6_11227

namespace S6_11299

theorem valid_sameSignature (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSignature identity.lhs identity.rhs :=
  sameSignatureOfFactorValid identity (validCyclic identity valid)
    (validSeparator identity valid) (validFirst identity valid)

/-- Every valid Identity Nat, with no rank or word-length restriction. -/
theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfSameSignature (valid_sameSignature identity valid)

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem valid_iff_signature (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ SameSignature identity.lhs identity.rhs := by
  constructor
  · exact valid_sameSignature identity
  · intro same
    exact (derivesOfSameSignature same).sound models

end S6_11299

namespace S6_11410

theorem valid_sameSignature (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSignature identity.lhs identity.rhs :=
  sameSignatureOfFactorValid identity (validCyclic identity valid)
    (validSeparator identity valid) (validFirst identity valid)

/-- Every valid Identity Nat, with no rank or word-length restriction. -/
theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfSameSignature (valid_sameSignature identity valid)

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem valid_iff_signature (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ SameSignature identity.lhs identity.rhs := by
  constructor
  · exact valid_sameSignature identity
  · intro same
    exact (derivesOfSameSignature same).sound models

end S6_11410

/-- C's sandwich collapse changes capped counts, so that skeleton is not exact. -/
def cap22 (count : Nat) : Nat := if count < 2 then count else 2 + count % 2

theorem sandwich_changes_capped_count :
    cap22 (law03.lhs.toList.count 1) ≠ cap22 (law03.rhs.toList.count 1) := by decide

theorem capped_count_not_necessary :
    ¬ (∀ identity : Identity Nat, identity.SatisfiedBy S6_8856.table.semigroup →
      ∀ letter, cap22 (identity.lhs.toList.count letter) =
        cap22 (identity.rhs.toList.count letter)) := by
  intro asserted
  exact sandwich_changes_capped_count
    (asserted law03 (S6_8856.models law03 (by decide)) 1)

end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile121415

