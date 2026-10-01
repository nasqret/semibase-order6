import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.Profile15Alignment

/-! Unrestricted completeness for the literal section-A representative.
Necessity is the exact-table key theorem; sufficiency is the constructive
global count reduction and growing-prefix alignment from the sixteen laws. -/

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15

open SemigroupBasis

theorem derives_iff_sameKey (left right : Word Nat) :
    Derives basis left right ↔ KeyTheory.SameKey left.toList right.toList :=
  ⟨KeyTheory.derives_sameKey, Alignment.derivesOfSameKey left right⟩

namespace Representative

theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact Alignment.derivesOfSameKey identity.lhs identity.rhs (KeyTheory.valid_sameKey identity valid)

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  basisForOpposite.1

theorem valid_iff_sameKey (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ KeyTheory.SameKey identity.lhs.toList identity.rhs.toList :=
  ⟨KeyTheory.valid_sameKey identity,
    fun same => (Alignment.derivesOfSameKey identity.lhs identity.rhs same).sound models⟩

end Representative
end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15
