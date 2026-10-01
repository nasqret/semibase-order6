import SemigroupBasis.CoRoots.S5_381Family

/-! Observations of the already-complete S5_610 core, viewed in the opposite
orientation. No order-six basis or new reach theorem occurs in this module.
The capped/support/simple wrapper follows the FordLast4 source template. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day12.FordLast2

open SemigroupBasis

abbrev coreTable : FiniteTable := Generated.Catalogue.S5_610.table
abbrev reversedCore : Semigroup (Fin 5) := coreTable.semigroup.opposite

structure LowerSignature (left right : Word Nat) : Prop where
  capped : ∀ letter,
    SemigroupBasis.CoRoots.S5_107.cappedMultiplicity left letter =
      SemigroupBasis.CoRoots.S5_107.cappedMultiplicity right letter

namespace LowerSignature

theorem symm {left right : Word Nat} (same : LowerSignature left right) :
    LowerSignature right left := ⟨fun letter => (same.capped letter).symm⟩

theorem support {left right : Word Nat} (same : LowerSignature left right) (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList := by
  have absent : letter ∉ left.toList ↔ letter ∉ right.toList := by
    rw [← List.count_eq_zero, ← List.count_eq_zero,
      ← SemigroupBasis.CoRoots.S5_107.cappedMultiplicity_eq_zero_iff,
      ← SemigroupBasis.CoRoots.S5_107.cappedMultiplicity_eq_zero_iff,
      same.capped letter]
  simpa using not_congr absent

theorem simple {left right : Word Nat} (same : LowerSignature left right) (letter : Nat) :
    SemigroupBasis.CoRoots.S5_107.SimpleIn left letter ↔
      SemigroupBasis.CoRoots.S5_107.SimpleIn right letter := by
  unfold SemigroupBasis.CoRoots.S5_107.SimpleIn
  rw [← SemigroupBasis.CoRoots.S5_107.cappedMultiplicity_eq_one_iff,
    ← SemigroupBasis.CoRoots.S5_107.cappedMultiplicity_eq_one_iff,
    same.capped letter]

end LowerSignature

theorem validLowerSignature (identity : Identity Nat)
    (valid : identity.SatisfiedBy reversedCore) :
    LowerSignature identity.lhs identity.rhs := by
  have directValid : identity.reversed.SatisfiedBy coreTable.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed identity coreTable.semigroup).mp valid
  have same := SemigroupBasis.CoRoots.S5_381FamilyInvariant.S5_610.valid_sameSignature
    identity.reversed directValid
  refine ⟨?_⟩
  intro letter
  simpa [Identity.reversed, SemigroupBasis.CoRoots.S5_107.cappedMultiplicity] using same.capped letter

/-- This is the LEFT unit of the opposite core, hence the RIGHT unit of S5_610. -/
theorem coreLeftUnit : ∀ value : Fin 5, reversedCore.mul (4 : Fin 5) value = value := by decide

end SemigroupBasis.CoRoots.Order6Day12.FordLast2
