import SemigroupBasis.CoRoots.S5_808

/-! Observations of the already-complete S5_808 core. This module contains
no order-six displayed basis, no new reach theorem and no class endpoint. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day12.FordLast4

open SemigroupBasis

abbrev coreTable : FiniteTable := Generated.Catalogue.S5_808.table

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
    (valid : identity.SatisfiedBy coreTable.semigroup) :
    LowerSignature identity.lhs identity.rhs := by
  have oppositeValid : identity.reversed.SatisfiedBy coreTable.semigroup.opposite :=
    (Identity.satisfiedBy_opposite_iff_reversed identity.reversed coreTable.semigroup).mpr
      (by simpa only [Identity.reversed_reversed] using valid)
  have rootValid := SemigroupBasis.CoRoots.S5_808.dualRootEmbedding.pullback_identity
    identity.reversed (identity.reversed.satisfiedByPi coreTable.semigroup.opposite (Fin 2) oppositeValid)
  have same := SemigroupBasis.CoRoots.S5_848.valid_sameSignature identity.reversed rootValid
  refine ⟨?_⟩
  intro letter
  simpa [Identity.reversed] using same.capped letter

theorem coreLeftUnit : ∀ value : Fin 5, coreTable.mul (4 : Fin 5) value = value := by decide

end SemigroupBasis.CoRoots.Order6Day12.FordLast4
