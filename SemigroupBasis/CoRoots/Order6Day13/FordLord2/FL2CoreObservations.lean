import SemigroupBasis.CoRoots.S5_378Family

/-! Observations of the already-complete S5_378 core in the opposite
orientation. Right multiplication by 2 and 4 separates the direct core;
this becomes joint LEFT separation here. No unit is assumed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day13.FordLord2

open SemigroupBasis

abbrev coreTable : FiniteTable := Generated.Catalogue.S5_378.table
abbrev reversedCore : Semigroup (Fin 5) := coreTable.semigroup.opposite
abbrev SimpleIn := SemigroupBasis.CoRoots.S5_378.GloballySimple

structure LowerSignature (left right : Word Nat) : Prop where
  supportEq : ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList
  simpleEq : ∀ letter, SimpleIn left letter ↔ SimpleIn right letter

namespace LowerSignature

theorem symm {left right : Word Nat} (same : LowerSignature left right) :
    LowerSignature right left :=
  ⟨fun letter => (same.supportEq letter).symm, fun letter => (same.simpleEq letter).symm⟩

theorem support {left right : Word Nat} (same : LowerSignature left right) (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList := same.supportEq letter

theorem simple {left right : Word Nat} (same : LowerSignature left right) (letter : Nat) :
    SimpleIn left letter ↔ SimpleIn right letter := same.simpleEq letter

end LowerSignature

theorem validLowerSignature (identity : Identity Nat)
    (valid : identity.SatisfiedBy reversedCore) :
    LowerSignature identity.lhs identity.rhs := by
  have directValid : identity.reversed.SatisfiedBy coreTable.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed identity coreTable.semigroup).mp valid
  have same := SemigroupBasis.CoRoots.S5_378.valid_sameSignature identity.reversed directValid
  constructor
  · intro letter
    simpa [Identity.reversed] using same.support letter
  · intro letter
    simpa [Identity.reversed, SimpleIn, SemigroupBasis.CoRoots.S5_378.GloballySimple] using
      same.globallySimple letter

/-- The concrete pair of left translations replaces an unavailable unit. -/
theorem coreLeftSeparates : Function.Injective (fun value : Fin 5 =>
    (reversedCore.mul (2 : Fin 5) value, reversedCore.mul (4 : Fin 5) value)) := by
  intro a b
  exact by decide +revert

end SemigroupBasis.CoRoots.Order6Day13.FordLord2
