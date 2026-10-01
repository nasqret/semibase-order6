import SemigroupBasis.CoRoots.Order6LeeZhangCondition14Derivations
import SemigroupBasis.CoRoots.S5_791Invariant

/-!
# Exact invariant for Lee--Zhang Condition 14

The `S5_791` factor records the ordered connected-component signature and
the complete first-occurrence sequence.  The cyclic factor records every
occurrence count modulo two.  Their conjunction is the exact signature used
by the Condition 14 canonical form.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14

open SemigroupBasis
open SemigroupBasis.Examples

/-- Pointwise equality of all occurrence counts modulo two. -/
def SameOccurrenceParity (left right : Word Nat) : Prop :=
  ∀ letter,
    left.toList.count letter % 2 =
      right.toList.count letter % 2

/-- The exact product-factor invariant for Condition 14. -/
structure SameComponentInitialParitySignature
    (left right : Word Nat) : Prop where
  componentInitial :
    S5_791Invariant.SameComponentInitialSignature left right
  parity : SameOccurrenceParity left right

namespace SameComponentInitialParitySignature

theorem refl (word : Word Nat) :
    SameComponentInitialParitySignature word word :=
  ⟨S5_791Invariant.SameComponentInitialSignature.refl word,
    fun _ => rfl⟩

theorem symm {left right : Word Nat}
    (same : SameComponentInitialParitySignature left right) :
    SameComponentInitialParitySignature right left :=
  ⟨same.componentInitial.symm,
    fun letter => (same.parity letter).symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameComponentInitialParitySignature left middle)
    (second : SameComponentInitialParitySignature middle right) :
    SameComponentInitialParitySignature left right :=
  ⟨first.componentInitial.trans second.componentInitial,
    fun letter =>
      (first.parity letter).trans (second.parity letter)⟩

end SameComponentInitialParitySignature

/-- Validity in the two exact factors determines the complete Condition 14
signature. -/
theorem valid_sameComponentInitialParitySignature
    (identity : Identity Nat)
    (cyclicValid : identity.SatisfiedBy cyclic)
    (coreValid : identity.SatisfiedBy core) :
    SameComponentInitialParitySignature
      identity.lhs identity.rhs := by
  have catalogueCoreValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_791.table.semigroup := by
    simpa [core, coreTable] using coreValid
  have cyclicTwoValid :
      identity.SatisfiedBy cyclicTwo.semigroup := by
    simpa [cyclic, cyclicTable,
      SemigroupBasis.Generated.S2_2.table_eq_catalogue_model] using
        cyclicValid
  exact
    ⟨S5_791FamilyInvariant.S5_791.valid_sameSignature
        identity catalogueCoreValid,
      cyclicValid_parity_eq identity cyclicTwoValid⟩

/-- Every derivation from the six laws preserves the complete product-factor
signature.  This is the invariant side of the eventual normal-form proof. -/
theorem derives_sameComponentInitialParitySignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameComponentInitialParitySignature left right := by
  apply valid_sameComponentInitialParitySignature
    (⟨left, right⟩ : Identity Nat)
  · exact fun valuation => derivation.sound cyclicModels valuation
  · exact fun valuation => derivation.sound coreModels valuation

end SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14
