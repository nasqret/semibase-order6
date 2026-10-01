import SemigroupBasis.CoRoots.S5_348Factors
import SemigroupBasis.Examples.SimpleSequenceFirstGap

namespace SemigroupBasis.CoRoots

open SemigroupBasis
open SemigroupBasis.Examples

namespace S5_348Invariant

abbrev SameSimpleSequenceFirstGapFinalSignature
    (left right : Word Nat) : Prop :=
  SimpleSequenceFirstGap.SameSignature left right

abbrev sameSignature (left right : Word Nat) : Prop :=
  SameSimpleSequenceFirstGapFinalSignature left right

end S5_348Invariant

namespace S5_348

private def oppositeS4_71 : FiniteTable where
  order := 4
  mul := fun a b => Generated.S4_71.table.mul b a
  assoc := by decide

private theorem blockModels :
    Models Generated.S4_71.table.semigroup.opposite basis := by
  have checked :=
    models_of_finite_checks oppositeS4_71 (by decide)
  simpa [oppositeS4_71, FiniteTable.semigroup,
    Semigroup.opposite] using checked

private theorem finalMarkerModels :
    Models finalMarkerThree.semigroup basis :=
  models_of_finite_checks finalMarkerThree (by decide)

/-- Every derivation from the exact seven-law basis preserves capped
multiplicity, the ordered simple-variable sequence, every first-occurrence
gap, and the optional globally simple final marker. -/
theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    S5_348Invariant.SameSimpleSequenceFirstGapFinalSignature
      left right :=
  SimpleSequenceFirstGap.sameSignature_of_factor_valid
    ⟨left, right⟩
    (fun valuation => derivation.sound blockModels valuation)
    (fun valuation => derivation.sound finalMarkerModels valuation)

end S5_348

namespace S5_348FamilyInvariant

namespace S5_348

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_348.table.semigroup) :
    S5_348Invariant.SameSimpleSequenceFirstGapFinalSignature
      identity.lhs identity.rhs :=
  SimpleSequenceFirstGap.sameSignature_of_factor_valid identity
    (S5_348Factors.S5_348.valid_block identity valid)
    (S5_348Factors.S5_348.valid_finalMarker identity valid)

end S5_348

namespace S5_354

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_354.table.semigroup) :
    S5_348Invariant.SameSimpleSequenceFirstGapFinalSignature
      identity.lhs identity.rhs :=
  SimpleSequenceFirstGap.sameSignature_of_factor_valid identity
    (S5_348Factors.S5_354.valid_block identity valid)
    (S5_348Factors.S5_354.valid_finalMarker identity valid)

end S5_354

end S5_348FamilyInvariant

end SemigroupBasis.CoRoots
