import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.CoRoots.S5_441Invariant
import SemigroupBasis.CoRoots.S5_788Factors

namespace SemigroupBasis.CoRoots

open SemigroupBasis
open SemigroupBasis.Examples

namespace S5_788Invariant

/-- The semantic invariant of the `S5_788` family: support, all exact
unique-separator cuts with their side supports, and the complete sequence
of first occurrences. -/
structure SameSeparatorInitialSignature
    (left right : Word Nat) : Prop where
  support : S5_441Invariant.SameSupport left right
  exactCuts : S5_441Invariant.SameExactCutSignature left right
  initials :
    firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList

abbrev sameSignature (left right : Word Nat) : Prop :=
  SameSeparatorInitialSignature left right

namespace SameSeparatorInitialSignature

theorem refl (word : Word Nat) :
    SameSeparatorInitialSignature word word :=
  ⟨S5_441Invariant.SameSupport.refl word,
    S5_441Invariant.SameExactCutSignature.refl word, rfl⟩

theorem symm {left right : Word Nat}
    (same : SameSeparatorInitialSignature left right) :
    SameSeparatorInitialSignature right left :=
  ⟨S5_441Invariant.SameSupport.symm same.support,
    S5_441Invariant.SameExactCutSignature.symm same.exactCuts,
    same.initials.symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameSeparatorInitialSignature left middle)
    (second : SameSeparatorInitialSignature middle right) :
    SameSeparatorInitialSignature left right :=
  ⟨S5_441Invariant.SameSupport.trans first.support second.support,
    S5_441Invariant.SameExactCutSignature.trans
      first.exactCuts second.exactCuts,
    first.initials.trans second.initials⟩

end SameSeparatorInitialSignature

theorem sameSignature_of_s4_69_s3_16_valid
    (identity : Identity Nat)
    (separatorValid :
      identity.SatisfiedBy
        Generated.Catalogue.S4_69.table.semigroup)
    (initialValid :
      identity.SatisfiedBy Generated.S3_16.table.semigroup) :
    SameSeparatorInitialSignature identity.lhs identity.rhs := by
  have canonicalInitialValid :
      identity.SatisfiedBy leftRegularBandThree.semigroup := by
    simpa only [Generated.S3_16.table_eq_catalogue_model] using
      initialValid
  exact
    ⟨S5_441Invariant.sameSupport_of_s4_69_valid
        identity separatorValid,
      S5_441Invariant.sameExactCutSignature_of_s4_69_valid
        identity separatorValid,
      S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
        identity canonicalInitialValid⟩

end S5_788Invariant

namespace S5_788

/-- Every derivation from the 24-law basis preserves the intended
separator/initial signature. -/
theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    S5_788Invariant.SameSeparatorInitialSignature left right := by
  have separatorModels :
      Models uniqueSeparatorFour.semigroup basis :=
    models_of_finite_checks uniqueSeparatorFour (by decide)
  have initialModels :
      Models leftRegularBandThree.semigroup basis :=
    models_of_finite_checks leftRegularBandThree (by decide)
  exact
    ⟨S5_441Invariant.sameSupport_of_uniqueSeparatorFour_equalEval
        left right
        (fun valuation => derivation.sound separatorModels valuation),
      S5_441Invariant.sameExactCutSignature_of_uniqueSeparatorFour_equalEval
        left right
        (fun valuation => derivation.sound separatorModels valuation),
      S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
        (⟨left, right⟩ : Identity Nat)
        (fun valuation => derivation.sound initialModels valuation)⟩

end S5_788

namespace S5_788FamilyInvariant

namespace S5_788

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_788.table.semigroup) :
    S5_788Invariant.SameSeparatorInitialSignature
      identity.lhs identity.rhs :=
  S5_788Invariant.sameSignature_of_s4_69_s3_16_valid identity
    (S5_788Factors.S5_788.valid_s4_69 identity valid)
    (S5_788Factors.S5_788.valid_s3_16 identity valid)

end S5_788

namespace S5_805

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_805.table.semigroup) :
    S5_788Invariant.SameSeparatorInitialSignature
      identity.lhs identity.rhs :=
  S5_788Invariant.sameSignature_of_s4_69_s3_16_valid identity
    (S5_788Factors.S5_805.valid_s4_69 identity valid)
    (S5_788Factors.S5_805.valid_s3_16 identity valid)

end S5_805

namespace S5_811

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_811.table.semigroup) :
    S5_788Invariant.SameSeparatorInitialSignature
      identity.lhs identity.rhs :=
  S5_788Invariant.sameSignature_of_s4_69_s3_16_valid identity
    (S5_788Factors.S5_811.valid_s4_69 identity valid)
    (S5_788Factors.S5_811.valid_s3_16 identity valid)

end S5_811

end S5_788FamilyInvariant

end SemigroupBasis.CoRoots
