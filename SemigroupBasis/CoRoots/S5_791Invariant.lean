import SemigroupBasis.CoRoots.S5_788Invariant
import SemigroupBasis.CoRoots.S5_790Invariant
import SemigroupBasis.CoRoots.S5_791Factors

namespace SemigroupBasis.CoRoots

open SemigroupBasis
open SemigroupBasis.Examples

namespace S5_791Invariant

/-- The exact semantic invariant of the family: the ordered `S4_70`
connected-component signatures and the complete sequence of first
occurrences. -/
structure SameComponentInitialSignature
    (left right : Word Nat) : Prop where
  components :
    connectedComponentSignaturesWord left =
      connectedComponentSignaturesWord right
  initials :
    firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList

abbrev sameSignature (left right : Word Nat) : Prop :=
  SameComponentInitialSignature left right

namespace SameComponentInitialSignature

theorem refl (word : Word Nat) :
    SameComponentInitialSignature word word :=
  ⟨rfl, rfl⟩

theorem symm {left right : Word Nat}
    (same : SameComponentInitialSignature left right) :
    SameComponentInitialSignature right left :=
  ⟨same.components.symm, same.initials.symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameComponentInitialSignature left middle)
    (second : SameComponentInitialSignature middle right) :
    SameComponentInitialSignature left right :=
  ⟨first.components.trans second.components,
    first.initials.trans second.initials⟩

end SameComponentInitialSignature

theorem sameSignature_of_s4_70_s3_16_valid
    (identity : Identity Nat)
    (componentValid :
      identity.SatisfiedBy Generated.S4_70.table.semigroup)
    (initialValid :
      identity.SatisfiedBy Generated.S3_16.table.semigroup) :
    SameComponentInitialSignature identity.lhs identity.rhs := by
  have canonicalInitialValid :
      identity.SatisfiedBy leftRegularBandThree.semigroup := by
    simpa only [Generated.S3_16.table_eq_catalogue_model] using
      initialValid
  exact
    ⟨S5_790Invariant.sameComponents_of_s4_70_valid
        identity componentValid,
      S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
        identity canonicalInitialValid⟩

end S5_791Invariant

namespace S5_791

/-- Every derivation from the five-law basis preserves the combined
component/initial signature. -/
theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    S5_791Invariant.SameComponentInitialSignature left right := by
  have componentModels :
      Models Generated.S4_70.table.semigroup basis :=
    models_of_finite_checks Generated.S4_70.table (by decide)
  have initialModels :
      Models leftRegularBandThree.semigroup basis :=
    models_of_finite_checks leftRegularBandThree (by decide)
  let identity : Identity Nat := ⟨left, right⟩
  exact
    ⟨S5_790Invariant.sameComponents_of_s4_70_valid identity
        (fun valuation => derivation.sound componentModels valuation),
      S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
        identity
        (fun valuation => derivation.sound initialModels valuation)⟩

end S5_791

namespace S5_791FamilyInvariant

namespace S5_791

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_791.table.semigroup) :
    S5_791Invariant.SameComponentInitialSignature
      identity.lhs identity.rhs :=
  S5_791Invariant.sameSignature_of_s4_70_s3_16_valid identity
    (S5_791Factors.S5_791.valid_s4_70 identity valid)
    (S5_791Factors.S5_791.valid_s3_16 identity valid)

end S5_791

namespace S5_807

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_807.table.semigroup) :
    S5_791Invariant.SameComponentInitialSignature
      identity.lhs identity.rhs :=
  S5_791Invariant.sameSignature_of_s4_70_s3_16_valid identity
    (S5_791Factors.S5_807.valid_s4_70 identity valid)
    (S5_791Factors.S5_807.valid_s3_16 identity valid)

end S5_807

end S5_791FamilyInvariant

end SemigroupBasis.CoRoots
