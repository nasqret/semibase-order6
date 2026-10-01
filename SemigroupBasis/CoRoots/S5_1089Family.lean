import SemigroupBasis.CoRoots.S5_1089Semantics

namespace SemigroupBasis.CoRoots.S5_1089Family

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_1089

namespace S5_1089

open SemigroupBasis.CoRoots.S5_1089Semantics.S5_1089

theorem basis_complete :
    BasisFor table.semigroup basis :=
  basis_complete_of_head_last_separation
    table.semigroup models fun identity valid =>
      ⟨valid_head_eq identity valid,
        valid_lastOccurrenceSequence_eq identity valid⟩

theorem representative_basis :
    BasisFor table.semigroup basis :=
  basis_complete

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using basis_complete.oppositeReversed

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis_complete

theorem derives_iff_sameR2S2Signature
    {left right : Word Nat} :
    Derives basis left right ↔ SameR2S2Signature left right := by
  constructor
  · intro derivation
    have valid :
        (Identity.mk left right).SatisfiedBy table.semigroup :=
      fun valuation => derivation.sound models valuation
    exact
      ⟨valid_head_eq (Identity.mk left right) valid,
        valid_lastOccurrenceSequence_eq
          (Identity.mk left right) valid⟩
  · exact derives_of_sameR2S2Signature

end S5_1089

namespace S5_1143

open SemigroupBasis.CoRoots.S5_1089Semantics.S5_1143

theorem basis_complete :
    BasisFor table.semigroup basis :=
  basis_complete_of_head_last_separation
    table.semigroup models fun identity valid =>
      ⟨valid_head_eq identity valid,
        valid_lastOccurrenceSequence_eq identity valid⟩

theorem representative_basis :
    BasisFor table.semigroup basis :=
  basis_complete

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using basis_complete.oppositeReversed

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis_complete

theorem derives_iff_sameR2S2Signature
    {left right : Word Nat} :
    Derives basis left right ↔ SameR2S2Signature left right := by
  constructor
  · intro derivation
    have valid :
        (Identity.mk left right).SatisfiedBy table.semigroup :=
      fun valuation => derivation.sound models valuation
    exact
      ⟨valid_head_eq (Identity.mk left right) valid,
        valid_lastOccurrenceSequence_eq
          (Identity.mk left right) valid⟩
  · exact derives_of_sameR2S2Signature

end S5_1143

end SemigroupBasis.CoRoots.S5_1089Family
