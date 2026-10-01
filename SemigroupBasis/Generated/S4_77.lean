import SemigroupBasis.Examples.TwoLetterPrefixFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_77

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_77`. -/
def table : FiniteTable :=
  twoLetterPrefixFour

theorem table_eq_catalogue_model :
    table = twoLetterPrefixFour := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_77.table := by
  unfold table twoLetterPrefixFour twoLetterPrefixFourMul
    SemigroupBasis.Generated.Catalogue.S4_77.table
    SemigroupBasis.Generated.Catalogue.S4_77.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup twoLetterPrefixBasis := by
  simpa [table] using twoLetterPrefixFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis twoLetterPrefixBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S4_77
