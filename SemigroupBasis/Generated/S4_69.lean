import SemigroupBasis.Examples.UniqueSeparatorFourFinal
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_69

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_69`. -/
def table : FiniteTable :=
  uniqueSeparatorFour

theorem table_eq_catalogue_model :
    table = uniqueSeparatorFour := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_69.table := by
  unfold table uniqueSeparatorFour uniqueSeparatorFourMul
    SemigroupBasis.Generated.Catalogue.S4_69.table
    SemigroupBasis.Generated.Catalogue.S4_69.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup uniqueSeparatorFourBasis := by
  simpa [table] using uniqueSeparatorFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis uniqueSeparatorFourBasis) := by
  simpa [table, uniqueSeparatorFourOppositeBasis] using
    uniqueSeparatorFourOppositeBasis_complete

end SemigroupBasis.Generated.S4_69
