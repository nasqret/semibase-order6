import SemigroupBasis.Examples.FirstContentFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_55

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_55`, with exact table
`[[1,1,1,1],[1,1,1,1],[1,1,3,1],[4,4,4,4]]`. -/
def table : FiniteTable where
  order := 4
  mul := firstContentFourMul
  assoc := by decide

theorem table_eq_catalogue_model : table = firstContentFour := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_55.table := by
  unfold table SemigroupBasis.Generated.Catalogue.S4_55.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup firstContentFourBasis := by
  simpa [table, firstContentFour] using
    firstContentFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis firstContentFourBasis) := by
  simpa [table, firstContentFour, firstContentFourOppositeBasis] using
    firstContentFourOppositeBasis_complete

end SemigroupBasis.Generated.S4_55
