import SemigroupBasis.Examples.FirstOccurrenceFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_59

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_59`, with exact table
`[[1,1,1,1],[1,1,1,1],[1,1,3,4],[4,4,4,4]]`. -/
def table : FiniteTable where
  order := 4
  mul := firstOccurrenceFourMul
  assoc := by decide

theorem table_eq_catalogue_model : table = firstOccurrenceFour := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_59.table := by
  unfold table SemigroupBasis.Generated.Catalogue.S4_59.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup firstOccurrenceFourBasis := by
  simpa [table, firstOccurrenceFour] using
    firstOccurrenceFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      firstOccurrenceFourOppositeBasis := by
  simpa [table, firstOccurrenceFour] using
    firstOccurrenceFourOppositeBasis_complete

end SemigroupBasis.Generated.S4_59
