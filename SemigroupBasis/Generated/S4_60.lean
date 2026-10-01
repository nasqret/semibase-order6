import SemigroupBasis.Examples.EdmundsFourSixty
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_60

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_60`, with exact table
`[[1,1,1,1],[1,1,1,1],[1,2,3,1],[4,4,4,4]]`. -/
def table : FiniteTable :=
  edmundsFourSixty

theorem table_eq_catalogue_model :
    table = edmundsFourSixty := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_60.table := by
  unfold table edmundsFourSixty
    SemigroupBasis.Generated.Catalogue.S4_60.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup edmundsFourSixtyBasis := by
  simpa [table] using edmundsFourSixtyBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis edmundsFourSixtyBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S4_60
