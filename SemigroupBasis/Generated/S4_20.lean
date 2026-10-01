import SemigroupBasis.Examples.SimpleEndpointsFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_20

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_20`, with exact table
`[[1,1,1,1],[1,1,1,1],[1,1,1,3],[1,2,1,4]]`. -/
def table : FiniteTable :=
  simpleEndpointsFour

theorem table_eq_catalogue_model :
    table = simpleEndpointsFour := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_20.table := by
  unfold table simpleEndpointsFour
    SemigroupBasis.Generated.Catalogue.S4_20.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup simpleEndpointsBasis := by
  simpa [table] using simpleEndpointsFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis simpleEndpointsBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S4_20
