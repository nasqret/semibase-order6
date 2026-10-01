import SemigroupBasis.Examples.ConnectedComponentFourFinal
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_70

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_70`. -/
def table : FiniteTable :=
  connectedComponentFour

theorem table_eq_catalogue_model :
    table = connectedComponentFour := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_70.table := by
  unfold table connectedComponentFour connectedComponentFourMul
    SemigroupBasis.Generated.Catalogue.S4_70.table
    SemigroupBasis.Generated.Catalogue.S4_70.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup connectedComponentFourBasis := by
  simpa [table] using connectedComponentFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis connectedComponentFourBasis) := by
  simpa [table, connectedComponentFourOppositeBasis] using
    connectedComponentFourOppositeBasis_complete

end SemigroupBasis.Generated.S4_70
