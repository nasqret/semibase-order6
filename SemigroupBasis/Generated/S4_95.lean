import SemigroupBasis.Examples.ParityInitialFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_95

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_95`, with exact table
`[[1,2,3,4],[2,1,3,4],[3,3,3,3],[4,4,4,4]]`. -/
def table : FiniteTable :=
  parityInitialFour

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_95.table := by
  unfold table parityInitialFour parityInitialFourMul
    SemigroupBasis.Generated.Catalogue.S4_95.table
    SemigroupBasis.Generated.Catalogue.S4_95.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup parityInitialBasis := by
  simpa [table] using parityInitialBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis parityInitialBasis) := by
  simpa [table, parityInitialOppositeBasis] using
    parityInitialOppositeBasis_complete

end SemigroupBasis.Generated.S4_95
