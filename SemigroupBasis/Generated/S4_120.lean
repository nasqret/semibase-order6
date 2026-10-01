import SemigroupBasis.Examples.FirstFinalBandFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_120

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_120`, with exact table
`[[1,1,1,1],[1,2,3,4],[1,2,3,4],[4,4,4,4]]`. -/
def table : FiniteTable :=
  firstFinalBandFour

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_120.table := by
  unfold table firstFinalBandFour firstFinalBandFourMul
    SemigroupBasis.Generated.Catalogue.S4_120.table
    SemigroupBasis.Generated.Catalogue.S4_120.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup firstFinalBandBasis := by
  simpa [table] using firstFinalBandBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis firstFinalBandBasis) := by
  simpa [table, firstFinalBandOppositeBasis] using
    firstFinalBandOppositeBasis_complete

end SemigroupBasis.Generated.S4_120
