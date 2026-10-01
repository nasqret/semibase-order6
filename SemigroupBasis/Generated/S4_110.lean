import SemigroupBasis.Examples.NormalBandFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_110

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_110`, with exact table
`[[1,1,1,1],[1,2,1,4],[3,3,3,3],[1,2,1,4]]`. -/
def table : FiniteTable :=
  normalBandFour

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_110.table := by
  unfold table normalBandFour normalBandFourMul
    SemigroupBasis.Generated.Catalogue.S4_110.table
    SemigroupBasis.Generated.Catalogue.S4_110.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup normalBandBasis := by
  simpa [table] using normalBandFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis normalBandBasis) := by
  simpa [table, normalBandFourOppositeBasis] using
    normalBandFourOppositeBasis_complete

end SemigroupBasis.Generated.S4_110
