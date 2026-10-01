import SemigroupBasis.Examples.CommutativeThresholdSupportFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_38

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_38`, with exact table
`[[1,1,1,1],[1,1,1,1],[1,1,2,1],[1,1,1,4]]`. -/
def table : FiniteTable where
  order := 4
  mul := thresholdSupportFourMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = thresholdSupportFour := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_38.table := by
  unfold table SemigroupBasis.Generated.Catalogue.S4_38.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup commutativeThresholdSupportBasis := by
  simpa [table, thresholdSupportFour] using
    commutativeThresholdSupportBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis commutativeThresholdSupportBasis) := by
  simpa [table, thresholdSupportFour] using
    commutativeThresholdSupportOppositeBasis_complete

end SemigroupBasis.Generated.S4_38
