import SemigroupBasis.Examples.LeftNormalBandFifteen
import SemigroupBasis.Generated.CatalogueOrder3

namespace SemigroupBasis.Generated.S3_15

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S3_15`, with exact table
`[[1,1,1],[1,2,2],[1,3,3]]`. -/
def table : FiniteTable where
  order := 3
  mul := leftNormalBandFifteenMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = leftNormalBandFifteen := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S3_15.table := by
  unfold table SemigroupBasis.Generated.Catalogue.S3_15.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup leftNormalBandThreeBasis := by
  simpa [table, leftNormalBandFifteen] using
    leftNormalBandFifteenBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) := by
  simpa [table, leftNormalBandFifteen] using
    leftNormalBandFifteenOppositeBasis_complete

end SemigroupBasis.Generated.S3_15
