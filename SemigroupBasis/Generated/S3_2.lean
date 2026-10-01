import SemigroupBasis.Examples.CommonSquareParityThree
import SemigroupBasis.Generated.CatalogueOrder3

namespace SemigroupBasis.Generated.S3_2

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S3_2`, with exact table
`[[1,1,3],[1,1,3],[3,3,1]]`. -/
def table : FiniteTable where
  order := 3
  mul := commonSquareParityFirstMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = commonSquareParityFirst := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S3_2.table := rfl

theorem representative_basis :
    BasisFor table.semigroup commonSquareParityBasis := by
  simpa [table, commonSquareParityFirst] using
    commonSquareParityFirstBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite commonSquareParityBasis := by
  simpa [table, commonSquareParityFirst] using
    commonSquareParityFirstOppositeBasis_complete

theorem table_selfDual :
    table.semigroup.opposite = table.semigroup := by
  simpa [table, commonSquareParityFirst] using
    commonSquareParityFirst_selfDual

theorem self_dual_basis :
    BasisFor table.semigroup.opposite commonSquareParityBasis :=
  opposite_basis

end SemigroupBasis.Generated.S3_2
