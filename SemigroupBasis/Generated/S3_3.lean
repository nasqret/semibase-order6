import SemigroupBasis.Examples.CommonSquareParityThree
import SemigroupBasis.Generated.CatalogueOrder3

namespace SemigroupBasis.Generated.S3_3

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S3_3`, with exact table
`[[1,2,2],[2,1,1],[2,1,1]]`. -/
def table : FiniteTable where
  order := 3
  mul := commonSquareParitySecondMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = commonSquareParitySecond := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S3_3.table := rfl

theorem representative_basis :
    BasisFor table.semigroup commonSquareParityBasis := by
  simpa [table, commonSquareParitySecond] using
    commonSquareParitySecondBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite commonSquareParityBasis := by
  simpa [table, commonSquareParitySecond] using
    commonSquareParitySecondOppositeBasis_complete

theorem table_selfDual :
    table.semigroup.opposite = table.semigroup := by
  simpa [table, commonSquareParitySecond] using
    commonSquareParitySecond_selfDual

theorem self_dual_basis :
    BasisFor table.semigroup.opposite commonSquareParityBasis :=
  opposite_basis

end SemigroupBasis.Generated.S3_3
