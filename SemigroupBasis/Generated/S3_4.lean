import SemigroupBasis.Examples.ProjectionQuadraticThree

namespace SemigroupBasis.Generated.S3_4

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S3_4`, with exact table
`[[1,1,1],[1,1,1],[1,1,2]]`. -/
def table : FiniteTable where
  order := 3
  mul := projectionQuadraticThreeMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = projectionQuadraticThree := rfl

theorem representative_basis :
    BasisFor table.semigroup projectionQuadraticThreeBasis := by
  simpa [table, projectionQuadraticThree] using
    projectionQuadraticThreeBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite projectionQuadraticThreeBasis := by
  simpa [table, projectionQuadraticThree] using
    projectionQuadraticThreeOppositeBasis_complete

end SemigroupBasis.Generated.S3_4
