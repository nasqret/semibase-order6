import SemigroupBasis.Examples.FinalMarkerThree

namespace SemigroupBasis.Generated.S3_6

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S3_6`, with exact table
`[[1,1,1],[1,1,1],[1,2,3]]`. -/
def table : FiniteTable where
  order := 3
  mul := finalMarkerThreeMul
  assoc := by decide

theorem table_eq_catalogue_model : table = finalMarkerThree := rfl

theorem representative_basis :
    BasisFor table.semigroup finalMarkerThreeBasis := by
  simpa [table, finalMarkerThree] using
    finalMarkerThreeBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite finalMarkerThreeOppositeBasis := by
  simpa [table, finalMarkerThree] using
    finalMarkerThreeOppositeBasis_complete

end SemigroupBasis.Generated.S3_6
