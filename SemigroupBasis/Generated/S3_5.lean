import SemigroupBasis.Examples.SaturatedSupportThree

namespace SemigroupBasis.Generated.S3_5

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S3_5`, with exact table
`[[1,1,1],[1,1,1],[1,1,3]]`. -/
def table : FiniteTable where
  order := 3
  mul := saturatedSupportThreeFiveMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = saturatedSupportThreeFive := rfl

theorem representative_basis :
    BasisFor table.semigroup saturatedSupportBasis := by
  simpa [table, saturatedSupportThreeFive] using
    saturatedSupportThreeFiveBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite saturatedSupportBasis := by
  simpa [table, saturatedSupportThreeFive] using
    saturatedSupportThreeFiveOppositeBasis_complete

end SemigroupBasis.Generated.S3_5
