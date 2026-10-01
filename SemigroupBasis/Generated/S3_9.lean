import SemigroupBasis.Examples.SaturatedSupportThree

namespace SemigroupBasis.Generated.S3_9

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S3_9`, with exact table
`[[1,1,3],[1,1,3],[3,3,3]]`. -/
def table : FiniteTable where
  order := 3
  mul := saturatedSupportThreeNineMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = saturatedSupportThreeNine := rfl

theorem representative_basis :
    BasisFor table.semigroup saturatedSupportBasis := by
  simpa [table, saturatedSupportThreeNine] using
    saturatedSupportThreeNineBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite saturatedSupportBasis := by
  simpa [table, saturatedSupportThreeNine] using
    saturatedSupportThreeNineOppositeBasis_complete

end SemigroupBasis.Generated.S3_9
