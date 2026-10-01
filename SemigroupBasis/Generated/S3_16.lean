import SemigroupBasis.Examples.LeftRegularBandThree

namespace SemigroupBasis.Generated.S3_16

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S3_16`, with exact table
`[[1,1,1],[1,2,3],[3,3,3]]`. -/
def table : FiniteTable where
  order := 3
  mul := leftRegularBandThreeMul
  assoc := by decide

theorem table_eq_catalogue_model : table = leftRegularBandThree := rfl

theorem representative_basis :
    BasisFor table.semigroup leftRegularBandThreeBasis := by
  simpa [table, leftRegularBandThree] using
    leftRegularBandThreeBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      leftRegularBandThreeOppositeBasis := by
  simpa [table, leftRegularBandThree] using
    leftRegularBandThreeOppositeBasis_complete

end SemigroupBasis.Generated.S3_16
