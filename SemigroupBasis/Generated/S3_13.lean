import SemigroupBasis.Examples.LeftNormalBandThree

namespace SemigroupBasis.Generated.S3_13

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S3_13`, with table
`[[1,1,1],[1,2,1],[3,3,3]]`. -/
def table : FiniteTable where
  order := 3
  mul := leftNormalBandThreeMul
  assoc := by decide

theorem table_eq_catalogue_model : table = leftNormalBandThree := rfl

theorem representative_basis :
    BasisFor table.semigroup leftNormalBandThreeBasis := by
  simpa [table, leftNormalBandThree] using
    leftNormalBandThreeBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) := by
  simpa [table, leftNormalBandThree, leftNormalBandThreeOppositeBasis] using
    leftNormalBandThreeOppositeBasis_complete

end SemigroupBasis.Generated.S3_13
