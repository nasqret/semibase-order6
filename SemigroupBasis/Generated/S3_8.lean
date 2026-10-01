import SemigroupBasis.Examples.CommutativeExponentThree

namespace SemigroupBasis.Generated.S3_8

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S3_8`, with table
`[[1,1,1],[1,1,2],[1,2,3]]` in one-based notation. -/
def table : FiniteTable where
  order := 3
  mul := commutativeExponentThreeMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = commutativeExponentThree := rfl

theorem representative_basis :
    BasisFor table.semigroup commutativeExponentThreeBasis := by
  simpa [table, commutativeExponentThree] using
    commutativeExponentThreeBasis_complete

end SemigroupBasis.Generated.S3_8
