import SemigroupBasis.Examples.CommutativeParityThree
import SemigroupBasis.Generated.CatalogueOrder3

namespace SemigroupBasis.Generated.S3_10

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S3_10`, with exact table
`[[1,2,1],[2,1,2],[1,2,3]]`. -/
def table : FiniteTable where
  order := 3
  mul := parityIdentityThreeMul
  assoc := by decide

theorem table_eq_catalogue_model : table = parityIdentityThree := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S3_10.table := rfl

theorem representative_basis :
    BasisFor table.semigroup commutativeParityBasis := by
  simpa [table, parityIdentityThree] using
    parityIdentityThreeBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite commutativeParityBasis := by
  simpa [table, parityIdentityThree] using
    parityIdentityThreeOppositeBasis_complete

end SemigroupBasis.Generated.S3_10
