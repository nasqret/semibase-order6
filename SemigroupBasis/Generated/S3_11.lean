import SemigroupBasis.Examples.CommutativeParityThree
import SemigroupBasis.Generated.CatalogueOrder3

namespace SemigroupBasis.Generated.S3_11

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S3_11`, with exact table
`[[1,2,3],[2,1,3],[3,3,3]]`. -/
def table : FiniteTable where
  order := 3
  mul := parityZeroThreeMul
  assoc := by decide

theorem table_eq_catalogue_model : table = parityZeroThree := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S3_11.table := by
  unfold table SemigroupBasis.Generated.Catalogue.S3_11.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup commutativeParityBasis := by
  simpa [table, parityZeroThree] using
    parityZeroThreeBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite commutativeParityBasis := by
  simpa [table, parityZeroThree] using
    parityZeroThreeOppositeBasis_complete

end SemigroupBasis.Generated.S3_11
