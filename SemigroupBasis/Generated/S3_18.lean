import SemigroupBasis.Examples.CyclicThree
import SemigroupBasis.Generated.CatalogueOrder3

namespace SemigroupBasis.Generated.S3_18

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S3_18`, the cyclic group `C3`. -/
def table : FiniteTable where
  order := 3
  mul := cyclicThreeMul
  assoc := by decide

theorem table_eq_catalogue_model : table = cyclicThree := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S3_18.table := by
  unfold table SemigroupBasis.Generated.Catalogue.S3_18.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup cyclicThreeBasis := by
  simpa [table, cyclicThree] using cyclicThreeBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite cyclicThreeBasis := by
  simpa [table, cyclicThree] using cyclicThreeOppositeBasis_complete

end SemigroupBasis.Generated.S3_18
