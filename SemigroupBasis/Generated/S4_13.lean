import SemigroupBasis.Examples.CyclicThreeTwo
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_13

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_13`, the cyclic semigroup
`C_{3,2}`. -/
def table : FiniteTable :=
  cyclicThreeTwo

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_13.table := by
  unfold table cyclicThreeTwo cyclicThreeTwoMul
    SemigroupBasis.Generated.Catalogue.S4_13.table
    SemigroupBasis.Generated.Catalogue.S4_13.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup cyclicThreeTwoBasis := by
  simpa [table] using cyclicThreeTwoBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis cyclicThreeTwoBasis) := by
  simpa [table] using cyclicThreeTwoOppositeBasis_complete

end SemigroupBasis.Generated.S4_13
