import SemigroupBasis.Examples.CyclicFourOne
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_11

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_11`, the cyclic semigroup
`C_{4,1}`. -/
def table : FiniteTable :=
  cyclicFourOne

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_11.table := by
  unfold table cyclicFourOne cyclicFourOneMul
    SemigroupBasis.Generated.Catalogue.S4_11.table
    SemigroupBasis.Generated.Catalogue.S4_11.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup cyclicFourOneBasis := by
  simpa [table] using cyclicFourOneBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis cyclicFourOneBasis) := by
  simpa [table] using cyclicFourOneOppositeBasis_complete

end SemigroupBasis.Generated.S4_11
