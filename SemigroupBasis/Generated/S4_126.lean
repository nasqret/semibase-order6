import SemigroupBasis.Examples.CyclicTwoThree
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_126

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_126`, the cyclic semigroup
`C_{2,3}`. -/
def table : FiniteTable :=
  cyclicTwoThree

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_126.table := by
  unfold table cyclicTwoThree cyclicTwoThreeMul
    SemigroupBasis.Generated.Catalogue.S4_126.table
    SemigroupBasis.Generated.Catalogue.S4_126.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup cyclicTwoThreeBasis := by
  simpa [table] using cyclicTwoThreeBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis cyclicTwoThreeBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S4_126
