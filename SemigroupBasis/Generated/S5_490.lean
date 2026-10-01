import SemigroupBasis.Examples.CyclicTwoFour
import SemigroupBasis.Generated.CatalogueOrder5Part04

namespace SemigroupBasis.Generated.S5_490

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S5_490`, the cyclic semigroup
`C_{2,4}`. -/
def table : FiniteTable :=
  cyclicTwoFour

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_490.table := by
  unfold table cyclicTwoFour cyclicTwoFourMul
    SemigroupBasis.Generated.Catalogue.S5_490.table
    SemigroupBasis.Generated.Catalogue.S5_490.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup cyclicTwoFourBasis := by
  simpa [table] using cyclicTwoFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis cyclicTwoFourBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S5_490
