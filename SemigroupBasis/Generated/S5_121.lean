import SemigroupBasis.Examples.DualMultipleBlockFive
import SemigroupBasis.Generated.CatalogueOrder5Part01

namespace SemigroupBasis.Generated.S5_121

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S5_121`, with exact table
`[[1,1,1,4,1],[1,1,1,4,1],[1,1,1,4,3],[4,4,4,1,4],[1,2,3,4,5]]`. -/
def table : FiniteTable :=
  dualMultipleBlockFiveStored

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_121.table := by
  unfold table dualMultipleBlockFiveStored
    dualMultipleBlockFiveStoredMul dualMultipleBlockFiveMul
    SemigroupBasis.Generated.Catalogue.S5_121.table
    SemigroupBasis.Generated.Catalogue.S5_121.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup dualMultipleBlockFiveStoredBasis := by
  simpa [table] using dualMultipleBlockFiveStoredBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis dualMultipleBlockFiveStoredBasis) := by
  simpa [table] using
    dualMultipleBlockFiveStoredBasis_complete.oppositeReversed

end SemigroupBasis.Generated.S5_121
