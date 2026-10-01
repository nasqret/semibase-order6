import SemigroupBasis.Examples.DualCappedMultipleBlockFive
import SemigroupBasis.Generated.CatalogueOrder5Part02

namespace SemigroupBasis.Generated.S5_209

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S5_209`, with exact table
`[[1,1,1,1,1],[1,1,1,1,2],[1,1,1,1,1],[1,1,1,2,4],[1,2,3,4,5]]`. -/
def table : FiniteTable :=
  dualCappedMultipleBlockFiveStored

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_209.table := by
  unfold table dualCappedMultipleBlockFiveStored
    dualCappedMultipleBlockFiveStoredMul dualCappedMultipleBlockFiveMul
    SemigroupBasis.Generated.Catalogue.S5_209.table
    SemigroupBasis.Generated.Catalogue.S5_209.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup dualCappedMultipleBlockFiveStoredBasis := by
  simpa [table] using dualCappedMultipleBlockFiveStoredBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis dualCappedMultipleBlockFiveStoredBasis) := by
  simpa [table] using
    dualCappedMultipleBlockFiveStoredBasis_complete.oppositeReversed

end SemigroupBasis.Generated.S5_209
