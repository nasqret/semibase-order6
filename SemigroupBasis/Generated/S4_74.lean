import SemigroupBasis.Examples.FirstCappedMultiplicityFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_74

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_74`, with exact table
`[[1,1,1,1],[1,1,1,2],[3,3,3,3],[1,2,1,4]]`. -/
def table : FiniteTable where
  order := 4
  mul := firstCappedMultiplicityFourMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = firstCappedMultiplicityFour := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_74.table := by
  unfold table SemigroupBasis.Generated.Catalogue.S4_74.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup firstCappedMultiplicityFourBasis := by
  simpa [table, firstCappedMultiplicityFour] using
    firstCappedMultiplicityFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis firstCappedMultiplicityFourBasis) := by
  simpa [table, firstCappedMultiplicityFour,
    firstCappedMultiplicityFourOppositeBasis] using
      firstCappedMultiplicityFourOppositeBasis_complete

end SemigroupBasis.Generated.S4_74
