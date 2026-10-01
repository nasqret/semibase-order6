import SemigroupBasis.Examples.EdmundsFourSixtyFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_64

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_64`, with exact table
`[[1,1,1,1],[1,1,1,1],[1,2,3,4],[4,4,4,4]]`. -/
def table : FiniteTable where
  order := 4
  mul := edmundsFourSixtyFourMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = edmundsFourSixtyFour := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_64.table := by
  unfold table SemigroupBasis.Generated.Catalogue.S4_64.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup edmundsFourSixtyFourBasis := by
  simpa [table, edmundsFourSixtyFour] using
    edmundsFourSixtyFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis edmundsFourSixtyFourBasis) := by
  simpa [table, edmundsFourSixtyFour] using
    edmundsFourSixtyFourBasis_complete.oppositeReversed

end SemigroupBasis.Generated.S4_64
