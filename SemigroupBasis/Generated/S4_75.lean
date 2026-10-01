import SemigroupBasis.Examples.EdmundsFiveTwoFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_75

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_75`, with exact table
`[[1,1,1,1],[1,1,1,2],[3,3,3,3],[1,2,3,4]]`. -/
def table : FiniteTable where
  order := 4
  mul := edmundsFiveTwoFourMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = edmundsFiveTwoFour := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_75.table := by
  unfold table SemigroupBasis.Generated.Catalogue.S4_75.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup edmundsFiveTwoFourBasis := by
  simpa [table, edmundsFiveTwoFour] using
    edmundsFiveTwoFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis edmundsFiveTwoFourBasis) := by
  simpa [table, edmundsFiveTwoFour] using
    edmundsFiveTwoFourBasis_complete.oppositeReversed

end SemigroupBasis.Generated.S4_75
