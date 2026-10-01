import SemigroupBasis.Examples.EdmundsFourTwentyOne
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_21

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_21`, with exact table
`[[1,1,1,1],[1,1,1,1],[1,1,1,3],[1,2,3,4]]`. -/
def table : FiniteTable where
  order := 4
  mul := edmundsFourTwentyOneMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = edmundsFourTwentyOne := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_21.table := by
  unfold table SemigroupBasis.Generated.Catalogue.S4_21.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup edmundsFourTwentyOneBasis := by
  simpa [table, edmundsFourTwentyOne] using
    edmundsFourTwentyOneBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis edmundsFourTwentyOneBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S4_21
