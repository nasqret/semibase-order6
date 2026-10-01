import SemigroupBasis.Examples.EdmundsFourSeventyOne
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_71

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_71`, with exact table
`[[1,1,1,1],[1,1,1,2],[1,2,3,3],[1,2,3,4]]`. -/
def table : FiniteTable where
  order := 4
  mul := edmundsFourSeventyOneMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = edmundsFourSeventyOne := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_71.table := by
  unfold table SemigroupBasis.Generated.Catalogue.S4_71.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup edmundsFourSeventyOneBasis := by
  simpa [table, edmundsFourSeventyOne] using
    edmundsFourSeventyOneBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis edmundsFourSeventyOneBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S4_71
