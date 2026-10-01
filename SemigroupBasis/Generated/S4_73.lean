import SemigroupBasis.Examples.EdmundsFourSeventyThree
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_73

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_73`, with exact table
`[[1,1,1,1],[1,1,1,2],[3,3,3,3],[1,1,3,4]]`. -/
def table : FiniteTable where
  order := 4
  mul := edmundsFourSeventyThreeMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = edmundsFourSeventyThree := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_73.table := by
  unfold table SemigroupBasis.Generated.Catalogue.S4_73.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup edmundsFourSeventyThreeBasis := by
  simpa [table, edmundsFourSeventyThree] using
    edmundsFourSeventyThreeBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis edmundsFourSeventyThreeBasis) := by
  simpa [table, edmundsFourSeventyThree] using
    edmundsFourSeventyThreeBasis_complete.oppositeReversed

end SemigroupBasis.Generated.S4_73
