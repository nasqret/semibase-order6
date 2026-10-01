import SemigroupBasis.Examples.EdmundsFourTwentySeven
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_27

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_27`, with exact table
`[[1,1,3,1],[1,1,3,1],[3,3,1,3],[1,2,3,4]]`. -/
def table : FiniteTable :=
  edmundsFourTwentySeven

theorem table_eq_catalogue_model :
    table = edmundsFourTwentySeven := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_27.table := by
  unfold table edmundsFourTwentySeven
    SemigroupBasis.Generated.Catalogue.S4_27.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup edmundsFourTwentySevenBasis := by
  simpa [table] using edmundsFourTwentySevenBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis edmundsFourTwentySevenBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S4_27
