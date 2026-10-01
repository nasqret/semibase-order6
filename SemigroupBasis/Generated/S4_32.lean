import SemigroupBasis.Examples.CommutativePeriodTwoFromTwoFourThirtyTwo
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_32

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_32`, with exact table
`[[1,2,2,1],[2,1,1,2],[2,1,1,3],[1,2,3,4]]`. -/
def table : FiniteTable :=
  s4_32

theorem table_eq_catalogue_model :
    table = s4_32 := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_32.table := by
  unfold table s4_32 SemigroupBasis.Generated.Catalogue.S4_32.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup commutativePeriodTwoFromTwoBasis := by
  simpa [table] using s4_32Basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      commutativePeriodTwoFromTwoBasis :=
  commutativePeriodTwoFromTwoBasis_opposite_complete
    representative_basis

end SemigroupBasis.Generated.S4_32
