import SemigroupBasis.Examples.CyclicTwo

namespace SemigroupBasis.Generated.S2_2

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S2_2`, with exact table
`[[1,2],[2,1]]` in one-based notation. -/
def table : FiniteTable where
  order := 2
  mul := cyclicTwoMul
  assoc := by decide

theorem table_eq_catalogue_model : table = cyclicTwo := rfl

theorem representative_basis :
    BasisFor table.semigroup cyclicTwoBasis := by
  simpa [table, cyclicTwo] using cyclicTwoBasis_complete

end SemigroupBasis.Generated.S2_2
