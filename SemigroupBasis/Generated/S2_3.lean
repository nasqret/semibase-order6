import SemigroupBasis.Examples.SemilatticeTwo

namespace SemigroupBasis.Generated.S2_3

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S2_3`, with table
`[[1,1],[1,2]]` in one-based notation. -/
def table : FiniteTable where
  order := 2
  mul := semilatticeTwoMul
  assoc := by decide

theorem table_eq_catalogue_model : table = semilatticeTwo := rfl

theorem representative_basis :
    BasisFor table.semigroup semilatticeBasis := by
  simpa [table, semilatticeTwo] using semilatticeBasis_complete

end SemigroupBasis.Generated.S2_3
