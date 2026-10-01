import SemigroupBasis.Examples.LeftZeroTwo

namespace SemigroupBasis.Generated.S2_4

open SemigroupBasis
open SemigroupBasis.Examples

/--
The stored Smallsemi representative `S2_4`, whose canonical table is
`[[1, 1], [2, 2]]`.
-/
def table : FiniteTable where
  order := 2
  mul := fun a _ => a
  assoc := by intros; rfl

theorem table_eq_catalogue_model : table = leftZeroTwo := rfl

theorem representative_basis :
    BasisFor table.semigroup leftZeroBasis := by
  simpa [table, leftZeroTwo] using leftZeroBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite rightZeroBasis := by
  simpa [table, leftZeroTwo] using rightZeroBasis_complete

end SemigroupBasis.Generated.S2_4
