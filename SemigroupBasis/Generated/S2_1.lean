import SemigroupBasis.Examples.NullTwo

namespace SemigroupBasis.Generated.S2_1

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S2_1`, the two-element null semigroup. -/
def table : FiniteTable where
  order := 2
  mul := fun _ _ => 0
  assoc := by intros; rfl

theorem table_eq_catalogue_model : table = nullTwo := rfl

theorem representative_basis :
    BasisFor table.semigroup nullBasis := by
  simpa [table, nullTwo] using nullBasis_complete

end SemigroupBasis.Generated.S2_1
