import SemigroupBasis.CoRoots.S4_90
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.S4_90

open SemigroupBasis
open SemigroupBasis.CoRoots.S4_90

/-- The canonical Smallsemi representative `S4_90`. -/
def table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S4_90.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_90.table := rfl

theorem representative_basis :
    BasisFor table.semigroup basis := by
  simpa [table] using basis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S4_90
