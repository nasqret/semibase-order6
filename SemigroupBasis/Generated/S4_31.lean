import SemigroupBasis.CoRoots.S4_31
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.S4_31

open SemigroupBasis
open SemigroupBasis.Examples

/-- The canonical Smallsemi representative `S4_31`. -/
def table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S4_31.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_31.table := rfl

theorem representative_basis :
    BasisFor table.semigroup edmundsFourTwentySevenBasis := by
  simpa [table] using SemigroupBasis.CoRoots.S4_31.basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis edmundsFourTwentySevenBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S4_31
