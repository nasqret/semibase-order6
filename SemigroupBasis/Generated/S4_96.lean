import SemigroupBasis.Examples.AffineParityFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_96

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_96`. -/
def table : FiniteTable :=
  affineParityFour

theorem table_eq_canonical_catalogue :
    table =
      SemigroupBasis.Generated.Catalogue.S4_96.table :=
  rfl

theorem representative_basis :
    BasisFor table.semigroup affineParityFourBasis := by
  simpa [table] using affineParityFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis affineParityFourBasis) := by
  simpa [table, affineParityFourOppositeBasis] using
    affineParityFourOppositeBasis_complete

end SemigroupBasis.Generated.S4_96
