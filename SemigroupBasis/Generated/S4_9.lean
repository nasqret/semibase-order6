import SemigroupBasis.Examples.ThreeNilpotentFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_9

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_9`. -/
def table : FiniteTable where
  order := 4
  mul := threeNilpotentFourMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = threeNilpotentFour := rfl

/-- The hand-written representative is definitionally the canonical table
generated from `research/data/catalogue.json`. -/
theorem table_eq_canonical_catalogue :
    table = Catalogue.S4_9.table := rfl

theorem canonical_catalogue_eq_model :
    Catalogue.S4_9.table = threeNilpotentFour := by
  rw [← table_eq_canonical_catalogue]
  exact table_eq_catalogue_model

theorem representative_basis :
    BasisFor table.semigroup threeNilpotentFourBasis := by
  simpa [table, threeNilpotentFour] using
    threeNilpotentFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis threeNilpotentFourBasis) := by
  simpa [table, threeNilpotentFour] using
    threeNilpotentFourOppositeBasis_complete

end SemigroupBasis.Generated.S4_9
