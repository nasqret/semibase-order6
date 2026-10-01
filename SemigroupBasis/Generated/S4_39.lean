import SemigroupBasis.Examples.FirstLetterThreeNilpotentFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_39

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_39`. -/
def table : FiniteTable where
  order := 4
  mul := firstLetterThreeNilpotentFourMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = firstLetterThreeNilpotentFour := rfl

/-- The hand-written representative is definitionally the canonical table
generated from `research/data/catalogue.json`. -/
theorem table_eq_canonical_catalogue :
    table = Catalogue.S4_39.table := rfl

theorem canonical_catalogue_eq_model :
    Catalogue.S4_39.table = firstLetterThreeNilpotentFour := by
  rw [← table_eq_canonical_catalogue]
  exact table_eq_catalogue_model

theorem representative_basis :
    BasisFor table.semigroup firstLetterThreeNilpotentFourBasis := by
  simpa [table, firstLetterThreeNilpotentFour] using
    firstLetterThreeNilpotentFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis firstLetterThreeNilpotentFourBasis) := by
  simpa [table, firstLetterThreeNilpotentFour] using
    firstLetterThreeNilpotentFourOppositeBasis_complete

end SemigroupBasis.Generated.S4_39
