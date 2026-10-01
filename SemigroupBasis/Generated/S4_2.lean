import SemigroupBasis.Examples.CommonSquareThreeNilpotentFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_2

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_2`. -/
def table : FiniteTable where
  order := 4
  mul := commonSquareThreeNilpotentFourMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = commonSquareThreeNilpotentFour := rfl

theorem table_eq_canonical_catalogue :
    table = Catalogue.S4_2.table := rfl

theorem canonical_catalogue_eq_model :
    Catalogue.S4_2.table = commonSquareThreeNilpotentFour := by
  rw [← table_eq_canonical_catalogue]
  exact table_eq_catalogue_model

theorem representative_basis :
    BasisFor table.semigroup commonSquareThreeNilpotentBasis := by
  simpa [table, commonSquareThreeNilpotentFour] using
    commonSquareThreeNilpotentFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis commonSquareThreeNilpotentBasis) := by
  simpa [table, commonSquareThreeNilpotentFour] using
    commonSquareThreeNilpotentFourOppositeBasis_complete

end SemigroupBasis.Generated.S4_2
