import SemigroupBasis.Examples.CommutativeCommonSquareThreeNilpotentFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_3

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_3`. -/
def table : FiniteTable where
  order := 4
  mul := commutativeCommonSquareThreeNilpotentFourMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = commutativeCommonSquareThreeNilpotentFour := rfl

theorem table_eq_canonical_catalogue :
    table = Catalogue.S4_3.table := by
  unfold table Catalogue.S4_3.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup
      commutativeCommonSquareThreeNilpotentBasis := by
  simpa [table, commutativeCommonSquareThreeNilpotentFour] using
    commutativeCommonSquareThreeNilpotentBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis commutativeCommonSquareThreeNilpotentBasis) := by
  simpa [table, commutativeCommonSquareThreeNilpotentFour] using
    commutativeCommonSquareThreeNilpotentOppositeBasis_complete

end SemigroupBasis.Generated.S4_3
