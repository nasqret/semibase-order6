import SemigroupBasis.Examples.CommutativeExponentFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_40

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_40`, with exact table
`[[1,1,1,1],[1,1,1,2],[1,1,2,3],[1,2,3,4]]`. -/
def table : FiniteTable where
  order := 4
  mul := commutativeExponentFourMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = commutativeExponentFour := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_40.table := by
  unfold table SemigroupBasis.Generated.Catalogue.S4_40.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup commutativeExponentFourBasis := by
  simpa [table, commutativeExponentFour] using
    commutativeExponentFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis commutativeExponentFourBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S4_40
