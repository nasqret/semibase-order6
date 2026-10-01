import SemigroupBasis.Examples.CommutativePositiveModThreeFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_124

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_124`, with exact table
`[[1,1,1,1],[1,2,3,4],[1,3,4,2],[1,4,2,3]]`. -/
def table : FiniteTable where
  order := 4
  mul := commutativePositiveModThreeFourMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = commutativePositiveModThreeFour := rfl

theorem table_eq_canonical_catalogue :
    table =
      SemigroupBasis.Generated.Catalogue.S4_124.table := by
  unfold table
    commutativePositiveModThreeFourMul
    SemigroupBasis.Generated.Catalogue.S4_124.table
    SemigroupBasis.Generated.Catalogue.S4_124.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup
      commutativePositiveModThreeBasis := by
  simpa [table, commutativePositiveModThreeFour] using
    commutativePositiveModThreeFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis commutativePositiveModThreeBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S4_124
