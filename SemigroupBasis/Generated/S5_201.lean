import SemigroupBasis.Examples.CommutativeCappedSupportFive
import SemigroupBasis.Generated.CatalogueOrder5Part02

namespace SemigroupBasis.Generated.S5_201

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S5_201`. -/
def table : FiniteTable :=
  commutativeCappedSupportFive

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_201.table := by
  unfold table commutativeCappedSupportFive
    commutativeCappedSupportFiveMul
    SemigroupBasis.Generated.Catalogue.S5_201.table
    SemigroupBasis.Generated.Catalogue.S5_201.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup
      commutativeCappedSupportFiveBasis := by
  simpa [table] using
    commutativeCappedSupportFiveBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis commutativeCappedSupportFiveBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S5_201
