import SemigroupBasis.Examples.CommutativeParityThresholdFive
import SemigroupBasis.Generated.CatalogueOrder5Part02

namespace SemigroupBasis.Generated.S5_222

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S5_222`. -/
def table : FiniteTable :=
  commutativeParityThresholdFive

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_222.table := by
  unfold table commutativeParityThresholdFive
    commutativeParityThresholdFiveMul
    SemigroupBasis.Generated.Catalogue.S5_222.table
    SemigroupBasis.Generated.Catalogue.S5_222.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup
      commutativeParityThresholdFiveBasis := by
  simpa [table] using
    commutativeParityThresholdFiveBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis commutativeParityThresholdFiveBasis) := by
  simpa [table] using
    commutativeParityThresholdFiveOppositeBasis_complete

end SemigroupBasis.Generated.S5_222
