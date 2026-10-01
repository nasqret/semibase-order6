import SemigroupBasis.Examples.CommutativeParitySupportFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_26

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_26`. -/
def table : FiniteTable where
  order := 4
  mul := paritySupportFourMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = paritySupportFour := rfl

/-- The hand-written representative is definitionally the canonical table
generated from `research/data/catalogue.json`. -/
theorem table_eq_canonical_catalogue :
    table = Catalogue.S4_26.table := rfl

theorem canonical_catalogue_eq_model :
    Catalogue.S4_26.table = paritySupportFour := by
  rw [← table_eq_canonical_catalogue]
  exact table_eq_catalogue_model

theorem representative_basis :
    BasisFor table.semigroup commutativeParitySupportBasis := by
  simpa [table, paritySupportFour] using
    commutativeParitySupportBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis commutativeParitySupportBasis) := by
  simpa [table, paritySupportFour] using
    commutativeParitySupportOppositeBasis_complete

end SemigroupBasis.Generated.S4_26
