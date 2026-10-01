import SemigroupBasis.Examples.FirstRepeatedMarkerFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_72

open SemigroupBasis
open SemigroupBasis.Examples

def table : FiniteTable where
  order := 4
  mul := firstRepeatedMarkerFourMul
  assoc := by decide

theorem table_eq_catalogue_model :
    table = firstRepeatedMarkerFour := rfl

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_72.table := by
  unfold table SemigroupBasis.Generated.Catalogue.S4_72.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor table.semigroup firstRepeatedMarkerFourBasis := by
  simpa [table, firstRepeatedMarkerFour] using
    firstRepeatedMarkerFourBasis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis firstRepeatedMarkerFourBasis) := by
  simpa [table, firstRepeatedMarkerFour] using
    firstRepeatedMarkerFourBasis_complete.oppositeReversed

end SemigroupBasis.Generated.S4_72
