import SemigroupBasis.Examples.FirstLetterPowerThree

namespace SemigroupBasis.Generated.S3_7

open SemigroupBasis
open SemigroupBasis.Examples

def table : FiniteTable where
  order := 3
  mul := firstPowerMul
  assoc := by decide

theorem table_eq_catalogue_model : table = firstLetterPowerThree := rfl

theorem representative_basis :
    BasisFor table.semigroup firstPowerBasis := by
  simpa [table, firstLetterPowerThree] using firstPowerBasisComplete

theorem opposite_basis :
    BasisFor table.semigroup.opposite firstPowerOppositeBasis := by
  simpa [table, firstLetterPowerThree] using firstPowerOppositeBasisComplete

end SemigroupBasis.Generated.S3_7
