import SemigroupBasis.Examples.CommutativePeriodThreeFromTwoOrderFive
import SemigroupBasis.Generated.CatalogueOrder5Part08
import SemigroupBasis.Generated.CatalogueOrder5Part10

namespace SemigroupBasis.Generated.CommutativePeriodThreeFromTwoFamily

open SemigroupBasis
open SemigroupBasis.Examples

namespace S5_1001

theorem table_eq_canonical_catalogue :
    s5_1001 = SemigroupBasis.Generated.Catalogue.S5_1001.table := by
  unfold s5_1001 s5_1001Mul
    SemigroupBasis.Generated.Catalogue.S5_1001.table
    SemigroupBasis.Generated.Catalogue.S5_1001.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1001.table.semigroup
      commutativePeriodThreeFromTwoBasis := by
  rw [← table_eq_canonical_catalogue]
  exact s5_1001Basis

theorem self_dual :
    SemigroupBasis.Generated.Catalogue.S5_1001.table.semigroup.opposite =
      SemigroupBasis.Generated.Catalogue.S5_1001.table.semigroup := by
  rw [← table_eq_canonical_catalogue]
  exact s5_1001SelfDual

theorem opposite_basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_1001.table.semigroup.opposite
      commutativePeriodThreeFromTwoBasis := by
  rw [self_dual]
  exact representative_basis

end S5_1001

namespace S5_1004

theorem table_eq_canonical_catalogue :
    s5_1004 = SemigroupBasis.Generated.Catalogue.S5_1004.table := by
  unfold s5_1004 s5_1004Mul
    SemigroupBasis.Generated.Catalogue.S5_1004.table
    SemigroupBasis.Generated.Catalogue.S5_1004.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1004.table.semigroup
      commutativePeriodThreeFromTwoBasis := by
  rw [← table_eq_canonical_catalogue]
  exact s5_1004Basis

theorem self_dual :
    SemigroupBasis.Generated.Catalogue.S5_1004.table.semigroup.opposite =
      SemigroupBasis.Generated.Catalogue.S5_1004.table.semigroup := by
  rw [← table_eq_canonical_catalogue]
  exact s5_1004SelfDual

theorem opposite_basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_1004.table.semigroup.opposite
      commutativePeriodThreeFromTwoBasis := by
  rw [self_dual]
  exact representative_basis

end S5_1004

namespace S5_1156

theorem table_eq_canonical_catalogue :
    s5_1156 = SemigroupBasis.Generated.Catalogue.S5_1156.table := by
  unfold s5_1156 s5_1156Mul
    SemigroupBasis.Generated.Catalogue.S5_1156.table
    SemigroupBasis.Generated.Catalogue.S5_1156.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1156.table.semigroup
      commutativePeriodThreeFromTwoBasis := by
  rw [← table_eq_canonical_catalogue]
  exact s5_1156Basis

theorem self_dual :
    SemigroupBasis.Generated.Catalogue.S5_1156.table.semigroup.opposite =
      SemigroupBasis.Generated.Catalogue.S5_1156.table.semigroup := by
  rw [← table_eq_canonical_catalogue]
  exact s5_1156SelfDual

theorem opposite_basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_1156.table.semigroup.opposite
      commutativePeriodThreeFromTwoBasis := by
  rw [self_dual]
  exact representative_basis

end S5_1156

end SemigroupBasis.Generated.CommutativePeriodThreeFromTwoFamily
