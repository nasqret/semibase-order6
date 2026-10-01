import SemigroupBasis.Examples.CommutativePeriodTwoFromThreeOrderFive
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.Generated.CatalogueOrder5Part05

namespace SemigroupBasis.Generated.CommutativePeriodTwoFromThreeFamily

open SemigroupBasis
open SemigroupBasis.Examples

namespace S5_223

theorem table_eq_canonical_catalogue :
    s5_223 = SemigroupBasis.Generated.Catalogue.S5_223.table := by
  unfold s5_223 s5_223Mul
    SemigroupBasis.Generated.Catalogue.S5_223.table
    SemigroupBasis.Generated.Catalogue.S5_223.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_223.table.semigroup
      commutativePeriodTwoFromThreeBasis := by
  rw [← table_eq_canonical_catalogue]
  exact s5_223Basis

theorem self_dual :
    SemigroupBasis.Generated.Catalogue.S5_223.table.semigroup.opposite =
      SemigroupBasis.Generated.Catalogue.S5_223.table.semigroup := by
  rw [← table_eq_canonical_catalogue]
  exact s5_223SelfDual

theorem opposite_basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_223.table.semigroup.opposite
      commutativePeriodTwoFromThreeBasis := by
  rw [self_dual]
  exact representative_basis

end S5_223

namespace S5_226

theorem table_eq_canonical_catalogue :
    s5_226 = SemigroupBasis.Generated.Catalogue.S5_226.table := by
  unfold s5_226 s5_226Mul
    SemigroupBasis.Generated.Catalogue.S5_226.table
    SemigroupBasis.Generated.Catalogue.S5_226.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_226.table.semigroup
      commutativePeriodTwoFromThreeBasis := by
  rw [← table_eq_canonical_catalogue]
  exact s5_226Basis

theorem self_dual :
    SemigroupBasis.Generated.Catalogue.S5_226.table.semigroup.opposite =
      SemigroupBasis.Generated.Catalogue.S5_226.table.semigroup := by
  rw [← table_eq_canonical_catalogue]
  exact s5_226SelfDual

theorem opposite_basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_226.table.semigroup.opposite
      commutativePeriodTwoFromThreeBasis := by
  rw [self_dual]
  exact representative_basis

end S5_226

namespace S5_514

theorem table_eq_canonical_catalogue :
    s5_514 = SemigroupBasis.Generated.Catalogue.S5_514.table := by
  unfold s5_514 s5_514Mul
    SemigroupBasis.Generated.Catalogue.S5_514.table
    SemigroupBasis.Generated.Catalogue.S5_514.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_514.table.semigroup
      commutativePeriodTwoFromThreeBasis := by
  rw [← table_eq_canonical_catalogue]
  exact s5_514Basis

theorem self_dual :
    SemigroupBasis.Generated.Catalogue.S5_514.table.semigroup.opposite =
      SemigroupBasis.Generated.Catalogue.S5_514.table.semigroup := by
  rw [← table_eq_canonical_catalogue]
  exact s5_514SelfDual

theorem opposite_basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_514.table.semigroup.opposite
      commutativePeriodTwoFromThreeBasis := by
  rw [self_dual]
  exact representative_basis

end S5_514

end SemigroupBasis.Generated.CommutativePeriodTwoFromThreeFamily
