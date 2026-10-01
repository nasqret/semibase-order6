import SemigroupBasis.Examples.CyclicThreeThree
import SemigroupBasis.Generated.CatalogueOrder5Part10

namespace SemigroupBasis.CoRoots.S5_540

open SemigroupBasis
open SemigroupBasis.Examples

abbrev basis : List (Identity Nat) :=
  cyclicThreeThreeBasis

namespace S5_1159

/-- The actual root of the family, presented as `C_{3,3}`. -/
def table : FiniteTable :=
  cyclicThreeThree

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_1159.table := by
  unfold table cyclicThreeThree cyclicThreeThreeMul
    SemigroupBasis.Generated.Catalogue.S5_1159.table
    SemigroupBasis.Generated.Catalogue.S5_1159.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

def generator : Fin 5 := 4

def powerSequenceOneBased : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8].map
    (fun exponent => (cyclicThreeThreeState exponent).val + 1)

theorem generatorOneBased_certificate :
    generator.val + 1 = 5 := rfl

theorem powerSequenceOneBased_certificate :
    powerSequenceOneBased = [5, 4, 1, 2, 3, 1, 2, 3] := by
  decide

theorem models :
    Models SemigroupBasis.Generated.Catalogue.S5_1159.table.semigroup
      basis := by
  rw [← table_eq_canonical_catalogue]
  exact cyclicThreeThreeBasis_models

theorem representative_basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_1159.table.semigroup
      basis := by
  rw [← table_eq_canonical_catalogue]
  exact cyclicThreeThreeBasis_complete

theorem self_dual :
    SemigroupBasis.Generated.Catalogue.S5_1159.table.semigroup.opposite =
      SemigroupBasis.Generated.Catalogue.S5_1159.table.semigroup := by
  rw [← table_eq_canonical_catalogue]
  exact cyclicThreeThree_selfDual

theorem opposite_basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_1159.table.semigroup.opposite
      basis := by
  rw [self_dual]
  exact representative_basis

end S5_1159

end SemigroupBasis.CoRoots.S5_540
