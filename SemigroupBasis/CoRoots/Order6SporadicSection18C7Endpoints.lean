import SemigroupBasis.CoRoots.Order6SporadicSection18Completeness
import SemigroupBasis.Opposite

/-! Literal catalogue endpoints for C7. The unrestricted theorem is inherited
from the frozen completeness cut; the opposite uses literal word reversal. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.C7.S6_3841

open SemigroupBasis

abbrev table : FiniteTable := Actual.table

def oppositeTable : FiniteTable where
  order := table.order
  mul a b := table.mul b a
  assoc a b c := (table.assoc c b a).symm

theorem representative_table_exact :
    (List.finRange 6).map (fun a =>
      (List.finRange 6).map (fun b => (table.mul a b).val)) =
    [[0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 1],
     [0, 0, 0, 0, 0, 2],
     [0, 0, 1, 0, 3, 0],
     [0, 0, 2, 0, 4, 0],
     [0, 1, 0, 3, 0, 5]] := by decide

theorem opposite_table_exact :
    (List.finRange 6).map (fun a =>
      (List.finRange 6).map (fun b => (oppositeTable.mul a b).val)) =
    [[0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 1],
     [0, 0, 0, 1, 2, 0],
     [0, 0, 0, 0, 0, 3],
     [0, 0, 0, 3, 4, 0],
     [0, 1, 2, 0, 0, 5]] := by decide

theorem basis_length : basis.length = 22 := by decide

theorem representative_basis : BasisFor table.semigroup basis :=
  Canonical.basisFor_actual

theorem opposite_basis : BasisFor oppositeTable.semigroup (reversedBasis basis) := by
  change BasisFor table.semigroup.opposite (reversedBasis basis)
  exact representative_basis.oppositeReversed

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.C7.S6_3841.representative_table_exact
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.C7.S6_3841.opposite_table_exact
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.C7.S6_3841.basis_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.C7.S6_3841.representative_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.C7.S6_3841.opposite_basis

end SemigroupBasis.CoRoots.Order6SporadicSection18.C7.S6_3841

