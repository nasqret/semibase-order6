import SemigroupBasis.CoRoots.Order6SporadicSection26Basis
import SemigroupBasis.FiniteCertificate

/-! Literal F7 on paper p114 equals the actual direct S6_13527 catalogue table.
This is soundness and finite infrastructure only, not a completeness theorem. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

namespace SemigroupBasis.CoRoots.Order6SporadicSection26.F7
open SemigroupBasis

def tableMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0
  else if a = 1 then if b = 4 ∨ b = 5 then 1 else 0
  else if a = 2 then 2
  else if a = 3 then 3
  else if b = 0 then 0
  else if b = 1 then 1
  else if b = 2 then if a = 4 then 0 else 3
  else b

theorem table_rows_exact :
    List.ofFn (fun (a : Fin 6) => List.ofFn (fun (b : Fin 6) => (tableMul a b).val)) =
      [[0,0,0,0,0,0],[0,0,0,0,1,1],[2,2,2,2,2,2],
       [3,3,3,3,3,3],[0,1,0,3,4,5],[0,1,3,3,4,5]] := by decide

def table : FiniteTable where
  order := 6
  mul := tableMul
  assoc := by decide

def toFinFour (letter : Nat) : Fin 4 := ⟨letter % 4, Nat.mod_lt _ (by decide)⟩

theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinFour (by decide)

theorem mul_zero (a : Fin 6) : tableMul 0 a = 0 := by decide +revert
theorem mul_two (a : Fin 6) : tableMul 2 a = 2 := by decide +revert
theorem mul_three (a : Fin 6) : tableMul 3 a = 3 := by decide +revert
theorem right_zero_pair :
    tableMul 4 4 = 4 ∧ tableMul 4 5 = 5 ∧
      tableMul 5 4 = 4 ∧ tableMul 5 5 = 5 := by decide
theorem separator_products : tableMul 4 2 = 0 ∧ tableMul 5 2 = 3 := by decide

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.table_rows_exact
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.models
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.mul_zero
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.mul_two
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.mul_three
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.right_zero_pair
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.separator_products
end SemigroupBasis.CoRoots.Order6SporadicSection26.F7
