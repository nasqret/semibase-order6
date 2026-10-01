import SemigroupBasis.CoRoots.Order6SporadicSection17Basis
import SemigroupBasis.FiniteReflection

/-! Literal direct catalogue table and raw-basis soundness.
Every closed decision ranges over at most three Fin6 values.
This module supplies no completeness assumption. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.S6_7987
open SemigroupBasis

def tableMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6)) else (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6))

def table : FiniteTable where
  order := 6
  mul := tableMul
  assoc := by decide

theorem table_literal_exact :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (tableMul a b).val)) =
      [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2], [0, 0, 2, 3, 4, 3], [0, 2, 2, 3, 4, 3], [0, 0, 2, 3, 4, 5]] := by decide

private theorem checkPower :
    ∀ x : Fin 6,
      (tableMul (tableMul x x) x) = (tableMul x x) := by decide

theorem modelsPower : lawPower.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkPower (valuation 0)

private theorem checkLeft :
    ∀ x y : Fin 6,
      (tableMul (tableMul (tableMul x x) y) x) = (tableMul (tableMul x y) x) := by decide

theorem modelsLeft : lawLeft.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkLeft (valuation 0) (valuation 1)

private theorem checkRight :
    ∀ x y : Fin 6,
      (tableMul (tableMul (tableMul x y) x) x) = (tableMul (tableMul x y) x) := by decide

theorem modelsRight : lawRight.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkRight (valuation 0) (valuation 1)

private theorem checkPermute :
    ∀ x y z : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul x x) y) y) z) z) = (tableMul (tableMul (tableMul (tableMul (tableMul y y) x) x) z) z) := by decide

theorem modelsPermute : lawPermute.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkPermute (valuation 0) (valuation 1) (valuation 2)

private theorem checkInflate :
    ∀ x y : Fin 6,
      (tableMul (tableMul (tableMul x x) y) y) = (tableMul (tableMul (tableMul y x) x) y) := by decide

theorem modelsInflate : lawInflate.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkInflate (valuation 0) (valuation 1)

private theorem checkInflateH :
    ∀ x h y : Fin 6,
      (tableMul (tableMul (tableMul (tableMul x x) h) y) y) = (tableMul (tableMul (tableMul (tableMul y x) x) h) y) := by decide

theorem modelsInflateH : lawInflateH.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkInflateH (valuation 0) (valuation 2) (valuation 1)

private theorem checkSwap :
    ∀ x y : Fin 6,
      (tableMul (tableMul (tableMul x y) x) y) = (tableMul (tableMul (tableMul y x) x) y) := by decide

theorem modelsSwap : lawSwap.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkSwap (valuation 0) (valuation 1)

private theorem checkSwapK :
    ∀ x y k : Fin 6,
      (tableMul (tableMul (tableMul (tableMul x y) x) k) y) = (tableMul (tableMul (tableMul (tableMul y x) x) k) y) := by decide

theorem modelsSwapK : lawSwapK.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkSwapK (valuation 0) (valuation 1) (valuation 3)

private theorem checkSwapH :
    ∀ x y h : Fin 6,
      (tableMul (tableMul (tableMul (tableMul x y) h) x) y) = (tableMul (tableMul (tableMul (tableMul y x) h) x) y) := by decide

theorem modelsSwapH : lawSwapH.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkSwapH (valuation 0) (valuation 1) (valuation 2)

private theorem checkSwapHK_0 :
    ∀ y h k : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) y) h) (0 : Fin 6)) k) y) = (tableMul (tableMul (tableMul (tableMul (tableMul y (0 : Fin 6)) h) (0 : Fin 6)) k) y) := by decide

private theorem checkSwapHK_1 :
    ∀ y h k : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) y) h) (1 : Fin 6)) k) y) = (tableMul (tableMul (tableMul (tableMul (tableMul y (1 : Fin 6)) h) (1 : Fin 6)) k) y) := by decide

private theorem checkSwapHK_2 :
    ∀ y h k : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) y) h) (2 : Fin 6)) k) y) = (tableMul (tableMul (tableMul (tableMul (tableMul y (2 : Fin 6)) h) (2 : Fin 6)) k) y) := by decide

private theorem checkSwapHK_3 :
    ∀ y h k : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) y) h) (3 : Fin 6)) k) y) = (tableMul (tableMul (tableMul (tableMul (tableMul y (3 : Fin 6)) h) (3 : Fin 6)) k) y) := by decide

private theorem checkSwapHK_4 :
    ∀ y h k : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) y) h) (4 : Fin 6)) k) y) = (tableMul (tableMul (tableMul (tableMul (tableMul y (4 : Fin 6)) h) (4 : Fin 6)) k) y) := by decide

private theorem checkSwapHK_5 :
    ∀ y h k : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) y) h) (5 : Fin 6)) k) y) = (tableMul (tableMul (tableMul (tableMul (tableMul y (5 : Fin 6)) h) (5 : Fin 6)) k) y) := by decide

private theorem checkSwapHK :
    ∀ x y h k : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul x y) h) x) k) y) = (tableMul (tableMul (tableMul (tableMul (tableMul y x) h) x) k) y) := by
  intro x y h k
  have cases_x : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
    revert x
    decide
  rcases cases_x with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSwapHK_0 y h k
  · exact checkSwapHK_1 y h k
  · exact checkSwapHK_2 y h k
  · exact checkSwapHK_3 y h k
  · exact checkSwapHK_4 y h k
  · exact checkSwapHK_5 y h k

theorem modelsSwapHK : lawSwapHK.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkSwapHK (valuation 0) (valuation 1) (valuation 2) (valuation 3)

theorem models : Models table.semigroup basis := by
  intro e member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact modelsPower
  · exact modelsLeft
  · exact modelsRight
  · exact modelsPermute
  · exact modelsInflate
  · exact modelsInflateH
  · exact modelsSwap
  · exact modelsSwapK
  · exact modelsSwapH
  · exact modelsSwapHK

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.S6_7987.table_literal_exact
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.S6_7987.models
end SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.S6_7987
