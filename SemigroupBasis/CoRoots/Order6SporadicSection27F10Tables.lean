import SemigroupBasis.CoRoots.Order6SporadicSection27F10Basis

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27.F10

open SemigroupBasis

/-- Literal, unrelabelled S6_13560 / paper F10 multiplication, zero-based. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0
  else if a = 1 then
    if b = 4 then 1 else if b = 5 then 2 else 0
  else if a = 2 then 2
  else if a = 3 then
    if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2
    else if b = 3 then 3 else if b = 4 then 1 else 2
  else if a = 4 then
    if b = 4 then 4 else if b = 5 then 5 else 0
  else 5

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem table_literal_exact :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul a b).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,1,2], [2,2,2,2,2,2],
       [0,1,2,3,1,2], [0,0,0,0,4,5], [5,5,5,5,5,5]] := by decide

/-! Each closed decision ranges over at most THREE finite values. -/

private theorem checkA_empty :
    ∀ x : Fin 6,
      (mul (mul x x) x) = (mul x x) := by decide

private theorem validA_empty : (lawA_empty).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkA_empty (valuation 0)

private theorem checkA_H :
    ∀ x h : Fin 6,
      (mul (mul (mul x h) x) x) = (mul (mul x h) x) := by decide

private theorem validA_H : (lawA_H).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkA_H (valuation 0) (valuation 2)

private theorem checkB_empty :
    ∀ x y : Fin 6,
      (mul (mul (mul x y) x) y) = (mul (mul (mul x y) y) x) := by decide

private theorem validB_empty : (lawB_empty).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkB_empty (valuation 0) (valuation 1)

private theorem checkB_K :
    ∀ x y k : Fin 6,
      (mul (mul (mul (mul x y) k) x) y) = (mul (mul (mul (mul x y) k) y) x) := by decide

private theorem validB_K : (lawB_K).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkB_K (valuation 0) (valuation 1) (valuation 3)

private theorem checkB_H :
    ∀ x h y : Fin 6,
      (mul (mul (mul (mul x h) y) x) y) = (mul (mul (mul (mul x h) y) y) x) := by decide

private theorem validB_H : (lawB_H).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkB_H (valuation 0) (valuation 2) (valuation 1)

private theorem checkB_HK_0 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (0 : Fin 6) h) y) k) (0 : Fin 6)) y) = (mul (mul (mul (mul (mul (0 : Fin 6) h) y) k) y) (0 : Fin 6)) := by decide

private theorem checkB_HK_1 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (1 : Fin 6) h) y) k) (1 : Fin 6)) y) = (mul (mul (mul (mul (mul (1 : Fin 6) h) y) k) y) (1 : Fin 6)) := by decide

private theorem checkB_HK_2 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (2 : Fin 6) h) y) k) (2 : Fin 6)) y) = (mul (mul (mul (mul (mul (2 : Fin 6) h) y) k) y) (2 : Fin 6)) := by decide

private theorem checkB_HK_3 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (3 : Fin 6) h) y) k) (3 : Fin 6)) y) = (mul (mul (mul (mul (mul (3 : Fin 6) h) y) k) y) (3 : Fin 6)) := by decide

private theorem checkB_HK_4 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (4 : Fin 6) h) y) k) (4 : Fin 6)) y) = (mul (mul (mul (mul (mul (4 : Fin 6) h) y) k) y) (4 : Fin 6)) := by decide

private theorem checkB_HK_5 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (5 : Fin 6) h) y) k) (5 : Fin 6)) y) = (mul (mul (mul (mul (mul (5 : Fin 6) h) y) k) y) (5 : Fin 6)) := by decide

private theorem checkB_HK :
    ∀ x h y k : Fin 6,
      (mul (mul (mul (mul (mul x h) y) k) x) y) = (mul (mul (mul (mul (mul x h) y) k) y) x) := by
  intro x h y k
  have cases_x : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
    revert x
    decide
  rcases cases_x with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkB_HK_0 h y k
  · exact checkB_HK_1 h y k
  · exact checkB_HK_2 h y k
  · exact checkB_HK_3 h y k
  · exact checkB_HK_4 h y k
  · exact checkB_HK_5 h y k

private theorem validB_HK : (lawB_HK).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkB_HK (valuation 0) (valuation 2) (valuation 1) (valuation 3)

private theorem checkC_empty :
    ∀ x y : Fin 6,
      (mul (mul (mul x y) y) x) = (mul (mul x y) x) := by decide

private theorem validC_empty : (lawC_empty).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkC_empty (valuation 0) (valuation 1)

private theorem checkC_K :
    ∀ x y k : Fin 6,
      (mul (mul (mul (mul x y) k) y) x) = (mul (mul (mul x y) k) x) := by decide

private theorem validC_K : (lawC_K).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkC_K (valuation 0) (valuation 1) (valuation 3)

private theorem checkC_H :
    ∀ x h y : Fin 6,
      (mul (mul (mul (mul x h) y) y) x) = (mul (mul (mul x h) y) x) := by decide

private theorem validC_H : (lawC_H).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkC_H (valuation 0) (valuation 2) (valuation 1)

private theorem checkC_HK_0 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (0 : Fin 6) h) y) k) y) (0 : Fin 6)) = (mul (mul (mul (mul (0 : Fin 6) h) y) k) (0 : Fin 6)) := by decide

private theorem checkC_HK_1 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (1 : Fin 6) h) y) k) y) (1 : Fin 6)) = (mul (mul (mul (mul (1 : Fin 6) h) y) k) (1 : Fin 6)) := by decide

private theorem checkC_HK_2 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (2 : Fin 6) h) y) k) y) (2 : Fin 6)) = (mul (mul (mul (mul (2 : Fin 6) h) y) k) (2 : Fin 6)) := by decide

private theorem checkC_HK_3 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (3 : Fin 6) h) y) k) y) (3 : Fin 6)) = (mul (mul (mul (mul (3 : Fin 6) h) y) k) (3 : Fin 6)) := by decide

private theorem checkC_HK_4 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (4 : Fin 6) h) y) k) y) (4 : Fin 6)) = (mul (mul (mul (mul (4 : Fin 6) h) y) k) (4 : Fin 6)) := by decide

private theorem checkC_HK_5 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (5 : Fin 6) h) y) k) y) (5 : Fin 6)) = (mul (mul (mul (mul (5 : Fin 6) h) y) k) (5 : Fin 6)) := by decide

private theorem checkC_HK :
    ∀ x h y k : Fin 6,
      (mul (mul (mul (mul (mul x h) y) k) y) x) = (mul (mul (mul (mul x h) y) k) x) := by
  intro x h y k
  have cases_x : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
    revert x
    decide
  rcases cases_x with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkC_HK_0 h y k
  · exact checkC_HK_1 h y k
  · exact checkC_HK_2 h y k
  · exact checkC_HK_3 h y k
  · exact checkC_HK_4 h y k
  · exact checkC_HK_5 h y k

private theorem validC_HK : (lawC_HK).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkC_HK (valuation 0) (valuation 2) (valuation 1) (valuation 3)

private theorem checkD_empty :
    ∀ x y : Fin 6,
      (mul (mul (mul x y) x) y) = (mul (mul (mul x y) x) x) := by decide

private theorem validD_empty : (lawD_empty).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkD_empty (valuation 0) (valuation 1)

private theorem checkD_T :
    ∀ x y t : Fin 6,
      (mul (mul (mul (mul x y) x) t) y) = (mul (mul (mul (mul x y) x) t) x) := by decide

private theorem validD_T : (lawD_T).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkD_T (valuation 0) (valuation 1) (valuation 4)

private theorem checkD_K :
    ∀ x y k : Fin 6,
      (mul (mul (mul (mul x y) k) x) y) = (mul (mul (mul (mul x y) k) x) x) := by decide

private theorem validD_K : (lawD_K).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkD_K (valuation 0) (valuation 1) (valuation 3)

private theorem checkD_KT_0 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (0 : Fin 6) y) k) (0 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (0 : Fin 6) y) k) (0 : Fin 6)) t) (0 : Fin 6)) := by decide

private theorem checkD_KT_1 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (1 : Fin 6) y) k) (1 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (1 : Fin 6) y) k) (1 : Fin 6)) t) (1 : Fin 6)) := by decide

private theorem checkD_KT_2 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (2 : Fin 6) y) k) (2 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (2 : Fin 6) y) k) (2 : Fin 6)) t) (2 : Fin 6)) := by decide

private theorem checkD_KT_3 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (3 : Fin 6) y) k) (3 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (3 : Fin 6) y) k) (3 : Fin 6)) t) (3 : Fin 6)) := by decide

private theorem checkD_KT_4 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (4 : Fin 6) y) k) (4 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (4 : Fin 6) y) k) (4 : Fin 6)) t) (4 : Fin 6)) := by decide

private theorem checkD_KT_5 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (5 : Fin 6) y) k) (5 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (5 : Fin 6) y) k) (5 : Fin 6)) t) (5 : Fin 6)) := by decide

private theorem checkD_KT :
    ∀ x y k t : Fin 6,
      (mul (mul (mul (mul (mul x y) k) x) t) y) = (mul (mul (mul (mul (mul x y) k) x) t) x) := by
  intro x y k t
  have cases_x : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
    revert x
    decide
  rcases cases_x with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkD_KT_0 y k t
  · exact checkD_KT_1 y k t
  · exact checkD_KT_2 y k t
  · exact checkD_KT_3 y k t
  · exact checkD_KT_4 y k t
  · exact checkD_KT_5 y k t

private theorem validD_KT : (lawD_KT).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkD_KT (valuation 0) (valuation 1) (valuation 3) (valuation 4)

private theorem checkD_H :
    ∀ x h y : Fin 6,
      (mul (mul (mul (mul x h) y) x) y) = (mul (mul (mul (mul x h) y) x) x) := by decide

private theorem validD_H : (lawD_H).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkD_H (valuation 0) (valuation 2) (valuation 1)

private theorem checkD_HT_0 :
    ∀ h y t : Fin 6,
      (mul (mul (mul (mul (mul (0 : Fin 6) h) y) (0 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (0 : Fin 6) h) y) (0 : Fin 6)) t) (0 : Fin 6)) := by decide

private theorem checkD_HT_1 :
    ∀ h y t : Fin 6,
      (mul (mul (mul (mul (mul (1 : Fin 6) h) y) (1 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (1 : Fin 6) h) y) (1 : Fin 6)) t) (1 : Fin 6)) := by decide

private theorem checkD_HT_2 :
    ∀ h y t : Fin 6,
      (mul (mul (mul (mul (mul (2 : Fin 6) h) y) (2 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (2 : Fin 6) h) y) (2 : Fin 6)) t) (2 : Fin 6)) := by decide

private theorem checkD_HT_3 :
    ∀ h y t : Fin 6,
      (mul (mul (mul (mul (mul (3 : Fin 6) h) y) (3 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (3 : Fin 6) h) y) (3 : Fin 6)) t) (3 : Fin 6)) := by decide

private theorem checkD_HT_4 :
    ∀ h y t : Fin 6,
      (mul (mul (mul (mul (mul (4 : Fin 6) h) y) (4 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (4 : Fin 6) h) y) (4 : Fin 6)) t) (4 : Fin 6)) := by decide

private theorem checkD_HT_5 :
    ∀ h y t : Fin 6,
      (mul (mul (mul (mul (mul (5 : Fin 6) h) y) (5 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (5 : Fin 6) h) y) (5 : Fin 6)) t) (5 : Fin 6)) := by decide

private theorem checkD_HT :
    ∀ x h y t : Fin 6,
      (mul (mul (mul (mul (mul x h) y) x) t) y) = (mul (mul (mul (mul (mul x h) y) x) t) x) := by
  intro x h y t
  have cases_x : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
    revert x
    decide
  rcases cases_x with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkD_HT_0 h y t
  · exact checkD_HT_1 h y t
  · exact checkD_HT_2 h y t
  · exact checkD_HT_3 h y t
  · exact checkD_HT_4 h y t
  · exact checkD_HT_5 h y t

private theorem validD_HT : (lawD_HT).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkD_HT (valuation 0) (valuation 2) (valuation 1) (valuation 4)

private theorem checkD_HK_0 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (0 : Fin 6) h) y) k) (0 : Fin 6)) y) = (mul (mul (mul (mul (mul (0 : Fin 6) h) y) k) (0 : Fin 6)) (0 : Fin 6)) := by decide

private theorem checkD_HK_1 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (1 : Fin 6) h) y) k) (1 : Fin 6)) y) = (mul (mul (mul (mul (mul (1 : Fin 6) h) y) k) (1 : Fin 6)) (1 : Fin 6)) := by decide

private theorem checkD_HK_2 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (2 : Fin 6) h) y) k) (2 : Fin 6)) y) = (mul (mul (mul (mul (mul (2 : Fin 6) h) y) k) (2 : Fin 6)) (2 : Fin 6)) := by decide

private theorem checkD_HK_3 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (3 : Fin 6) h) y) k) (3 : Fin 6)) y) = (mul (mul (mul (mul (mul (3 : Fin 6) h) y) k) (3 : Fin 6)) (3 : Fin 6)) := by decide

private theorem checkD_HK_4 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (4 : Fin 6) h) y) k) (4 : Fin 6)) y) = (mul (mul (mul (mul (mul (4 : Fin 6) h) y) k) (4 : Fin 6)) (4 : Fin 6)) := by decide

private theorem checkD_HK_5 :
    ∀ h y k : Fin 6,
      (mul (mul (mul (mul (mul (5 : Fin 6) h) y) k) (5 : Fin 6)) y) = (mul (mul (mul (mul (mul (5 : Fin 6) h) y) k) (5 : Fin 6)) (5 : Fin 6)) := by decide

private theorem checkD_HK :
    ∀ x h y k : Fin 6,
      (mul (mul (mul (mul (mul x h) y) k) x) y) = (mul (mul (mul (mul (mul x h) y) k) x) x) := by
  intro x h y k
  have cases_x : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
    revert x
    decide
  rcases cases_x with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkD_HK_0 h y k
  · exact checkD_HK_1 h y k
  · exact checkD_HK_2 h y k
  · exact checkD_HK_3 h y k
  · exact checkD_HK_4 h y k
  · exact checkD_HK_5 h y k

private theorem validD_HK : (lawD_HK).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkD_HK (valuation 0) (valuation 2) (valuation 1) (valuation 3)

private theorem checkD_HKT_0_0 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (0 : Fin 6) (0 : Fin 6)) y) k) (0 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (0 : Fin 6) (0 : Fin 6)) y) k) (0 : Fin 6)) t) (0 : Fin 6)) := by decide

private theorem checkD_HKT_0_1 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (0 : Fin 6) (1 : Fin 6)) y) k) (0 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (0 : Fin 6) (1 : Fin 6)) y) k) (0 : Fin 6)) t) (0 : Fin 6)) := by decide

private theorem checkD_HKT_0_2 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (0 : Fin 6) (2 : Fin 6)) y) k) (0 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (0 : Fin 6) (2 : Fin 6)) y) k) (0 : Fin 6)) t) (0 : Fin 6)) := by decide

private theorem checkD_HKT_0_3 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (0 : Fin 6) (3 : Fin 6)) y) k) (0 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (0 : Fin 6) (3 : Fin 6)) y) k) (0 : Fin 6)) t) (0 : Fin 6)) := by decide

private theorem checkD_HKT_0_4 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (0 : Fin 6) (4 : Fin 6)) y) k) (0 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (0 : Fin 6) (4 : Fin 6)) y) k) (0 : Fin 6)) t) (0 : Fin 6)) := by decide

private theorem checkD_HKT_0_5 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (0 : Fin 6) (5 : Fin 6)) y) k) (0 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (0 : Fin 6) (5 : Fin 6)) y) k) (0 : Fin 6)) t) (0 : Fin 6)) := by decide

private theorem checkD_HKT_1_0 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (1 : Fin 6) (0 : Fin 6)) y) k) (1 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (1 : Fin 6) (0 : Fin 6)) y) k) (1 : Fin 6)) t) (1 : Fin 6)) := by decide

private theorem checkD_HKT_1_1 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (1 : Fin 6) (1 : Fin 6)) y) k) (1 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (1 : Fin 6) (1 : Fin 6)) y) k) (1 : Fin 6)) t) (1 : Fin 6)) := by decide

private theorem checkD_HKT_1_2 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (1 : Fin 6) (2 : Fin 6)) y) k) (1 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (1 : Fin 6) (2 : Fin 6)) y) k) (1 : Fin 6)) t) (1 : Fin 6)) := by decide

private theorem checkD_HKT_1_3 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (1 : Fin 6) (3 : Fin 6)) y) k) (1 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (1 : Fin 6) (3 : Fin 6)) y) k) (1 : Fin 6)) t) (1 : Fin 6)) := by decide

private theorem checkD_HKT_1_4 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (1 : Fin 6) (4 : Fin 6)) y) k) (1 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (1 : Fin 6) (4 : Fin 6)) y) k) (1 : Fin 6)) t) (1 : Fin 6)) := by decide

private theorem checkD_HKT_1_5 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (1 : Fin 6) (5 : Fin 6)) y) k) (1 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (1 : Fin 6) (5 : Fin 6)) y) k) (1 : Fin 6)) t) (1 : Fin 6)) := by decide

private theorem checkD_HKT_2_0 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (2 : Fin 6) (0 : Fin 6)) y) k) (2 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (2 : Fin 6) (0 : Fin 6)) y) k) (2 : Fin 6)) t) (2 : Fin 6)) := by decide

private theorem checkD_HKT_2_1 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (2 : Fin 6) (1 : Fin 6)) y) k) (2 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (2 : Fin 6) (1 : Fin 6)) y) k) (2 : Fin 6)) t) (2 : Fin 6)) := by decide

private theorem checkD_HKT_2_2 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (2 : Fin 6) (2 : Fin 6)) y) k) (2 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (2 : Fin 6) (2 : Fin 6)) y) k) (2 : Fin 6)) t) (2 : Fin 6)) := by decide

private theorem checkD_HKT_2_3 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (2 : Fin 6) (3 : Fin 6)) y) k) (2 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (2 : Fin 6) (3 : Fin 6)) y) k) (2 : Fin 6)) t) (2 : Fin 6)) := by decide

private theorem checkD_HKT_2_4 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (2 : Fin 6) (4 : Fin 6)) y) k) (2 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (2 : Fin 6) (4 : Fin 6)) y) k) (2 : Fin 6)) t) (2 : Fin 6)) := by decide

private theorem checkD_HKT_2_5 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (2 : Fin 6) (5 : Fin 6)) y) k) (2 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (2 : Fin 6) (5 : Fin 6)) y) k) (2 : Fin 6)) t) (2 : Fin 6)) := by decide

private theorem checkD_HKT_3_0 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (3 : Fin 6) (0 : Fin 6)) y) k) (3 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (3 : Fin 6) (0 : Fin 6)) y) k) (3 : Fin 6)) t) (3 : Fin 6)) := by decide

private theorem checkD_HKT_3_1 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (3 : Fin 6) (1 : Fin 6)) y) k) (3 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (3 : Fin 6) (1 : Fin 6)) y) k) (3 : Fin 6)) t) (3 : Fin 6)) := by decide

private theorem checkD_HKT_3_2 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (3 : Fin 6) (2 : Fin 6)) y) k) (3 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (3 : Fin 6) (2 : Fin 6)) y) k) (3 : Fin 6)) t) (3 : Fin 6)) := by decide

private theorem checkD_HKT_3_3 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (3 : Fin 6) (3 : Fin 6)) y) k) (3 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (3 : Fin 6) (3 : Fin 6)) y) k) (3 : Fin 6)) t) (3 : Fin 6)) := by decide

private theorem checkD_HKT_3_4 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (3 : Fin 6) (4 : Fin 6)) y) k) (3 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (3 : Fin 6) (4 : Fin 6)) y) k) (3 : Fin 6)) t) (3 : Fin 6)) := by decide

private theorem checkD_HKT_3_5 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (3 : Fin 6) (5 : Fin 6)) y) k) (3 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (3 : Fin 6) (5 : Fin 6)) y) k) (3 : Fin 6)) t) (3 : Fin 6)) := by decide

private theorem checkD_HKT_4_0 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (4 : Fin 6) (0 : Fin 6)) y) k) (4 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (4 : Fin 6) (0 : Fin 6)) y) k) (4 : Fin 6)) t) (4 : Fin 6)) := by decide

private theorem checkD_HKT_4_1 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (4 : Fin 6) (1 : Fin 6)) y) k) (4 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (4 : Fin 6) (1 : Fin 6)) y) k) (4 : Fin 6)) t) (4 : Fin 6)) := by decide

private theorem checkD_HKT_4_2 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (4 : Fin 6) (2 : Fin 6)) y) k) (4 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (4 : Fin 6) (2 : Fin 6)) y) k) (4 : Fin 6)) t) (4 : Fin 6)) := by decide

private theorem checkD_HKT_4_3 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (4 : Fin 6) (3 : Fin 6)) y) k) (4 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (4 : Fin 6) (3 : Fin 6)) y) k) (4 : Fin 6)) t) (4 : Fin 6)) := by decide

private theorem checkD_HKT_4_4 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (4 : Fin 6) (4 : Fin 6)) y) k) (4 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (4 : Fin 6) (4 : Fin 6)) y) k) (4 : Fin 6)) t) (4 : Fin 6)) := by decide

private theorem checkD_HKT_4_5 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (4 : Fin 6) (5 : Fin 6)) y) k) (4 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (4 : Fin 6) (5 : Fin 6)) y) k) (4 : Fin 6)) t) (4 : Fin 6)) := by decide

private theorem checkD_HKT_5_0 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (5 : Fin 6) (0 : Fin 6)) y) k) (5 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (5 : Fin 6) (0 : Fin 6)) y) k) (5 : Fin 6)) t) (5 : Fin 6)) := by decide

private theorem checkD_HKT_5_1 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (5 : Fin 6) (1 : Fin 6)) y) k) (5 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (5 : Fin 6) (1 : Fin 6)) y) k) (5 : Fin 6)) t) (5 : Fin 6)) := by decide

private theorem checkD_HKT_5_2 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (5 : Fin 6) (2 : Fin 6)) y) k) (5 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (5 : Fin 6) (2 : Fin 6)) y) k) (5 : Fin 6)) t) (5 : Fin 6)) := by decide

private theorem checkD_HKT_5_3 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (5 : Fin 6) (3 : Fin 6)) y) k) (5 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (5 : Fin 6) (3 : Fin 6)) y) k) (5 : Fin 6)) t) (5 : Fin 6)) := by decide

private theorem checkD_HKT_5_4 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (5 : Fin 6) (4 : Fin 6)) y) k) (5 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (5 : Fin 6) (4 : Fin 6)) y) k) (5 : Fin 6)) t) (5 : Fin 6)) := by decide

private theorem checkD_HKT_5_5 :
    ∀ y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul (5 : Fin 6) (5 : Fin 6)) y) k) (5 : Fin 6)) t) y) = (mul (mul (mul (mul (mul (mul (5 : Fin 6) (5 : Fin 6)) y) k) (5 : Fin 6)) t) (5 : Fin 6)) := by decide

private theorem checkD_HKT :
    ∀ x h y k t : Fin 6,
      (mul (mul (mul (mul (mul (mul x h) y) k) x) t) y) = (mul (mul (mul (mul (mul (mul x h) y) k) x) t) x) := by
  intro x h y k t
  have cases_x : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
    revert x
    decide
  have cases_h : h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 := by
    revert h
    decide
  rcases cases_x with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases cases_h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkD_HKT_0_0 y k t
  · exact checkD_HKT_0_1 y k t
  · exact checkD_HKT_0_2 y k t
  · exact checkD_HKT_0_3 y k t
  · exact checkD_HKT_0_4 y k t
  · exact checkD_HKT_0_5 y k t
  · exact checkD_HKT_1_0 y k t
  · exact checkD_HKT_1_1 y k t
  · exact checkD_HKT_1_2 y k t
  · exact checkD_HKT_1_3 y k t
  · exact checkD_HKT_1_4 y k t
  · exact checkD_HKT_1_5 y k t
  · exact checkD_HKT_2_0 y k t
  · exact checkD_HKT_2_1 y k t
  · exact checkD_HKT_2_2 y k t
  · exact checkD_HKT_2_3 y k t
  · exact checkD_HKT_2_4 y k t
  · exact checkD_HKT_2_5 y k t
  · exact checkD_HKT_3_0 y k t
  · exact checkD_HKT_3_1 y k t
  · exact checkD_HKT_3_2 y k t
  · exact checkD_HKT_3_3 y k t
  · exact checkD_HKT_3_4 y k t
  · exact checkD_HKT_3_5 y k t
  · exact checkD_HKT_4_0 y k t
  · exact checkD_HKT_4_1 y k t
  · exact checkD_HKT_4_2 y k t
  · exact checkD_HKT_4_3 y k t
  · exact checkD_HKT_4_4 y k t
  · exact checkD_HKT_4_5 y k t
  · exact checkD_HKT_5_0 y k t
  · exact checkD_HKT_5_1 y k t
  · exact checkD_HKT_5_2 y k t
  · exact checkD_HKT_5_3 y k t
  · exact checkD_HKT_5_4 y k t
  · exact checkD_HKT_5_5 y k t

private theorem validD_HKT : (lawD_HKT).SatisfiedBy table.semigroup := by
  intro valuation
  exact checkD_HKT (valuation 0) (valuation 2) (valuation 1) (valuation 3) (valuation 4)

theorem models : Models table.semigroup basis := by
  intro e member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact validA_empty
  · exact validA_H
  · exact validB_empty
  · exact validB_K
  · exact validB_H
  · exact validB_HK
  · exact validC_empty
  · exact validC_K
  · exact validC_H
  · exact validC_HK
  · exact validD_empty
  · exact validD_T
  · exact validD_K
  · exact validD_KT
  · exact validD_H
  · exact validD_HT
  · exact validD_HK
  · exact validD_HKT

theorem zero_absorbs (a : Fin 6) : mul 0 a = 0 := by simp [mul]
theorem two_absorbs (a : Fin 6) : mul 2 a = 2 := by simp [mul]
theorem five_absorbs (a : Fin 6) : mul 5 a = 5 := by simp [mul]

end SemigroupBasis.CoRoots.Order6SporadicSection27.F10

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.table
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.table_literal_exact
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.models
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.zero_absorbs
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.two_absorbs
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.five_absorbs
