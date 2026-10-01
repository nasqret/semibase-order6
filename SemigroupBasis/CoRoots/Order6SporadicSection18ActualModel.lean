import SemigroupBasis.CoRoots.Order6SporadicSection18Basis
import SemigroupBasis.FiniteReflection

/-! Actual S6_3841 table and full soundness of the exact published basis.
The two local units are zero-based elements4 and5, not a global identity. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Actual
open SemigroupBasis

def tableMul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 1, 5 => 1
  | 2, 5 => 2
  | 3, 2 => 1
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 4 => 4
  | 5, 1 => 1
  | 5, 3 => 3
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := tableMul
  assoc := by decide

theorem table_literal_exact :
  (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (tableMul a b).val)) =
    [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2], [0, 0, 1, 0, 3, 0], [0, 0, 2, 0, 4, 0], [0, 1, 0, 3, 0, 5]] := by decide

private theorem casesFin6 (x : Fin 6) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
  revert x
  decide

private theorem check_lawPower :
    ∀ a0 : Fin 6,
      (tableMul (tableMul a0 a0) a0) = (tableMul a0 a0) := by decide

theorem lawPower_valid : lawPower.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_lawPower (valuation 0)

private theorem check_lawLeft :
    ∀ a0 a1 : Fin 6,
      (tableMul (tableMul (tableMul a0 a0) a1) a0) = (tableMul (tableMul a0 a1) a0) := by decide

theorem lawLeft_valid : lawLeft.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_lawLeft (valuation 0) (valuation 1)

private theorem check_lawRight :
    ∀ a0 a1 : Fin 6,
      (tableMul (tableMul (tableMul a0 a1) a0) a0) = (tableMul (tableMul a0 a1) a0) := by decide

theorem lawRight_valid : lawRight.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_lawRight (valuation 0) (valuation 1)

private theorem check_lawSquare :
    ∀ a0 a1 : Fin 6,
      (tableMul (tableMul (tableMul a0 a0) a1) a1) = (tableMul (tableMul (tableMul a1 a1) a0) a0) := by decide

theorem lawSquare_valid : lawSquare.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_lawSquare (valuation 0) (valuation 1)

private theorem check_law04 :
    ∀ a0 a1 a2 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul a0 a1) a1) a2) a0) = (tableMul (tableMul (tableMul (tableMul a0 a2) a1) a1) a0) := by decide

theorem law04_valid : law04.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law04 (valuation 0) (valuation 1) (valuation 2)

private theorem check_law05 :
    ∀ a0 a1 a2 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul a0 a1) a0) a2) a0) = (tableMul (tableMul (tableMul (tableMul a0 a2) a0) a1) a0) := by decide

theorem law05_valid : law05.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law05 (valuation 0) (valuation 1) (valuation 2)

private theorem check_law06 :
    ∀ a0 a1 : Fin 6,
      (tableMul (tableMul (tableMul a0 a1) a0) a1) = (tableMul (tableMul (tableMul (tableMul a0 a1) a0) a1) a0) := by decide

theorem law06_valid : law06.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law06 (valuation 0) (valuation 1)

private theorem check_law07 :
    ∀ a0 a1 a2 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul a0 a1) a0) a2) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul a0 a1) a0) a2) a1) a0) := by decide

theorem law07_valid : law07.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law07 (valuation 0) (valuation 1) (valuation 2)

private theorem check_law08 :
    ∀ a0 a1 a2 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a0) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a0) a1) a0) := by decide

theorem law08_valid : law08.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law08 (valuation 0) (valuation 1) (valuation 2)

private theorem check_law09_0 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) a1) a2) (0 : Fin 6)) a3) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) a1) a2) (0 : Fin 6)) a3) a1) (0 : Fin 6)) := by decide

private theorem check_law09_1 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) a1) a2) (1 : Fin 6)) a3) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) a1) a2) (1 : Fin 6)) a3) a1) (1 : Fin 6)) := by decide

private theorem check_law09_2 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) a1) a2) (2 : Fin 6)) a3) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) a1) a2) (2 : Fin 6)) a3) a1) (2 : Fin 6)) := by decide

private theorem check_law09_3 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) a1) a2) (3 : Fin 6)) a3) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) a1) a2) (3 : Fin 6)) a3) a1) (3 : Fin 6)) := by decide

private theorem check_law09_4 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) a1) a2) (4 : Fin 6)) a3) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) a1) a2) (4 : Fin 6)) a3) a1) (4 : Fin 6)) := by decide

private theorem check_law09_5 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) a1) a2) (5 : Fin 6)) a3) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) a1) a2) (5 : Fin 6)) a3) a1) (5 : Fin 6)) := by decide

private theorem check_law09 :
    ∀ a0 a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a0) a3) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a0) a3) a1) a0) := by
  intro a0 a1 a2 a3
  have split_a0 := casesFin6 a0
  rcases split_a0 with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    exact check_law09_0 a1 a2 a3
  ·
    exact check_law09_1 a1 a2 a3
  ·
    exact check_law09_2 a1 a2 a3
  ·
    exact check_law09_3 a1 a2 a3
  ·
    exact check_law09_4 a1 a2 a3
  ·
    exact check_law09_5 a1 a2 a3

theorem law09_valid : law09.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law09 (valuation 0) (valuation 1) (valuation 2) (valuation 3)

private theorem check_law10 :
    ∀ a0 a1 a2 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a0) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a0) a2) a0) := by decide

theorem law10_valid : law10.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law10 (valuation 0) (valuation 1) (valuation 2)

private theorem check_law11_0 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) a1) a2) (0 : Fin 6)) a3) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) a1) a2) (0 : Fin 6)) a3) a2) (0 : Fin 6)) := by decide

private theorem check_law11_1 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) a1) a2) (1 : Fin 6)) a3) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) a1) a2) (1 : Fin 6)) a3) a2) (1 : Fin 6)) := by decide

private theorem check_law11_2 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) a1) a2) (2 : Fin 6)) a3) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) a1) a2) (2 : Fin 6)) a3) a2) (2 : Fin 6)) := by decide

private theorem check_law11_3 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) a1) a2) (3 : Fin 6)) a3) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) a1) a2) (3 : Fin 6)) a3) a2) (3 : Fin 6)) := by decide

private theorem check_law11_4 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) a1) a2) (4 : Fin 6)) a3) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) a1) a2) (4 : Fin 6)) a3) a2) (4 : Fin 6)) := by decide

private theorem check_law11_5 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) a1) a2) (5 : Fin 6)) a3) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) a1) a2) (5 : Fin 6)) a3) a2) (5 : Fin 6)) := by decide

private theorem check_law11 :
    ∀ a0 a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a0) a3) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a0) a3) a2) a0) := by
  intro a0 a1 a2 a3
  have split_a0 := casesFin6 a0
  rcases split_a0 with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    exact check_law11_0 a1 a2 a3
  ·
    exact check_law11_1 a1 a2 a3
  ·
    exact check_law11_2 a1 a2 a3
  ·
    exact check_law11_3 a1 a2 a3
  ·
    exact check_law11_4 a1 a2 a3
  ·
    exact check_law11_5 a1 a2 a3

theorem law11_valid : law11.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law11 (valuation 0) (valuation 1) (valuation 2) (valuation 3)

private theorem check_law12_0 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) a1) a2) a3) (0 : Fin 6)) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) a1) a2) a3) (0 : Fin 6)) a2) (0 : Fin 6)) := by decide

private theorem check_law12_1 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) a1) a2) a3) (1 : Fin 6)) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) a1) a2) a3) (1 : Fin 6)) a2) (1 : Fin 6)) := by decide

private theorem check_law12_2 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) a1) a2) a3) (2 : Fin 6)) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) a1) a2) a3) (2 : Fin 6)) a2) (2 : Fin 6)) := by decide

private theorem check_law12_3 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) a1) a2) a3) (3 : Fin 6)) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) a1) a2) a3) (3 : Fin 6)) a2) (3 : Fin 6)) := by decide

private theorem check_law12_4 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) a1) a2) a3) (4 : Fin 6)) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) a1) a2) a3) (4 : Fin 6)) a2) (4 : Fin 6)) := by decide

private theorem check_law12_5 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) a1) a2) a3) (5 : Fin 6)) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) a1) a2) a3) (5 : Fin 6)) a2) (5 : Fin 6)) := by decide

private theorem check_law12 :
    ∀ a0 a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a3) a0) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a3) a0) a2) a0) := by
  intro a0 a1 a2 a3
  have split_a0 := casesFin6 a0
  rcases split_a0 with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    exact check_law12_0 a1 a2 a3
  ·
    exact check_law12_1 a1 a2 a3
  ·
    exact check_law12_2 a1 a2 a3
  ·
    exact check_law12_3 a1 a2 a3
  ·
    exact check_law12_4 a1 a2 a3
  ·
    exact check_law12_5 a1 a2 a3

theorem law12_valid : law12.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law12 (valuation 0) (valuation 1) (valuation 2) (valuation 3)

private theorem check_law13_0_0 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) (0 : Fin 6)) := by decide

private theorem check_law13_0_1 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (1 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (1 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) (0 : Fin 6)) := by decide

private theorem check_law13_0_2 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (2 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (2 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) (0 : Fin 6)) := by decide

private theorem check_law13_0_3 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (3 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (3 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) (0 : Fin 6)) := by decide

private theorem check_law13_0_4 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (4 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (4 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) (0 : Fin 6)) := by decide

private theorem check_law13_0_5 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (5 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (5 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) (0 : Fin 6)) := by decide

private theorem check_law13_1_0 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (0 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (0 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) (1 : Fin 6)) := by decide

private theorem check_law13_1_1 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) (1 : Fin 6)) := by decide

private theorem check_law13_1_2 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (2 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (2 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) (1 : Fin 6)) := by decide

private theorem check_law13_1_3 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (3 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (3 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) (1 : Fin 6)) := by decide

private theorem check_law13_1_4 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (4 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (4 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) (1 : Fin 6)) := by decide

private theorem check_law13_1_5 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (5 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (5 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) (1 : Fin 6)) := by decide

private theorem check_law13_2_0 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (0 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (0 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) (2 : Fin 6)) := by decide

private theorem check_law13_2_1 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (1 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (1 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) (2 : Fin 6)) := by decide

private theorem check_law13_2_2 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) (2 : Fin 6)) := by decide

private theorem check_law13_2_3 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (3 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (3 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) (2 : Fin 6)) := by decide

private theorem check_law13_2_4 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (4 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (4 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) (2 : Fin 6)) := by decide

private theorem check_law13_2_5 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (5 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (5 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) (2 : Fin 6)) := by decide

private theorem check_law13_3_0 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (0 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (0 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) (3 : Fin 6)) := by decide

private theorem check_law13_3_1 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (1 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (1 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) (3 : Fin 6)) := by decide

private theorem check_law13_3_2 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (2 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (2 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) (3 : Fin 6)) := by decide

private theorem check_law13_3_3 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) (3 : Fin 6)) := by decide

private theorem check_law13_3_4 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (4 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (4 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) (3 : Fin 6)) := by decide

private theorem check_law13_3_5 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (5 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (5 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) (3 : Fin 6)) := by decide

private theorem check_law13_4_0 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (0 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (0 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) (4 : Fin 6)) := by decide

private theorem check_law13_4_1 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (1 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (1 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) (4 : Fin 6)) := by decide

private theorem check_law13_4_2 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (2 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (2 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) (4 : Fin 6)) := by decide

private theorem check_law13_4_3 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (3 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (3 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) (4 : Fin 6)) := by decide

private theorem check_law13_4_4 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) (4 : Fin 6)) := by decide

private theorem check_law13_4_5 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (5 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (5 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) (4 : Fin 6)) := by decide

private theorem check_law13_5_0 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (0 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (0 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) (5 : Fin 6)) := by decide

private theorem check_law13_5_1 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (1 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (1 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) (5 : Fin 6)) := by decide

private theorem check_law13_5_2 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (2 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (2 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) (5 : Fin 6)) := by decide

private theorem check_law13_5_3 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (3 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (3 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) (5 : Fin 6)) := by decide

private theorem check_law13_5_4 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (4 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (4 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) (5 : Fin 6)) := by decide

private theorem check_law13_5_5 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) (5 : Fin 6)) := by decide

private theorem check_law13 :
    ∀ a0 a1 a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a3) a0) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a3) a0) a4) a2) a0) := by
  intro a0 a1 a2 a3 a4
  have split_a0 := casesFin6 a0
  rcases split_a0 with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    have split_a1 := casesFin6 a1
    rcases split_a1 with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      exact check_law13_0_0 a2 a3 a4
    ·
      exact check_law13_0_1 a2 a3 a4
    ·
      exact check_law13_0_2 a2 a3 a4
    ·
      exact check_law13_0_3 a2 a3 a4
    ·
      exact check_law13_0_4 a2 a3 a4
    ·
      exact check_law13_0_5 a2 a3 a4
  ·
    have split_a1 := casesFin6 a1
    rcases split_a1 with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      exact check_law13_1_0 a2 a3 a4
    ·
      exact check_law13_1_1 a2 a3 a4
    ·
      exact check_law13_1_2 a2 a3 a4
    ·
      exact check_law13_1_3 a2 a3 a4
    ·
      exact check_law13_1_4 a2 a3 a4
    ·
      exact check_law13_1_5 a2 a3 a4
  ·
    have split_a1 := casesFin6 a1
    rcases split_a1 with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      exact check_law13_2_0 a2 a3 a4
    ·
      exact check_law13_2_1 a2 a3 a4
    ·
      exact check_law13_2_2 a2 a3 a4
    ·
      exact check_law13_2_3 a2 a3 a4
    ·
      exact check_law13_2_4 a2 a3 a4
    ·
      exact check_law13_2_5 a2 a3 a4
  ·
    have split_a1 := casesFin6 a1
    rcases split_a1 with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      exact check_law13_3_0 a2 a3 a4
    ·
      exact check_law13_3_1 a2 a3 a4
    ·
      exact check_law13_3_2 a2 a3 a4
    ·
      exact check_law13_3_3 a2 a3 a4
    ·
      exact check_law13_3_4 a2 a3 a4
    ·
      exact check_law13_3_5 a2 a3 a4
  ·
    have split_a1 := casesFin6 a1
    rcases split_a1 with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      exact check_law13_4_0 a2 a3 a4
    ·
      exact check_law13_4_1 a2 a3 a4
    ·
      exact check_law13_4_2 a2 a3 a4
    ·
      exact check_law13_4_3 a2 a3 a4
    ·
      exact check_law13_4_4 a2 a3 a4
    ·
      exact check_law13_4_5 a2 a3 a4
  ·
    have split_a1 := casesFin6 a1
    rcases split_a1 with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      exact check_law13_5_0 a2 a3 a4
    ·
      exact check_law13_5_1 a2 a3 a4
    ·
      exact check_law13_5_2 a2 a3 a4
    ·
      exact check_law13_5_3 a2 a3 a4
    ·
      exact check_law13_5_4 a2 a3 a4
    ·
      exact check_law13_5_5 a2 a3 a4

theorem law13_valid : law13.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law13 (valuation 0) (valuation 1) (valuation 2) (valuation 3) (valuation 4)

private theorem check_law14 :
    ∀ a0 a1 : Fin 6,
      (tableMul (tableMul (tableMul a0 a1) a0) a1) = (tableMul (tableMul (tableMul (tableMul a1 a0) a1) a0) a1) := by decide

theorem law14_valid : law14.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law14 (valuation 0) (valuation 1)

private theorem check_law15 :
    ∀ a0 a1 a2 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul a0 a1) a0) a2) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul a1 a0) a1) a0) a2) a1) := by decide

theorem law15_valid : law15.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law15 (valuation 0) (valuation 1) (valuation 2)

private theorem check_law16 :
    ∀ a0 a1 a2 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a0) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul a1 a0) a1) a2) a0) a1) := by decide

theorem law16_valid : law16.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law16 (valuation 0) (valuation 1) (valuation 2)

private theorem check_law17_0 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) a1) a2) (0 : Fin 6)) a3) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a1 (0 : Fin 6)) a1) a2) (0 : Fin 6)) a3) a1) := by decide

private theorem check_law17_1 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) a1) a2) (1 : Fin 6)) a3) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a1 (1 : Fin 6)) a1) a2) (1 : Fin 6)) a3) a1) := by decide

private theorem check_law17_2 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) a1) a2) (2 : Fin 6)) a3) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a1 (2 : Fin 6)) a1) a2) (2 : Fin 6)) a3) a1) := by decide

private theorem check_law17_3 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) a1) a2) (3 : Fin 6)) a3) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a1 (3 : Fin 6)) a1) a2) (3 : Fin 6)) a3) a1) := by decide

private theorem check_law17_4 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) a1) a2) (4 : Fin 6)) a3) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a1 (4 : Fin 6)) a1) a2) (4 : Fin 6)) a3) a1) := by decide

private theorem check_law17_5 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) a1) a2) (5 : Fin 6)) a3) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a1 (5 : Fin 6)) a1) a2) (5 : Fin 6)) a3) a1) := by decide

private theorem check_law17 :
    ∀ a0 a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a0) a3) a1) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a1 a0) a1) a2) a0) a3) a1) := by
  intro a0 a1 a2 a3
  have split_a0 := casesFin6 a0
  rcases split_a0 with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    exact check_law17_0 a1 a2 a3
  ·
    exact check_law17_1 a1 a2 a3
  ·
    exact check_law17_2 a1 a2 a3
  ·
    exact check_law17_3 a1 a2 a3
  ·
    exact check_law17_4 a1 a2 a3
  ·
    exact check_law17_5 a1 a2 a3

theorem law17_valid : law17.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law17 (valuation 0) (valuation 1) (valuation 2) (valuation 3)

private theorem check_law18 :
    ∀ a0 a1 a2 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a0) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul a2 a0) a1) a2) a0) a2) := by decide

theorem law18_valid : law18.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law18 (valuation 0) (valuation 1) (valuation 2)

private theorem check_law19_0 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) a1) a2) (0 : Fin 6)) a3) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (0 : Fin 6)) a1) a2) (0 : Fin 6)) a3) a2) := by decide

private theorem check_law19_1 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) a1) a2) (1 : Fin 6)) a3) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (1 : Fin 6)) a1) a2) (1 : Fin 6)) a3) a2) := by decide

private theorem check_law19_2 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) a1) a2) (2 : Fin 6)) a3) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (2 : Fin 6)) a1) a2) (2 : Fin 6)) a3) a2) := by decide

private theorem check_law19_3 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) a1) a2) (3 : Fin 6)) a3) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (3 : Fin 6)) a1) a2) (3 : Fin 6)) a3) a2) := by decide

private theorem check_law19_4 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) a1) a2) (4 : Fin 6)) a3) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (4 : Fin 6)) a1) a2) (4 : Fin 6)) a3) a2) := by decide

private theorem check_law19_5 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) a1) a2) (5 : Fin 6)) a3) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (5 : Fin 6)) a1) a2) (5 : Fin 6)) a3) a2) := by decide

private theorem check_law19 :
    ∀ a0 a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a0) a3) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 a0) a1) a2) a0) a3) a2) := by
  intro a0 a1 a2 a3
  have split_a0 := casesFin6 a0
  rcases split_a0 with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    exact check_law19_0 a1 a2 a3
  ·
    exact check_law19_1 a1 a2 a3
  ·
    exact check_law19_2 a1 a2 a3
  ·
    exact check_law19_3 a1 a2 a3
  ·
    exact check_law19_4 a1 a2 a3
  ·
    exact check_law19_5 a1 a2 a3

theorem law19_valid : law19.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law19 (valuation 0) (valuation 1) (valuation 2) (valuation 3)

private theorem check_law20_0 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) a1) a2) a3) (0 : Fin 6)) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (0 : Fin 6)) a1) a2) a3) (0 : Fin 6)) a2) := by decide

private theorem check_law20_1 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) a1) a2) a3) (1 : Fin 6)) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (1 : Fin 6)) a1) a2) a3) (1 : Fin 6)) a2) := by decide

private theorem check_law20_2 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) a1) a2) a3) (2 : Fin 6)) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (2 : Fin 6)) a1) a2) a3) (2 : Fin 6)) a2) := by decide

private theorem check_law20_3 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) a1) a2) a3) (3 : Fin 6)) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (3 : Fin 6)) a1) a2) a3) (3 : Fin 6)) a2) := by decide

private theorem check_law20_4 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) a1) a2) a3) (4 : Fin 6)) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (4 : Fin 6)) a1) a2) a3) (4 : Fin 6)) a2) := by decide

private theorem check_law20_5 :
    ∀ a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) a1) a2) a3) (5 : Fin 6)) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (5 : Fin 6)) a1) a2) a3) (5 : Fin 6)) a2) := by decide

private theorem check_law20 :
    ∀ a0 a1 a2 a3 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a3) a0) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 a0) a1) a2) a3) a0) a2) := by
  intro a0 a1 a2 a3
  have split_a0 := casesFin6 a0
  rcases split_a0 with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    exact check_law20_0 a1 a2 a3
  ·
    exact check_law20_1 a1 a2 a3
  ·
    exact check_law20_2 a1 a2 a3
  ·
    exact check_law20_3 a1 a2 a3
  ·
    exact check_law20_4 a1 a2 a3
  ·
    exact check_law20_5 a1 a2 a3

theorem law20_valid : law20.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law20 (valuation 0) (valuation 1) (valuation 2) (valuation 3)

private theorem check_law21_0_0 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (0 : Fin 6)) (0 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) := by decide

private theorem check_law21_0_1 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (1 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (0 : Fin 6)) (1 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) := by decide

private theorem check_law21_0_2 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (2 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (0 : Fin 6)) (2 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) := by decide

private theorem check_law21_0_3 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (3 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (0 : Fin 6)) (3 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) := by decide

private theorem check_law21_0_4 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (4 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (0 : Fin 6)) (4 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) := by decide

private theorem check_law21_0_5 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (5 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (0 : Fin 6)) (5 : Fin 6)) a2) a3) (0 : Fin 6)) a4) a2) := by decide

private theorem check_law21_1_0 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (0 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (1 : Fin 6)) (0 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) := by decide

private theorem check_law21_1_1 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (1 : Fin 6)) (1 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) := by decide

private theorem check_law21_1_2 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (2 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (1 : Fin 6)) (2 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) := by decide

private theorem check_law21_1_3 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (3 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (1 : Fin 6)) (3 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) := by decide

private theorem check_law21_1_4 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (4 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (1 : Fin 6)) (4 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) := by decide

private theorem check_law21_1_5 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (5 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (1 : Fin 6)) (5 : Fin 6)) a2) a3) (1 : Fin 6)) a4) a2) := by decide

private theorem check_law21_2_0 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (0 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (2 : Fin 6)) (0 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) := by decide

private theorem check_law21_2_1 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (1 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (2 : Fin 6)) (1 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) := by decide

private theorem check_law21_2_2 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (2 : Fin 6)) (2 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) := by decide

private theorem check_law21_2_3 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (3 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (2 : Fin 6)) (3 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) := by decide

private theorem check_law21_2_4 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (4 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (2 : Fin 6)) (4 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) := by decide

private theorem check_law21_2_5 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (5 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (2 : Fin 6)) (5 : Fin 6)) a2) a3) (2 : Fin 6)) a4) a2) := by decide

private theorem check_law21_3_0 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (0 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (3 : Fin 6)) (0 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) := by decide

private theorem check_law21_3_1 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (1 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (3 : Fin 6)) (1 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) := by decide

private theorem check_law21_3_2 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (2 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (3 : Fin 6)) (2 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) := by decide

private theorem check_law21_3_3 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (3 : Fin 6)) (3 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) := by decide

private theorem check_law21_3_4 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (4 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (3 : Fin 6)) (4 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) := by decide

private theorem check_law21_3_5 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (5 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (3 : Fin 6)) (5 : Fin 6)) a2) a3) (3 : Fin 6)) a4) a2) := by decide

private theorem check_law21_4_0 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (0 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (4 : Fin 6)) (0 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) := by decide

private theorem check_law21_4_1 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (1 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (4 : Fin 6)) (1 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) := by decide

private theorem check_law21_4_2 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (2 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (4 : Fin 6)) (2 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) := by decide

private theorem check_law21_4_3 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (3 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (4 : Fin 6)) (3 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) := by decide

private theorem check_law21_4_4 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (4 : Fin 6)) (4 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) := by decide

private theorem check_law21_4_5 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (5 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (4 : Fin 6)) (5 : Fin 6)) a2) a3) (4 : Fin 6)) a4) a2) := by decide

private theorem check_law21_5_0 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (0 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (5 : Fin 6)) (0 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) := by decide

private theorem check_law21_5_1 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (1 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (5 : Fin 6)) (1 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) := by decide

private theorem check_law21_5_2 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (2 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (5 : Fin 6)) (2 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) := by decide

private theorem check_law21_5_3 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (3 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (5 : Fin 6)) (3 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) := by decide

private theorem check_law21_5_4 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (4 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (5 : Fin 6)) (4 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) := by decide

private theorem check_law21_5_5 :
    ∀ a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 (5 : Fin 6)) (5 : Fin 6)) a2) a3) (5 : Fin 6)) a4) a2) := by decide

private theorem check_law21 :
    ∀ a0 a1 a2 a3 a4 : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a0 a1) a2) a3) a0) a4) a2) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul a2 a0) a1) a2) a3) a0) a4) a2) := by
  intro a0 a1 a2 a3 a4
  have split_a0 := casesFin6 a0
  rcases split_a0 with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    have split_a1 := casesFin6 a1
    rcases split_a1 with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      exact check_law21_0_0 a2 a3 a4
    ·
      exact check_law21_0_1 a2 a3 a4
    ·
      exact check_law21_0_2 a2 a3 a4
    ·
      exact check_law21_0_3 a2 a3 a4
    ·
      exact check_law21_0_4 a2 a3 a4
    ·
      exact check_law21_0_5 a2 a3 a4
  ·
    have split_a1 := casesFin6 a1
    rcases split_a1 with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      exact check_law21_1_0 a2 a3 a4
    ·
      exact check_law21_1_1 a2 a3 a4
    ·
      exact check_law21_1_2 a2 a3 a4
    ·
      exact check_law21_1_3 a2 a3 a4
    ·
      exact check_law21_1_4 a2 a3 a4
    ·
      exact check_law21_1_5 a2 a3 a4
  ·
    have split_a1 := casesFin6 a1
    rcases split_a1 with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      exact check_law21_2_0 a2 a3 a4
    ·
      exact check_law21_2_1 a2 a3 a4
    ·
      exact check_law21_2_2 a2 a3 a4
    ·
      exact check_law21_2_3 a2 a3 a4
    ·
      exact check_law21_2_4 a2 a3 a4
    ·
      exact check_law21_2_5 a2 a3 a4
  ·
    have split_a1 := casesFin6 a1
    rcases split_a1 with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      exact check_law21_3_0 a2 a3 a4
    ·
      exact check_law21_3_1 a2 a3 a4
    ·
      exact check_law21_3_2 a2 a3 a4
    ·
      exact check_law21_3_3 a2 a3 a4
    ·
      exact check_law21_3_4 a2 a3 a4
    ·
      exact check_law21_3_5 a2 a3 a4
  ·
    have split_a1 := casesFin6 a1
    rcases split_a1 with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      exact check_law21_4_0 a2 a3 a4
    ·
      exact check_law21_4_1 a2 a3 a4
    ·
      exact check_law21_4_2 a2 a3 a4
    ·
      exact check_law21_4_3 a2 a3 a4
    ·
      exact check_law21_4_4 a2 a3 a4
    ·
      exact check_law21_4_5 a2 a3 a4
  ·
    have split_a1 := casesFin6 a1
    rcases split_a1 with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      exact check_law21_5_0 a2 a3 a4
    ·
      exact check_law21_5_1 a2 a3 a4
    ·
      exact check_law21_5_2 a2 a3 a4
    ·
      exact check_law21_5_3 a2 a3 a4
    ·
      exact check_law21_5_4 a2 a3 a4
    ·
      exact check_law21_5_5 a2 a3 a4

theorem law21_valid : law21.SatisfiedBy table.semigroup := by
  intro valuation
  exact check_law21 (valuation 0) (valuation 1) (valuation 2) (valuation 3) (valuation 4)

theorem models : Models table.semigroup basis := by
  intro e member
  simp only [basis,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lawPower_valid
  · exact lawLeft_valid
  · exact lawRight_valid
  · exact lawSquare_valid
  · exact law04_valid
  · exact law05_valid
  · exact law06_valid
  · exact law07_valid
  · exact law08_valid
  · exact law09_valid
  · exact law10_valid
  · exact law11_valid
  · exact law12_valid
  · exact law13_valid
  · exact law14_valid
  · exact law15_valid
  · exact law16_valid
  · exact law17_valid
  · exact law18_valid
  · exact law19_valid
  · exact law20_valid
  · exact law21_valid

theorem unit4_idempotent : tableMul 4 4 = 4 := by decide
theorem unit5_idempotent : tableMul 5 5 = 5 := by decide
theorem units_orthogonal : tableMul 4 5 = 0 ∧ tableMul 5 4 = 0 := by decide
theorem zero_absorbing : ∀ a : Fin 6, tableMul 0 a = 0 ∧ tableMul a 0 = 0 := by decide
theorem left_unit_cover : ∀ a : Fin 6, tableMul 4 a = a ∨ tableMul 5 a = a := by decide
theorem right_unit_cover : ∀ a : Fin 6, tableMul a 4 = a ∨ tableMul a 5 = a := by decide
theorem left_units_injective : ∀ a b : Fin 6,
    tableMul 4 a = tableMul 4 b → tableMul 5 a = tableMul 5 b → a = b := by decide
theorem right_units_injective : ∀ a b : Fin 6,
    tableMul a 4 = tableMul b 4 → tableMul a 5 = tableMul b 5 → a = b := by decide

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.table_literal_exact
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.lawPower_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.lawLeft_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.lawRight_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.lawSquare_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law04_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law05_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law06_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law07_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law08_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law09_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law10_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law11_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law12_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law13_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law14_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law15_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law16_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law17_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law18_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law19_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law20_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.law21_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.models
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.unit4_idempotent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.unit5_idempotent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.units_orthogonal
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.zero_absorbing
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.left_unit_cover
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.right_unit_cover
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.left_units_injective
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.right_units_injective

end SemigroupBasis.CoRoots.Order6SporadicSection18.Actual
