import SemigroupBasis.CoRoots.Order6SporadicSection17Basis
import SemigroupBasis.FiniteReflection

/-! Literal direct catalogue table and raw-basis soundness.
Every closed decision ranges over at most three Fin6 values.
This module supplies no completeness assumption. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.S6_2779
open SemigroupBasis

def tableMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)) else (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6))

def table : FiniteTable where
  order := 6
  mul := tableMul
  assoc := by decide

theorem table_literal_exact :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (tableMul a b).val)) =
      [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2], [0, 0, 1, 0, 1, 1], [0, 0, 1, 0, 1, 2], [0, 1, 1, 3, 3, 5]] := by decide

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

private theorem checkSquare :
    ∀ x y : Fin 6,
      (tableMul (tableMul (tableMul x x) y) y) = (tableMul (tableMul (tableMul y y) x) x) := by decide

theorem modelsSquare : lawSquare.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkSquare (valuation 0) (valuation 1)

private theorem checkSquareH :
    ∀ x h y : Fin 6,
      (tableMul (tableMul (tableMul (tableMul x x) h) y) y) = (tableMul (tableMul (tableMul (tableMul y y) h) x) x) := by decide

theorem modelsSquareH : lawSquareH.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkSquareH (valuation 0) (valuation 2) (valuation 1)

private theorem checkCubeSquare :
    ∀ x y : Fin 6,
      (tableMul (tableMul (tableMul (tableMul x x) x) y) y) = (tableMul (tableMul (tableMul (tableMul y y) x) x) x) := by decide

theorem modelsCubeSquare : lawCubeSquare.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkCubeSquare (valuation 0) (valuation 1)

private theorem checkCubeSquareH :
    ∀ x h y : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul x x) x) h) y) y) = (tableMul (tableMul (tableMul (tableMul (tableMul y y) h) x) x) x) := by decide

theorem modelsCubeSquareH : lawCubeSquareH.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkCubeSquareH (valuation 0) (valuation 2) (valuation 1)

private theorem checkCubes :
    ∀ x y : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul x x) x) y) y) y) = (tableMul (tableMul (tableMul (tableMul (tableMul y y) y) x) x) x) := by decide

theorem modelsCubes : lawCubes.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkCubes (valuation 0) (valuation 1)

private theorem checkCubesH :
    ∀ x h y : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul x x) x) h) y) y) y) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul y y) y) h) x) x) x) := by decide

theorem modelsCubesH : lawCubesH.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkCubesH (valuation 0) (valuation 2) (valuation 1)

private theorem checkSpreadRight :
    ∀ x y h : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul x x) x) y) h) h) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul x x) x) y) x) x) x) h) h) := by decide

theorem modelsSpreadRight : lawSpreadRight.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkSpreadRight (valuation 0) (valuation 1) (valuation 2)

private theorem checkSpreadLeft :
    ∀ h y x : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul h h) y) x) x) x) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul h h) x) x) x) y) x) x) x) := by decide

theorem modelsSpreadLeft : lawSpreadLeft.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkSpreadLeft (valuation 2) (valuation 1) (valuation 0)

private theorem checkSlide_0 :
    ∀ x y k : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) x) x) y) k) k) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) y) x) x) k) k) := by decide

private theorem checkSlide_1 :
    ∀ x y k : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) x) x) y) k) k) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) y) x) x) k) k) := by decide

private theorem checkSlide_2 :
    ∀ x y k : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) x) x) y) k) k) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) y) x) x) k) k) := by decide

private theorem checkSlide_3 :
    ∀ x y k : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) x) x) y) k) k) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) y) x) x) k) k) := by decide

private theorem checkSlide_4 :
    ∀ x y k : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) x) x) y) k) k) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) y) x) x) k) k) := by decide

private theorem checkSlide_5 :
    ∀ x y k : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) x) x) y) k) k) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) y) x) x) k) k) := by decide

private theorem checkSlide :
    ∀ h x y k : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul h h) x) x) y) k) k) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul h h) y) x) x) k) k) := by
  intro h x y k
  have cases_h : h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 := by
    revert h
    decide
  rcases cases_h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSlide_0 x y k
  · exact checkSlide_1 x y k
  · exact checkSlide_2 x y k
  · exact checkSlide_3 x y k
  · exact checkSlide_4 x y k
  · exact checkSlide_5 x y k

theorem modelsSlide : lawSlide.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkSlide (valuation 2) (valuation 0) (valuation 1) (valuation 3)

private theorem checkSwapBlocks :
    ∀ h x y : Fin 6,
      (tableMul (tableMul (tableMul (tableMul h x) h) y) h) = (tableMul (tableMul (tableMul (tableMul h y) h) x) h) := by decide

theorem modelsSwapBlocks : lawSwapBlocks.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkSwapBlocks (valuation 2) (valuation 0) (valuation 1)

private theorem checkSwapSquareBlocks_0_0 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) (0 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) y) k) k) (0 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_0_1 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) (1 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) y) k) k) (1 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_0_2 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) (2 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) y) k) k) (2 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_0_3 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) (3 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) y) k) k) (3 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_0_4 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) (4 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) y) k) k) (4 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_0_5 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) (5 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (0 : Fin 6) (0 : Fin 6)) y) k) k) (5 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_1_0 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) (0 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) y) k) k) (0 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_1_1 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) (1 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) y) k) k) (1 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_1_2 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) (2 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) y) k) k) (2 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_1_3 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) (3 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) y) k) k) (3 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_1_4 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) (4 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) y) k) k) (4 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_1_5 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) (5 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (1 : Fin 6) (1 : Fin 6)) y) k) k) (5 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_2_0 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) (0 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) y) k) k) (0 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_2_1 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) (1 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) y) k) k) (1 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_2_2 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) (2 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) y) k) k) (2 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_2_3 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) (3 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) y) k) k) (3 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_2_4 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) (4 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) y) k) k) (4 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_2_5 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) (5 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (2 : Fin 6) (2 : Fin 6)) y) k) k) (5 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_3_0 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) (0 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) y) k) k) (0 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_3_1 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) (1 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) y) k) k) (1 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_3_2 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) (2 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) y) k) k) (2 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_3_3 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) (3 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) y) k) k) (3 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_3_4 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) (4 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) y) k) k) (4 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_3_5 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) (5 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (3 : Fin 6) (3 : Fin 6)) y) k) k) (5 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_4_0 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) (0 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) y) k) k) (0 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_4_1 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) (1 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) y) k) k) (1 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_4_2 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) (2 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) y) k) k) (2 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_4_3 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) (3 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) y) k) k) (3 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_4_4 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) (4 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) y) k) k) (4 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_4_5 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) (5 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (4 : Fin 6) (4 : Fin 6)) y) k) k) (5 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_5_0 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) (0 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) y) k) k) (0 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_5_1 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) (1 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) y) k) k) (1 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_5_2 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) (2 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) y) k) k) (2 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_5_3 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) (3 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) y) k) k) (3 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_5_4 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) (4 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) y) k) k) (4 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks_5_5 :
    ∀ k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) (5 : Fin 6)) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (5 : Fin 6) (5 : Fin 6)) y) k) k) (5 : Fin 6)) t) t) := by decide

private theorem checkSwapSquareBlocks :
    ∀ h x k y t : Fin 6,
      (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul h h) x) k) k) y) t) t) = (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul (tableMul h h) y) k) k) x) t) t) := by
  intro h x k y t
  have cases_h : h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 := by
    revert h
    decide
  have cases_x : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
    revert x
    decide
  rcases cases_h with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases cases_x with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSwapSquareBlocks_0_0 k y t
  · exact checkSwapSquareBlocks_0_1 k y t
  · exact checkSwapSquareBlocks_0_2 k y t
  · exact checkSwapSquareBlocks_0_3 k y t
  · exact checkSwapSquareBlocks_0_4 k y t
  · exact checkSwapSquareBlocks_0_5 k y t
  · exact checkSwapSquareBlocks_1_0 k y t
  · exact checkSwapSquareBlocks_1_1 k y t
  · exact checkSwapSquareBlocks_1_2 k y t
  · exact checkSwapSquareBlocks_1_3 k y t
  · exact checkSwapSquareBlocks_1_4 k y t
  · exact checkSwapSquareBlocks_1_5 k y t
  · exact checkSwapSquareBlocks_2_0 k y t
  · exact checkSwapSquareBlocks_2_1 k y t
  · exact checkSwapSquareBlocks_2_2 k y t
  · exact checkSwapSquareBlocks_2_3 k y t
  · exact checkSwapSquareBlocks_2_4 k y t
  · exact checkSwapSquareBlocks_2_5 k y t
  · exact checkSwapSquareBlocks_3_0 k y t
  · exact checkSwapSquareBlocks_3_1 k y t
  · exact checkSwapSquareBlocks_3_2 k y t
  · exact checkSwapSquareBlocks_3_3 k y t
  · exact checkSwapSquareBlocks_3_4 k y t
  · exact checkSwapSquareBlocks_3_5 k y t
  · exact checkSwapSquareBlocks_4_0 k y t
  · exact checkSwapSquareBlocks_4_1 k y t
  · exact checkSwapSquareBlocks_4_2 k y t
  · exact checkSwapSquareBlocks_4_3 k y t
  · exact checkSwapSquareBlocks_4_4 k y t
  · exact checkSwapSquareBlocks_4_5 k y t
  · exact checkSwapSquareBlocks_5_0 k y t
  · exact checkSwapSquareBlocks_5_1 k y t
  · exact checkSwapSquareBlocks_5_2 k y t
  · exact checkSwapSquareBlocks_5_3 k y t
  · exact checkSwapSquareBlocks_5_4 k y t
  · exact checkSwapSquareBlocks_5_5 k y t

theorem modelsSwapSquareBlocks : lawSwapSquareBlocks.SatisfiedBy table.semigroup := by
  intro valuation
  exact checkSwapSquareBlocks (valuation 2) (valuation 0) (valuation 3) (valuation 1) (valuation 4)

theorem models : Models table.semigroup basis := by
  intro e member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact modelsLeft
  · exact modelsRight
  · exact modelsSquare
  · exact modelsSquareH
  · exact modelsCubeSquare
  · exact modelsCubeSquareH
  · exact modelsCubes
  · exact modelsCubesH
  · exact modelsSpreadRight
  · exact modelsSpreadLeft
  · exact modelsSlide
  · exact modelsSwapBlocks
  · exact modelsSwapSquareBlocks

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.S6_2779.table_literal_exact
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.S6_2779.models
end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.S6_2779
