import SemigroupBasis.CoRoots.Order6SporadicSection17Basis
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Exact context-safe raw13 instances for Proposition17.1. A square is
not collapsed to a cube: only fourth and higher powers collapse to cubes.
Optional contexts are split into empty and nonempty cases. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

abbrev ListDerives : List Nat → List Nat → Prop := S5_107.ListDerives basis

private def replacement (x y h k t : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => h
  | 3 => k
  | _ => t

private theorem instantiate (law : Identity Nat) (member : law ∈ basis)
    (x y h k t : Word Nat) :
    ListDerives (law.lhs.bind (replacement x y h k t)).toList
      (law.rhs.bind (replacement x y h k t)).toList :=
  S5_107.ListDerives.ofWord
    (Derives.subst (Derives.fromBasis (e := law) member) (replacement x y h k t))

theorem fourthPower (x : Nat) : ListDerives [x,x,x,x] [x,x,x] :=
  instantiate lawLeft (by decide) (Word.singleton x) (Word.singleton x)
    (Word.singleton x) (Word.singleton x) (Word.singleton x)

theorem cubeIdempotent (x : Nat) : ListDerives [x,x,x,x,x,x] [x,x,x] := by
  have first : ListDerives [x,x,x,x,x,x] [x,x,x,x,x] := (fourthPower x).append [x,x]
  have second : ListDerives [x,x,x,x,x] [x,x,x,x] := (fourthPower x).append [x]
  exact first.trans (second.trans (fourthPower x))

theorem duplicateFirst (x : Nat) (gap : List Nat) (nonempty : gap ≠ []) :
    ListDerives ([x] ++ gap ++ [x]) ([x,x] ++ gap ++ [x]) := by
  cases gap with
  | nil => exact False.elim (nonempty rfl)
  | cons h t =>
      have raw := instantiate lawLeft (by decide) (Word.singleton x)
        (S5_107.listWordOfCons h t) (Word.singleton x) (Word.singleton x) (Word.singleton x)
      simpa [lawLeft,replacement,Word.bind,Word.toList,Word.append,
        Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw.symm

theorem duplicateLast (x : Nat) (gap : List Nat) (nonempty : gap ≠ []) :
    ListDerives ([x] ++ gap ++ [x]) ([x] ++ gap ++ [x,x]) := by
  cases gap with
  | nil => exact False.elim (nonempty rfl)
  | cons h t =>
      have raw := instantiate lawRight (by decide) (Word.singleton x)
        (S5_107.listWordOfCons h t) (Word.singleton x) (Word.singleton x) (Word.singleton x)
      simpa [lawRight,replacement,Word.bind,Word.toList,Word.append,
        Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw.symm

theorem cubeFirst (x : Nat) (gap : List Nat) (nonempty : gap ≠ []) :
    ListDerives ([x] ++ gap ++ [x]) ([x,x,x] ++ gap ++ [x]) := by
  have first := duplicateFirst x gap nonempty
  have second : ListDerives ([x,x] ++ gap ++ [x]) ([x,x,x] ++ gap ++ [x]) := by
    simpa [List.append_assoc] using (duplicateFirst x gap nonempty).prepend [x]
  exact first.trans second

theorem cubeLast (x : Nat) (gap : List Nat) (nonempty : gap ≠ []) :
    ListDerives ([x] ++ gap ++ [x]) ([x] ++ gap ++ [x,x,x]) := by
  have first := duplicateLast x gap nonempty
  have second : ListDerives ([x] ++ gap ++ [x,x]) ([x] ++ gap ++ [x,x,x]) := by
    simpa [List.append_assoc] using (duplicateLast x gap nonempty).append [x]
  exact first.trans second

theorem swapSquares (x y : Nat) (gap : List Nat) :
    ListDerives ([x,x] ++ gap ++ [y,y]) ([y,y] ++ gap ++ [x,x]) := by
  cases gap with
  | nil =>
      exact instantiate lawSquare (by decide) (Word.singleton x) (Word.singleton y)
        (Word.singleton x) (Word.singleton x) (Word.singleton x)
  | cons h t =>
      have raw := instantiate lawSquareH (by decide) (Word.singleton x) (Word.singleton y)
        (S5_107.listWordOfCons h t) (Word.singleton x) (Word.singleton x)
      simpa [lawSquareH,replacement,Word.bind,Word.toList,Word.append,
        Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw

theorem swapCubeSquare (x y : Nat) (gap : List Nat) :
    ListDerives ([x,x,x] ++ gap ++ [y,y]) ([y,y] ++ gap ++ [x,x,x]) := by
  cases gap with
  | nil =>
      exact instantiate lawCubeSquare (by decide) (Word.singleton x) (Word.singleton y)
        (Word.singleton x) (Word.singleton x) (Word.singleton x)
  | cons h t =>
      have raw := instantiate lawCubeSquareH (by decide) (Word.singleton x) (Word.singleton y)
        (S5_107.listWordOfCons h t) (Word.singleton x) (Word.singleton x)
      simpa [lawCubeSquareH,replacement,Word.bind,Word.toList,Word.append,
        Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw

theorem swapCubes (x y : Nat) (gap : List Nat) :
    ListDerives ([x,x,x] ++ gap ++ [y,y,y]) ([y,y,y] ++ gap ++ [x,x,x]) := by
  cases gap with
  | nil =>
      exact instantiate lawCubes (by decide) (Word.singleton x) (Word.singleton y)
        (Word.singleton x) (Word.singleton x) (Word.singleton x)
  | cons h t =>
      have raw := instantiate lawCubesH (by decide) (Word.singleton x) (Word.singleton y)
        (S5_107.listWordOfCons h t) (Word.singleton x) (Word.singleton x)
      simpa [lawCubesH,replacement,Word.bind,Word.toList,Word.append,
        Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw

theorem spreadCubeRight (x h : Nat) (gap : List Nat) (nonempty : gap ≠ []) :
    ListDerives ([x,x,x] ++ gap ++ [h,h]) ([x,x,x] ++ gap ++ [x,x,x,h,h]) := by
  cases gap with
  | nil => exact False.elim (nonempty rfl)
  | cons y ys =>
      have raw := instantiate lawSpreadRight (by decide) (Word.singleton x)
        (S5_107.listWordOfCons y ys) (Word.singleton h) (Word.singleton x) (Word.singleton x)
      simpa [lawSpreadRight,replacement,Word.bind,Word.toList,Word.append,
        Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw

theorem spreadCubeLeft (h x : Nat) (gap : List Nat) (nonempty : gap ≠ []) :
    ListDerives ([h,h] ++ gap ++ [x,x,x]) ([h,h,x,x,x] ++ gap ++ [x,x,x]) := by
  cases gap with
  | nil => exact False.elim (nonempty rfl)
  | cons y ys =>
      have raw := instantiate lawSpreadLeft (by decide) (Word.singleton x)
        (S5_107.listWordOfCons y ys) (Word.singleton h) (Word.singleton x) (Word.singleton x)
      simpa [lawSpreadLeft,replacement,Word.bind,Word.toList,Word.append,
        Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw

theorem slideSquare (h x k : Nat) (gap : List Nat) :
    ListDerives ([h,h,x,x] ++ gap ++ [k,k]) ([h,h] ++ gap ++ [x,x,k,k]) := by
  cases gap with
  | nil => exact S5_107.ListDerives.refl _
  | cons y ys =>
      have raw := instantiate lawSlide (by decide) (Word.singleton x)
        (S5_107.listWordOfCons y ys) (Word.singleton h) (Word.singleton k) (Word.singleton k)
      simpa [lawSlide,replacement,Word.bind,Word.toList,Word.append,
        Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw

theorem swapRepeatedBlocks (h x y : Word Nat) :
    ListDerives (h.toList ++ x.toList ++ h.toList ++ y.toList ++ h.toList)
      (h.toList ++ y.toList ++ h.toList ++ x.toList ++ h.toList) := by
  have raw := instantiate lawSwapBlocks (by decide) x y h h h
  simpa [lawSwapBlocks,replacement,Word.bind,Word.toList,Word.append,List.append_assoc] using raw

theorem swapSquareGaps (h k t : Nat) (x y : Word Nat) :
    ListDerives ([h,h] ++ x.toList ++ [k,k] ++ y.toList ++ [t,t])
      ([h,h] ++ y.toList ++ [k,k] ++ x.toList ++ [t,t]) := by
  have raw := instantiate lawSwapSquareBlocks (by decide) x y
    (Word.singleton h) (Word.singleton k) (Word.singleton t)
  simpa [lawSwapSquareBlocks,replacement,Word.bind,Word.toList,Word.append,
    Word.singleton,List.append_assoc] using raw

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.fourthPower
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubeIdempotent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubeFirst
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubeLast
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.swapSquares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.swapCubeSquare
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.swapCubes
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.spreadCubeRight
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.spreadCubeLeft
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.slideSquare
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.swapRepeatedBlocks
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.swapSquareGaps

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
