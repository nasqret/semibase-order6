import SemigroupBasis.CoRoots.Order6SporadicSection22Basis
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Unrestricted E5 derivations from the exact five laws of Proposition22.1.
The empty middle case is treated separately; no empty semigroup substitution
is used for the ordinary variable y in22.1b. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection22.E5
open SemigroupBasis

abbrev ListDerives : List Nat → List Nat → Prop := S5_107.ListDerives basis

private def replacement (x y h : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | _ => h

private theorem instantiate (law : Identity Nat) (member : law ∈ basis) (x y h : Word Nat) :
    ListDerives (law.lhs.bind (replacement x y h)).toList (law.rhs.bind (replacement x y h)).toList :=
  S5_107.ListDerives.ofWord (Derives.subst (Derives.fromBasis (e := law) member) (replacement x y h))

theorem listPower (x : Nat) : ListDerives [x,x,x] [x,x] :=
  instantiate lawPower (by decide) (Word.singleton x) (Word.singleton x) (Word.singleton x)

theorem fourthPower (x : Nat) : ListDerives [x,x,x,x] [x,x] :=
  ((listPower x).append [x]).trans (listPower x)

theorem duplicateFirst (x : Nat) (gap : List Nat) :
    ListDerives ([x] ++ gap ++ [x]) ([x,x] ++ gap ++ [x]) := by
  cases gap with
  | nil => exact (listPower x).symm
  | cons h t =>
      have raw := instantiate lawLeft (by decide) (Word.singleton x)
        (S5_107.listWordOfCons h t) (Word.singleton x)
      simpa [lawLeft,replacement,Word.bind,Word.toList,Word.append,
        Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw.symm

theorem duplicateLast (x : Nat) (gap : List Nat) :
    ListDerives ([x] ++ gap ++ [x]) ([x] ++ gap ++ [x,x]) := by
  cases gap with
  | nil => exact (listPower x).symm
  | cons h t =>
      have raw := instantiate lawRight (by decide) (Word.singleton x)
        (S5_107.listWordOfCons h t) (Word.singleton x)
      simpa [lawRight,replacement,Word.bind,Word.toList,Word.append,
        Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw.symm

theorem duplicateLastOfSeen (stem : List Nat) (x : Nat) (seen : x ∈ stem) :
    ListDerives (stem ++ [x]) (stem ++ [x,x]) := by
  obtain ⟨before,gap,shape⟩ := List.mem_iff_append.mp seen
  simpa [shape,List.append_assoc] using (duplicateLast x gap).prepend before

theorem duplicateFirstOfSeen (x : Nat) (rest : List Nat) (seen : x ∈ rest) :
    ListDerives (x :: rest) (x :: x :: rest) := by
  obtain ⟨gap,after,shape⟩ := List.mem_iff_append.mp seen
  simpa [shape,List.append_assoc] using (duplicateFirst x gap).append after

theorem duplicateOccurrence (stem : List Nat) (x : Nat) (suffix : List Nat)
    (seen : x ∈ stem ∨ x ∈ suffix) :
    ListDerives (stem ++ x :: suffix) (stem ++ x :: x :: suffix) := by
  rcases seen with prior | later
  · simpa [List.append_assoc] using (duplicateLastOfSeen stem x prior).append suffix
  · exact (duplicateFirstOfSeen x suffix later).prepend stem

theorem moveProtected (h x : Nat) (gap : List Nat) (nonempty : gap ≠ []) :
    ListDerives ([h,h,x] ++ gap ++ [x]) ([h,h] ++ gap ++ [x,x]) := by
  cases gap with
  | nil => exact False.elim (nonempty rfl)
  | cons y ys =>
      have raw := instantiate lawMove (by decide) (Word.singleton x)
        (S5_107.listWordOfCons y ys) (Word.singleton h)
      simpa [lawMove,replacement,Word.bind,Word.toList,Word.append,
        Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw

/-- Insert a square immediately after an existing square, retaining the
later source square and the complete intervening word. -/
theorem inflateAfterSquare (h x : Nat) (gap : List Nat) :
    ListDerives ([h,h] ++ gap ++ [x,x]) ([h,h,x,x] ++ gap ++ [x,x]) := by
  by_cases empty : gap = []
  · subst gap
    exact (fourthPower x).symm.prepend [h,h]
  · have first := (moveProtected h x gap empty).symm
    have second : ListDerives ([h,h,x] ++ gap ++ [x]) ([h,h,x,x] ++ gap ++ [x]) := by
      simpa [List.append_assoc] using (duplicateFirst x gap).prepend [h,h]
    have third : ListDerives ([h,h,x,x] ++ gap ++ [x]) ([h,h,x,x] ++ gap ++ [x,x]) := by
      simpa [List.append_assoc] using (duplicateLast x gap).prepend [h,h,x]
    exact first.trans (second.trans third)

theorem swapProtectedSquares (h x y : Nat) :
    ListDerives [h,h,x,x,y,y] [h,h,y,y,x,x] :=
  instantiate lawSwap (by decide) (Word.singleton x) (Word.singleton y) (Word.singleton h)

#print axioms duplicateFirst
#print axioms duplicateLast
#print axioms duplicateOccurrence
#print axioms moveProtected
#print axioms inflateAfterSquare
#print axioms swapProtectedSquares

end SemigroupBasis.CoRoots.Order6SporadicSection22.E5
