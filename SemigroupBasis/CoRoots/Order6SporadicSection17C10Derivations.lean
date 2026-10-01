import SemigroupBasis.CoRoots.Order6SporadicSection17Basis
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Context-safe, unrestricted instances of Proposition17.5. Empty H/K
are separate basis members; no empty semigroup substitutions occur. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
open SemigroupBasis

abbrev ListDerives : List Nat → List Nat → Prop := S5_107.ListDerives basis

private def replacement (x y h k : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => h
  | _ => k

private theorem instantiate (law : Identity Nat) (member : law ∈ basis)
    (x y h k : Word Nat) :
    ListDerives (law.lhs.bind (replacement x y h k)).toList
      (law.rhs.bind (replacement x y h k)).toList :=
  S5_107.ListDerives.ofWord
    (Derives.subst (Derives.fromBasis (e := law) member) (replacement x y h k))

theorem listPower (x : Nat) : ListDerives [x,x,x] [x,x] :=
  instantiate lawPower (by decide) (Word.singleton x) (Word.singleton x)
    (Word.singleton x) (Word.singleton x)

theorem fourthPower (x : Nat) : ListDerives [x,x,x,x] [x,x] :=
  ((listPower x).append [x]).trans (listPower x)

theorem duplicateFirst (x : Nat) (gap : List Nat) :
    ListDerives ([x] ++ gap ++ [x]) ([x,x] ++ gap ++ [x]) := by
  cases gap with
  | nil => exact (listPower x).symm
  | cons h t =>
      have raw := instantiate lawLeft (by decide) (Word.singleton x)
        (S5_107.listWordOfCons h t) (Word.singleton x) (Word.singleton x)
      simpa [lawLeft,replacement,Word.bind,Word.toList,Word.append,
        Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw.symm

theorem duplicateLast (x : Nat) (gap : List Nat) :
    ListDerives ([x] ++ gap ++ [x]) ([x] ++ gap ++ [x,x]) := by
  cases gap with
  | nil => exact (listPower x).symm
  | cons h t =>
      have raw := instantiate lawRight (by decide) (Word.singleton x)
        (S5_107.listWordOfCons h t) (Word.singleton x) (Word.singleton x)
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

theorem swapProtectedSquares (x y h : Nat) :
    ListDerives [x,x,y,y,h,h] [y,y,x,x,h,h] :=
  instantiate lawPermute (by decide) (Word.singleton x) (Word.singleton y)
    (Word.singleton h) (Word.singleton h)

theorem inflateBeforeSquare (h x : Nat) (gap : List Nat) :
    ListDerives ([h,h] ++ gap ++ [x,x]) ([x,x,h,h] ++ gap ++ [x,x]) := by
  have first : ListDerives ([h,h] ++ gap ++ [x,x]) ([x,h,h] ++ gap ++ [x]) := by
    cases gap with
    | nil =>
        exact instantiate lawInflate (by decide) (Word.singleton h) (Word.singleton x)
          (Word.singleton h) (Word.singleton h)
    | cons a rest =>
        have raw := instantiate lawInflateH (by decide) (Word.singleton h) (Word.singleton x)
          (S5_107.listWordOfCons a rest) (Word.singleton h)
        simpa [lawInflateH,replacement,Word.bind,Word.toList,Word.append,
          Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw
  have second : ListDerives ([x,h,h] ++ gap ++ [x]) ([x,x,h,h] ++ gap ++ [x]) := by
    simpa [List.append_assoc] using duplicateFirst x ([h,h] ++ gap)
  have third : ListDerives ([x,x,h,h] ++ gap ++ [x]) ([x,x,h,h] ++ gap ++ [x,x]) := by
    simpa [List.append_assoc] using duplicateLast x ([x,h,h] ++ gap)
  exact first.trans (second.trans third)

theorem swapOrdered (x y : Nat) (firstGap secondGap : List Nat) :
    ListDerives ([x,y] ++ firstGap ++ [x] ++ secondGap ++ [y])
      ([y,x] ++ firstGap ++ [x] ++ secondGap ++ [y]) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          exact instantiate lawSwap (by decide) (Word.singleton x) (Word.singleton y)
            (Word.singleton x) (Word.singleton x)
      | cons h t =>
          have raw := instantiate lawSwapK (by decide) (Word.singleton x) (Word.singleton y)
            (Word.singleton x) (S5_107.listWordOfCons h t)
          simpa [lawSwapK,replacement,Word.bind,Word.toList,Word.append,
            Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw
  | cons h t =>
      cases secondGap with
      | nil =>
          have raw := instantiate lawSwapH (by decide) (Word.singleton x) (Word.singleton y)
            (S5_107.listWordOfCons h t) (Word.singleton x)
          simpa [lawSwapH,replacement,Word.bind,Word.toList,Word.append,
            Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw
      | cons k s =>
          have raw := instantiate lawSwapHK (by decide) (Word.singleton x) (Word.singleton y)
            (S5_107.listWordOfCons h t) (S5_107.listWordOfCons k s)
          simpa [lawSwapHK,replacement,Word.bind,Word.toList,Word.append,
            Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw

/-- Only letters genuinely present in the retained suffix may be swapped. -/
theorem swapBeforeSeen (x y : Nat) (suffix : List Nat)
    (seenX : x ∈ suffix) (seenY : y ∈ suffix) :
    ListDerives ([x,y] ++ suffix) ([y,x] ++ suffix) := by
  by_cases same : x = y
  · subst y
    exact S5_107.ListDerives.refl _
  obtain ⟨before,after,shape⟩ := List.mem_iff_append.mp seenX
  by_cases earlier : y ∈ before
  · obtain ⟨firstGap,secondGap,beforeShape⟩ := List.mem_iff_append.mp earlier
    simpa [shape,beforeShape,List.append_assoc] using
      (swapOrdered y x firstGap secondGap).symm.append after
  · have later : y ∈ after := by
      rw [shape] at seenY
      rcases List.mem_append.mp seenY with inBefore | inTail
      · exact False.elim (earlier inBefore)
      · exact (List.mem_cons.mp inTail).resolve_left (Ne.symm same)
    obtain ⟨secondGap,rest,afterShape⟩ := List.mem_iff_append.mp later
    simpa [shape,afterShape,List.append_assoc] using
      (swapOrdered x y before secondGap).append rest

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.duplicateOccurrence
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.swapProtectedSquares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.inflateBeforeSquare
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.swapBeforeSeen

end SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
