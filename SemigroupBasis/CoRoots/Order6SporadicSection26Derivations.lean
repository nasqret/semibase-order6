import SemigroupBasis.CoRoots.Order6SporadicSection26Basis
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Unrestricted list-context rules for all three reductions in Lemma26.2.
Optional gaps are split explicitly; ordinary substituted words stay nonempty. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection26.F7
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
  S5_107.ListDerives.ofWord (Derives.subst (Derives.fromBasis (e := law) member) (replacement x y h k))

theorem listPower (x : Nat) : ListDerives [x,x,x] [x,x] :=
  instantiate lawPower (by decide) (Word.singleton x) (Word.singleton x)
    (Word.singleton x) (Word.singleton x)

theorem duplicateFirst (x : Nat) (gap : List Nat) :
    ListDerives ([x] ++ gap ++ [x]) ([x,x] ++ gap ++ [x]) := by
  cases gap with
  | nil => exact (listPower x).symm
  | cons h t =>
      have raw := instantiate lawLeft (by decide) (Word.singleton x) (Word.singleton x)
        (S5_107.listWordOfCons h t) (Word.singleton x)
      simpa [lawLeft,replacement,Word.bind,Word.toList,Word.append,Word.singleton,
        S5_107.listWordOfCons,List.append_assoc] using raw.symm

theorem duplicateLast (x : Nat) (gap : List Nat) :
    ListDerives ([x] ++ gap ++ [x]) ([x] ++ gap ++ [x,x]) := by
  cases gap with
  | nil => exact (listPower x).symm
  | cons h t =>
      have raw := instantiate lawRight (by decide) (Word.singleton x) (Word.singleton x)
        (S5_107.listWordOfCons h t) (Word.singleton x)
      simpa [lawRight,replacement,Word.bind,Word.toList,Word.append,Word.singleton,
        S5_107.listWordOfCons,List.append_assoc] using raw.symm

theorem duplicateFirstOfSeen (x : Nat) (suffix : List Nat) (seen : x ∈ suffix) :
    ListDerives (x :: suffix) (x :: x :: suffix) := by
  obtain ⟨gap,after,shape⟩ := List.mem_iff_append.mp seen
  simpa [shape,List.append_assoc] using (duplicateFirst x gap).append after

theorem duplicateLastOfSeen (stem : List Nat) (x : Nat) (seen : x ∈ stem) :
    ListDerives (stem ++ [x]) (stem ++ [x,x]) := by
  obtain ⟨before,gap,shape⟩ := List.mem_iff_append.mp seen
  simpa [shape,List.append_assoc] using (duplicateLast x gap).prepend before

/-- Case k<l: remove a repeated x immediately before the repeated y,
retaining its multiplicity at its earlier occurrence. -/
theorem pairMove (x y : Nat) (gap middle : List Nat) :
    ListDerives ([x] ++ gap ++ [y] ++ middle ++ [x,y])
      ([x,x] ++ gap ++ [y] ++ middle ++ [y]) := by
  cases gap with
  | nil =>
      cases middle with
      | nil =>
          exact instantiate lawMove00 (by decide) (Word.singleton x) (Word.singleton y)
            (Word.singleton x) (Word.singleton x)
      | cons k ks =>
          have raw := instantiate lawMove01 (by decide) (Word.singleton x) (Word.singleton y)
            (Word.singleton x) (S5_107.listWordOfCons k ks)
          simpa [lawMove01,replacement,Word.bind,Word.toList,Word.append,Word.singleton,
            S5_107.listWordOfCons,List.append_assoc] using raw
  | cons h hs =>
      cases middle with
      | nil =>
          have raw := instantiate lawMove10 (by decide) (Word.singleton x) (Word.singleton y)
            (S5_107.listWordOfCons h hs) (Word.singleton x)
          simpa [lawMove10,replacement,Word.bind,Word.toList,Word.append,Word.singleton,
            S5_107.listWordOfCons,List.append_assoc] using raw
      | cons k ks =>
          have raw := instantiate lawMove11 (by decide) (Word.singleton x) (Word.singleton y)
            (S5_107.listWordOfCons h hs) (S5_107.listWordOfCons k ks)
          simpa [lawMove11,replacement,Word.bind,Word.toList,Word.append,Word.singleton,
            S5_107.listWordOfCons,List.append_assoc] using raw

/-- Case l<k. The inner middle is genuinely nonempty, as it contains the
new head of the later block in the canonical conversion. -/
theorem crossingFold (x y : Nat) (gap : List Nat) (middle : Word Nat) :
    ListDerives ([x] ++ gap ++ [y] ++ middle.toList ++ [y,x])
      ([x] ++ gap ++ [y,y] ++ middle.toList ++ [x]) := by
  cases gap with
  | nil =>
      have raw := instantiate lawFold0 (by decide) (Word.singleton x) (Word.singleton y)
        (Word.singleton x) middle
      cases middle with
      | mk h t =>
          simpa [lawFold0,replacement,Word.bind,Word.toList,Word.append,Word.singleton,
            List.append_assoc] using raw
  | cons h hs =>
      have raw := instantiate lawFold1 (by decide) (Word.singleton x) (Word.singleton y)
        (S5_107.listWordOfCons h hs) middle
      cases middle with
      | mk k ks =>
          simpa [lawFold1,replacement,Word.bind,Word.toList,Word.append,Word.singleton,
            S5_107.listWordOfCons,List.append_assoc] using raw

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.listPower
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.duplicateFirst
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.duplicateLast
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.duplicateFirstOfSeen
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.duplicateLastOfSeen
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.pairMove
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.crossingFold
end SemigroupBasis.CoRoots.Order6SporadicSection26.F7
