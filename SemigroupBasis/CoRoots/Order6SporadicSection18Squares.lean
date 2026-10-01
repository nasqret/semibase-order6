import SemigroupBasis.CoRoots.Order6SporadicSection18Basis
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! The unrestricted commutative-idempotent algebra of square blocks in
Lee–Zhang Section18. No bound on the alphabet, word length or multiplicity. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18
open SemigroupBasis

abbrev ListDerives : List Nat → List Nat → Prop := S5_107.ListDerives basis

private def two (x y : Word Nat) : Nat → Word Nat
  | 0 => x
  | _ => y

private theorem instantiateTwo (law : Identity Nat) (member : law ∈ basis)
    (x y : Word Nat) :
    ListDerives (law.lhs.bind (two x y)).toList (law.rhs.bind (two x y)).toList :=
  S5_107.ListDerives.ofWord
    (Derives.subst (Derives.fromBasis (e := law) member) (two x y))

theorem listPower (x : Nat) : ListDerives [x,x,x] [x,x] :=
  instantiateTwo lawPower (by decide) (Word.singleton x) (Word.singleton x)

theorem fourthPower (x : Nat) : ListDerives [x,x,x,x] [x,x] :=
  ((listPower x).append [x]).trans (listPower x)

theorem duplicateFirst (x : Nat) (gap : List Nat) :
    ListDerives ([x] ++ gap ++ [x]) ([x,x] ++ gap ++ [x]) := by
  cases gap with
  | nil => exact (listPower x).symm
  | cons h t =>
      have raw := instantiateTwo lawLeft (by decide) (Word.singleton x)
        (S5_107.listWordOfCons h t)
      simpa [lawLeft,two,Word.bind,Word.toList,Word.append,
        Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw.symm

theorem duplicateLast (x : Nat) (gap : List Nat) :
    ListDerives ([x] ++ gap ++ [x]) ([x] ++ gap ++ [x,x]) := by
  cases gap with
  | nil => exact (listPower x).symm
  | cons h t =>
      have raw := instantiateTwo lawRight (by decide) (Word.singleton x)
        (S5_107.listWordOfCons h t)
      simpa [lawRight,two,Word.bind,Word.toList,Word.append,
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

theorem swapSquares (x y : Nat) : ListDerives [x,x,y,y] [y,y,x,x] :=
  instantiateTwo lawSquare (by decide) (Word.singleton x) (Word.singleton y)

def squareList (letters : List Nat) : List Nat := letters.flatMap (fun x => [x,x])

theorem squareList_nil : squareList [] = [] := rfl
theorem squareList_cons (x : Nat) (xs : List Nat) :
    squareList (x :: xs) = [x,x] ++ squareList xs := rfl
theorem squareList_append (xs ys : List Nat) :
    squareList (xs ++ ys) = squareList xs ++ squareList ys := List.flatMap_append

theorem squareList_mem (letters : List Nat) (x : Nat) :
    x ∈ squareList letters ↔ x ∈ letters := by
  induction letters with
  | nil => simp [squareList]
  | cons h t ih => simp [squareList_cons,ih]

theorem moveToFront (x : Nat) (before after : List Nat) :
    (before ++ x :: after).Perm (x :: before ++ after) := by
  induction before with
  | nil => exact List.Perm.refl _
  | cons h t ih => exact (List.Perm.cons h ih).trans (List.Perm.swap x h (t ++ after))

theorem permAppend (xs ys : List Nat) : (xs ++ ys).Perm (ys ++ xs) := by
  induction xs with
  | nil => simpa using List.Perm.refl ys
  | cons x xs ih =>
      simpa using (List.Perm.cons x ih).trans (moveToFront x ys xs).symm

/-- Unlike Section17, no protected last square is needed. -/
theorem permuteSquares {left right : List Nat} (permutation : left.Perm right) :
    ListDerives (squareList left) (squareList right) := by
  induction permutation with
  | nil => exact S5_107.ListDerives.refl _
  | cons x permutation ih =>
      simpa [squareList_cons,List.append_assoc] using ih.prepend [x,x]
  | swap x y rest =>
      simpa [squareList_cons,List.append_assoc] using (swapSquares x y).symm.append (squareList rest)
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

theorem contractSeenSquare (letters : List Nat) (x : Nat) (seen : x ∈ letters) :
    ListDerives (squareList (x :: letters)) (squareList letters) := by
  obtain ⟨before,after,shape⟩ := List.mem_iff_append.mp seen
  have permutation : (x :: letters).Perm (x :: x :: (before ++ after)) := by
    simpa [shape] using List.Perm.cons x (moveToFront x before after)
  have first := permuteSquares permutation
  have contraction : ListDerives (squareList (x :: x :: (before ++ after)))
      (squareList (x :: (before ++ after))) := by
    simpa [squareList_cons,List.append_assoc] using (fourthPower x).append (squareList (before ++ after))
  have restore : ListDerives (squareList (x :: (before ++ after))) (squareList letters) := by
    simpa [shape] using (permuteSquares (moveToFront x before after)).symm
  exact first.trans (contraction.trans restore)

theorem prependKnownSquares (letters extras : List Nat)
    (known : ∀ x ∈ extras, x ∈ letters) :
    ListDerives (squareList letters) (squareList (extras ++ letters)) := by
  induction extras with
  | nil => exact S5_107.ListDerives.refl _
  | cons x xs ih =>
      have first := ih (fun y member => known y (List.mem_cons_of_mem x member))
      have seen : x ∈ xs ++ letters := List.mem_append.mpr (Or.inr (known x (by simp)))
      simpa using first.trans (contractSeenSquare (xs ++ letters) x seen).symm

/-- Arbitrary square blocks with equal support are derivably equal. -/
theorem squareBlocks_same_content (left right : List Nat)
    (same : ∀ x, x ∈ left ↔ x ∈ right) :
    ListDerives (squareList left) (squareList right) := by
  have addRight := prependKnownSquares left right (fun x member => (same x).mpr member)
  have commute := permuteSquares (permAppend right left)
  have addLeft := prependKnownSquares right left (fun x member => (same x).mp member)
  exact addRight.trans (commute.trans addLeft.symm)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.listPower
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.fourthPower
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.duplicateOccurrence
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.swapSquares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.squareList_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.permuteSquares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.contractSeenSquare
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.prependKnownSquares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.squareBlocks_same_content

end SemigroupBasis.CoRoots.Order6SporadicSection18
