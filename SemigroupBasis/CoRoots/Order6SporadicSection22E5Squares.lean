import SemigroupBasis.CoRoots.Order6SporadicSection22E5Derivations

/-! Square-word calculus for the final block comparison in Proposition22.1.
Commutation always retains an actual preceding square. This module does
not assert the false unanchored commutation of arbitrary E5 squares. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection22.E5
open SemigroupBasis

def squareList (letters : List Nat) : List Nat := letters.flatMap (fun x => [x,x])

theorem squareList_nil : squareList [] = [] := rfl
theorem squareList_cons (x : Nat) (xs : List Nat) : squareList (x :: xs) = [x,x] ++ squareList xs := rfl
theorem squareList_append (xs ys : List Nat) : squareList (xs ++ ys) = squareList xs ++ squareList ys :=
  List.flatMap_append

theorem moveToFront (x : Nat) (before after : List Nat) :
    (before ++ x :: after).Perm (x :: before ++ after) := by
  induction before with
  | nil => exact List.Perm.refl _
  | cons h t ih => exact (List.Perm.cons h ih).trans (List.Perm.swap x h (t ++ after))

theorem permuteSquareTail {left right : List Nat} (permutation : left.Perm right) (h : Nat) :
    ListDerives ([h,h] ++ squareList left) ([h,h] ++ squareList right) := by
  induction permutation generalizing h with
  | nil => exact S5_107.ListDerives.refl _
  | cons x permutation ih =>
      simpa [squareList_cons,List.append_assoc] using (ih x).prepend [h,h]
  | swap x y rest =>
      simpa [squareList_cons,List.append_assoc] using (swapProtectedSquares h x y).symm.append (squareList rest)
  | trans first second ihFirst ihSecond => exact (ihFirst h).trans (ihSecond h)

/-- A later duplicate square can be contracted when its label is already
in the protected-head square word. -/
theorem contractSeenSquare (h : Nat) (letters : List Nat) (x : Nat) (seen : x ∈ h :: letters) :
    ListDerives ([h,h] ++ squareList (letters ++ [x])) ([h,h] ++ squareList letters) := by
  rcases List.mem_cons.mp seen with same | later
  · subst x
    have permuted := permuteSquareTail (moveToFront h letters []) h
    have contracted := (fourthPower h).append (squareList letters)
    have first : ListDerives ([h,h] ++ squareList (letters ++ [h]))
        ([h,h,h,h] ++ squareList letters) := by
      simpa [squareList_cons,List.append_assoc] using permuted
    exact first.trans contracted
  · obtain ⟨before,after,shape⟩ := List.mem_iff_append.mp later
    have firstPerm : (letters ++ [x]).Perm (x :: x :: (before ++ after)) := by
      have first : (letters ++ [x]).Perm (x :: (before ++ (after ++ [x]))) := by
        simpa [shape,List.append_assoc] using moveToFront x before (after ++ [x])
      have second : (x :: (before ++ (after ++ [x]))).Perm
          (x :: x :: (before ++ after)) := by
        simpa [List.append_assoc] using List.Perm.cons x (moveToFront x (before ++ after) [])
      exact first.trans second
    have first := permuteSquareTail firstPerm h
    have contraction : ListDerives ([h,h] ++ squareList (x :: x :: (before ++ after)))
        ([h,h] ++ squareList (x :: (before ++ after))) := by
      simpa [squareList_cons,List.append_assoc] using
        ((fourthPower x).prepend [h,h]).append (squareList (before ++ after))
    have restore : ListDerives ([h,h] ++ squareList (x :: (before ++ after)))
        ([h,h] ++ squareList letters) := by
      simpa [shape] using (permuteSquareTail (moveToFront x before after) h).symm
    exact first.trans (contraction.trans restore)

theorem appendKnownSquares (h : Nat) (letters extras : List Nat)
    (known : ∀ x ∈ extras, x ∈ h :: letters) :
    ListDerives ([h,h] ++ squareList letters) ([h,h] ++ squareList (letters ++ extras)) := by
  induction extras generalizing letters with
  | nil => simpa using S5_107.ListDerives.refl (basis := basis) ([h,h] ++ squareList letters)
  | cons x xs ih =>
      have first := (contractSeenSquare h letters x (known x (by simp))).symm
      have nextKnown : ∀ y ∈ xs, y ∈ h :: (letters ++ [x]) := by
        intro y member
        have prior := known y (List.mem_cons_of_mem x member)
        rcases List.mem_cons.mp prior with same | old
        · simp [same]
        · exact List.mem_cons_of_mem h (List.mem_append.mpr (Or.inl old))
      simpa [List.append_assoc] using first.trans (ih (letters ++ [x]) nextKnown)

theorem permAppend (xs ys : List Nat) : (xs ++ ys).Perm (ys ++ xs) := by
  induction xs with
  | nil => simpa using List.Perm.refl ys
  | cons x xs ih =>
      have first := List.Perm.cons x ih
      have second := (moveToFront x ys xs).symm
      simpa using first.trans second

/-- Equal content with the same protected first letter suffices for complete
block derivability; no sorting algorithm or hidden canonical field is used. -/
theorem squareBlocks_same_content (h : Nat) (left right : List Nat)
    (same : ∀ x, x ∈ h :: left ↔ x ∈ h :: right) :
    ListDerives (squareList (h :: left)) (squareList (h :: right)) := by
  have addRight := appendKnownSquares h left right
    (fun x member => (same x).mpr (List.mem_cons_of_mem h member))
  have commute := permuteSquareTail (permAppend left right) h
  have addLeft := appendKnownSquares h right left
    (fun x member => (same x).mp (List.mem_cons_of_mem h member))
  exact addRight.trans (commute.trans addLeft.symm)

#print axioms permuteSquareTail
#print axioms contractSeenSquare
#print axioms appendKnownSquares
#print axioms squareBlocks_same_content

end SemigroupBasis.CoRoots.Order6SporadicSection22.E5
