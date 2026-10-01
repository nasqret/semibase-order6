import SemigroupBasis.CoRoots.Order6SporadicSection17C10Derivations

/-! Square blocks with a protected LAST letter. This is not unguarded
commutation: every swap retains a real following square, as in17.2b. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
open SemigroupBasis

def squareList (letters : List Nat) : List Nat := letters.flatMap (fun x => [x,x])

theorem squareList_nil : squareList [] = [] := rfl
theorem squareList_cons (x : Nat) (xs : List Nat) :
    squareList (x :: xs) = [x,x] ++ squareList xs := rfl
theorem squareList_append (xs ys : List Nat) :
    squareList (xs ++ ys) = squareList xs ++ squareList ys := List.flatMap_append

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

theorem swapBeforeSquareBlock (x y h : Nat) (rest : List Nat) :
    ListDerives (squareList (x :: y :: rest) ++ [h,h])
      (squareList (y :: x :: rest) ++ [h,h]) := by
  cases rest with
  | nil => exact swapProtectedSquares x y h
  | cons z zs =>
      simpa [squareList_cons,List.append_assoc] using
        (swapProtectedSquares x y z).append (squareList zs ++ [h,h])

theorem permuteSquarePrefix {left right : List Nat} (permutation : left.Perm right) (h : Nat) :
    ListDerives (squareList left ++ [h,h]) (squareList right ++ [h,h]) := by
  induction permutation with
  | nil => exact S5_107.ListDerives.refl _
  | cons x permutation ih =>
      simpa [squareList_cons,List.append_assoc] using ih.prepend [x,x]
  | swap x y rest => exact (swapBeforeSquareBlock x y h rest).symm
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

theorem contractSeenSquare (h : Nat) (letters : List Nat) (x : Nat)
    (seen : x ∈ letters ++ [h]) :
    ListDerives (squareList (x :: letters) ++ [h,h]) (squareList letters ++ [h,h]) := by
  rcases List.mem_append.mp seen with earlier | last
  · obtain ⟨before,after,shape⟩ := List.mem_iff_append.mp earlier
    have permutation : (x :: letters).Perm (x :: x :: (before ++ after)) := by
      simpa [shape] using List.Perm.cons x (moveToFront x before after)
    have first := permuteSquarePrefix permutation h
    have contraction : ListDerives (squareList (x :: x :: (before ++ after)) ++ [h,h])
        (squareList (x :: (before ++ after)) ++ [h,h]) := by
      simpa [squareList_cons,List.append_assoc] using
        (fourthPower x).append (squareList (before ++ after) ++ [h,h])
    have restore : ListDerives (squareList (x :: (before ++ after)) ++ [h,h])
        (squareList letters ++ [h,h]) := by
      simpa [shape] using (permuteSquarePrefix (moveToFront x before after) h).symm
    exact first.trans (contraction.trans restore)
  · have equal : x = h := by simpa using last
    subst x
    have first : ListDerives (squareList (h :: letters) ++ [h,h])
        (squareList letters ++ [h,h,h,h]) := by
      simpa [squareList_append,squareList_cons,squareList_nil,List.append_assoc] using
        permuteSquarePrefix (permAppend [h] letters) h
    exact first.trans ((fourthPower h).prepend (squareList letters))

theorem prependKnownSquares (h : Nat) (letters extras : List Nat)
    (known : ∀ x ∈ extras, x ∈ letters ++ [h]) :
    ListDerives (squareList letters ++ [h,h]) (squareList (extras ++ letters) ++ [h,h]) := by
  induction extras with
  | nil => exact S5_107.ListDerives.refl _
  | cons x xs ih =>
      have first := ih (fun y member => known y (List.mem_cons_of_mem x member))
      have seen : x ∈ (xs ++ letters) ++ [h] := by
        have prior := known x (by simp)
        simpa only [List.mem_append,or_assoc] using
          (Or.inr prior : x ∈ xs ∨ x ∈ letters ++ [h])
      simpa using first.trans (contractSeenSquare h (xs ++ letters) x seen).symm

/-- Equal contents with the same last square give unrestricted block replay. -/
theorem squareBlocks_same_content (h : Nat) (left right : List Nat)
    (same : ∀ x, x ∈ left ++ [h] ↔ x ∈ right ++ [h]) :
    ListDerives (squareList left ++ [h,h]) (squareList right ++ [h,h]) := by
  have addRight := prependKnownSquares h left right
    (fun x member => (same x).mpr (List.mem_append.mpr (Or.inl member)))
  have commute := permuteSquarePrefix (permAppend right left) h
  have addLeft := prependKnownSquares h right left
    (fun x member => (same x).mp (List.mem_append.mpr (Or.inl member)))
  exact addRight.trans (commute.trans addLeft.symm)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.permuteSquarePrefix
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.contractSeenSquare
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.prependKnownSquares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.squareBlocks_same_content

end SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
