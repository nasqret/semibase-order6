import SemigroupBasis.CoRoots.Order6SporadicSection17C10Squares

/-! The algebraic comparison step of Lemma17.9. Different terminal letters
may be exchanged ONLY when both occur in the retained suffix. This is the
explicit boundary needed by the last-to-simple detector, not cancellation. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
open SemigroupBasis

theorem permuteBeforeSeen {left right : List Nat} (permutation : left.Perm right)
    (suffix : List Nat) (seen : ∀ x ∈ left, x ∈ suffix) :
    ListDerives (left ++ suffix) (right ++ suffix) := by
  induction permutation with
  | nil => exact S5_107.ListDerives.refl _
  | cons x permutation ih =>
      have later := ih (fun y member => seen y (List.mem_cons_of_mem x member))
      simpa using later.prepend [x]
  | swap x y rest =>
      have hx : x ∈ suffix := seen x (by simp)
      have hy : y ∈ suffix := seen y (by simp)
      simpa [List.append_assoc] using
        (swapBeforeSeen x y (rest ++ suffix)
          (List.mem_append.mpr (Or.inr hx)) (List.mem_append.mpr (Or.inr hy))).symm
  | trans first second ihFirst ihSecond =>
      exact (ihFirst seen).trans
        (ihSecond (fun x member => seen x (first.mem_iff.mpr member)))

theorem swapSquaresBeforeSeen (x y : Nat) (suffix : List Nat)
    (hx : x ∈ suffix) (hy : y ∈ suffix) :
    ListDerives ([x,x,y,y] ++ suffix) ([y,y,x,x] ++ suffix) := by
  have seen : ∀ z ∈ [x,x,y,y], z ∈ suffix := by
    intro z member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact hx
    · exact hx
    · exact hy
    · exact hy
  exact permuteBeforeSeen (permAppend [x,x] [y,y]) suffix seen

theorem changeLastSquare (x y : Nat) (left suffix : List Nat)
    (yPresent : y ∈ left ++ [x]) (hx : x ∈ suffix) (hy : y ∈ suffix) :
    ListDerives ((squareList left ++ [x,x]) ++ suffix)
      ((squareList (left ++ [x]) ++ [y,y]) ++ suffix) := by
  have addY := prependKnownSquares x left [y] (by
    intro z member
    have equal : z = y := by simpa using member
    simpa [equal] using yPresent)
  have moveY := permuteSquarePrefix (permAppend [y] left) x
  have first : ListDerives ((squareList left ++ [x,x]) ++ suffix)
      (squareList left ++ ([y,y,x,x] ++ suffix)) := by
    simpa [squareList_append,squareList_cons,squareList_nil,List.append_assoc] using
      (addY.trans moveY).append suffix
  have second : ListDerives (squareList left ++ ([y,y,x,x] ++ suffix))
      ((squareList (left ++ [x]) ++ [y,y]) ++ suffix) := by
    simpa [squareList_append,squareList_cons,squareList_nil,List.append_assoc] using
      (swapSquaresBeforeSeen y x suffix hy hx).prepend (squareList left)
  exact first.trans second

/-- Complete block replay under exactly the alternative supplied by the
semantic boundary: equal last letters, or both genuinely recur later. -/
theorem squareBlocks_replay_with_suffix (x y : Nat) (left right suffix : List Nat)
    (same : ∀ z, z ∈ left ++ [x] ↔ z ∈ right ++ [y])
    (lasts : x = y ∨ (x ∈ suffix ∧ y ∈ suffix)) :
    ListDerives ((squareList left ++ [x,x]) ++ suffix)
      ((squareList right ++ [y,y]) ++ suffix) := by
  rcases lasts with sameLast | ⟨hx,hy⟩
  · subst y
    exact (squareBlocks_same_content x left right same).append suffix
  · have yPresent : y ∈ left ++ [x] := (same y).mpr (by simp)
    have first := changeLastSquare x y left suffix yPresent hx hy
    have content : ∀ z, z ∈ (left ++ [x]) ++ [y] ↔ z ∈ right ++ [y] := by
      intro z
      constructor
      · intro member
        rcases List.mem_append.mp member with old | final
        · exact (same z).mp old
        · exact List.mem_append.mpr (Or.inr final)
      · intro member
        exact List.mem_append.mpr (Or.inl ((same z).mpr member))
    exact first.trans ((squareBlocks_same_content y (left ++ [x]) right content).append suffix)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.permuteBeforeSeen
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.swapSquaresBeforeSeen
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.changeLastSquare
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.squareBlocks_replay_with_suffix

end SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
