import SemigroupBasis.CoRoots.Order6SporadicSection18CrossingRules

/-! Eliminate a crossing a ... b ... a ... b of nonempty square blocks by
saturating all four to their union, without changing any separating list. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18
open SemigroupBasis

theorem mergeSquareBlocks_to (left right desired gap : List Nat) (x : Nat)
    (inLeft : x ∈ left) (inRight : x ∈ right)
    (same : ∀ y, y ∈ left ++ right ↔ y ∈ desired) :
    ListDerives (squareList left ++ gap ++ squareList right)
      (squareList desired ++ gap ++ squareList desired) := by
  have normalize := squareBlocks_same_content (left ++ right) desired same
  have first := mergeSquareBlocks left right gap x inLeft inRight
  have second : ListDerives
      (squareList (left ++ right) ++ gap ++ squareList (left ++ right))
      (squareList desired ++ gap ++ squareList (left ++ right)) := by
    simpa [List.append_assoc] using normalize.append (gap ++ squareList (left ++ right))
  have third : ListDerives (squareList desired ++ gap ++ squareList (left ++ right))
      (squareList desired ++ gap ++ squareList desired) := by
    simpa [List.append_assoc] using normalize.prepend (squareList desired ++ gap)
  exact first.trans (second.trans third)

/-- The raw crossing may have empty gaps. Nonempty block hypotheses supply
real Word substitutions, never an identity element or an empty word variable. -/
theorem mergeCrossing (left right h k t : List Nat)
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ []) :
    ListDerives (squareList left ++ h ++ squareList right ++ k ++ squareList left ++ t ++ squareList right)
      (squareList (left ++ right) ++ h ++ squareList (left ++ right) ++ k ++
       squareList (left ++ right) ++ t ++ squareList (left ++ right)) := by
  cases left with
  | nil => exact False.elim (leftNonempty rfl)
  | cons x xs =>
    cases right with
    | nil => exact False.elim (rightNonempty rfl)
    | cons y ys =>
      let l := x :: xs
      let r := y :: ys
      let a := squareList l
      let b := squareList r
      let c := squareList (l ++ r)
      let aw : Word Nat := ⟨x, x :: squareList xs⟩
      let bw : Word Nat := ⟨y, y :: squareList ys⟩
      have ha : aw.toList = a := rfl
      have hb : bw.toList = b := rfl
      change ListDerives (a ++ h ++ b ++ k ++ a ++ t ++ b)
        (c ++ h ++ c ++ k ++ c ++ t ++ c)
      have first : ListDerives (a ++ h ++ b ++ k ++ a ++ t ++ b)
          (a ++ h ++ b ++ k ++ a ++ t ++ b ++ a) := by
        simpa only [ha,hb] using appendCrossing aw bw h k t
      have second : ListDerives (a ++ h ++ b ++ k ++ a ++ t ++ b ++ a)
          (b ++ a ++ h ++ b ++ k ++ a ++ t ++ b ++ a) := by
        simpa only [ha,hb,List.append_assoc] using (prependCrossing aw bw h k t).append a
      have firstContent : ∀ z, z ∈ (r ++ l) ++ r ↔ z ∈ l ++ r := by
        intro z
        simp [List.mem_append,or_assoc,or_left_comm,or_comm]
      have third : ListDerives (b ++ a ++ h ++ b ++ k ++ a ++ t ++ b ++ a)
          (c ++ h ++ c ++ k ++ a ++ t ++ b ++ a) := by
        have merged := mergeSquareBlocks_to (r ++ l) r (l ++ r) h y
          (by simp [r]) (by simp [r]) firstContent
        simpa [a,b,c,squareList_append,List.append_assoc] using merged.append (k ++ a ++ t ++ b ++ a)
      have lastContent : ∀ z, z ∈ l ++ (r ++ l) ↔ z ∈ l ++ r := by
        intro z
        simp [List.mem_append,or_assoc,or_left_comm,or_comm]
      have fourth : ListDerives (c ++ h ++ c ++ k ++ a ++ t ++ b ++ a)
          (c ++ h ++ c ++ k ++ c ++ t ++ c) := by
        have merged := mergeSquareBlocks_to l (r ++ l) (l ++ r) t x
          (by simp [l]) (by simp [l]) lastContent
        simpa [a,b,c,squareList_append,List.append_assoc] using merged.prepend (c ++ h ++ c ++ k)
      exact first.trans (second.trans (third.trans fourth))

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.mergeSquareBlocks_to
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.mergeCrossing

end SemigroupBasis.CoRoots.Order6SporadicSection18
