import SemigroupBasis.CoRoots.Order6SporadicSection18BlockNormalization

/-! The unrestricted square-block merging move needed by Lemmas18.4–18.6.
Only a shared letter is required; the separating list may be arbitrary. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18
open SemigroupBasis

private def three (h x y : Word Nat) : Nat → Word Nat
  | 0 => h
  | 1 => x
  | _ => y

theorem wordSquareSwap (a b : Word Nat) :
    ListDerives (a.toList ++ a.toList ++ b.toList ++ b.toList)
      (b.toList ++ b.toList ++ a.toList ++ a.toList) := by
  have raw : ListDerives (lawSquare.lhs.bind (three a b a)).toList
      (lawSquare.rhs.bind (three a b a)).toList := S5_107.ListDerives.ofWord
    (Derives.subst (Derives.fromBasis (e := lawSquare) (by decide)) (three a b a))
  simpa [lawSquare,three,Word.bind,Word.toList,Word.append,List.append_assoc] using raw

theorem slideWordSquare (h x y : Word Nat) :
    ListDerives (h.toList ++ x.toList ++ x.toList ++ y.toList ++ h.toList)
      (h.toList ++ y.toList ++ x.toList ++ x.toList ++ h.toList) := by
  have raw : ListDerives (law04.lhs.bind (three h x y)).toList
      (law04.rhs.bind (three h x y)).toList := S5_107.ListDerives.ofWord
    (Derives.subst (Derives.fromBasis (e := law04) (by decide)) (three h x y))
  simpa [law04,three,Word.bind,Word.toList,Word.append,List.append_assoc] using raw

theorem reverseThreeSquares (a b : Word Nat) (x : Nat) :
    ListDerives (a.toList ++ a.toList ++ [x,x] ++ b.toList ++ b.toList)
      (b.toList ++ b.toList ++ [x,x] ++ a.toList ++ a.toList) := by
  have first : ListDerives (a.toList ++ a.toList ++ [x,x] ++ b.toList ++ b.toList)
      ([x,x] ++ a.toList ++ a.toList ++ b.toList ++ b.toList) := by
    simpa [Word.singleton,Word.toList,List.append_assoc] using
      (wordSquareSwap a (Word.singleton x)).append (b.toList ++ b.toList)
  have second : ListDerives ([x,x] ++ a.toList ++ a.toList ++ b.toList ++ b.toList)
      ([x,x] ++ b.toList ++ b.toList ++ a.toList ++ a.toList) := by
    simpa [List.append_assoc] using (wordSquareSwap a b).prepend [x,x]
  have third : ListDerives ([x,x] ++ b.toList ++ b.toList ++ a.toList ++ a.toList)
      (b.toList ++ b.toList ++ [x,x] ++ a.toList ++ a.toList) := by
    simpa [Word.singleton,Word.toList,List.append_assoc] using
      (wordSquareSwap (Word.singleton x) b).append (a.toList ++ a.toList)
  exact first.trans (second.trans third)

private theorem wordOfNonempty (letters : List Nat) (nonempty : letters ≠ []) :
    ∃ w : Word Nat, w.toList = letters := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons h t => exact ⟨⟨h,t⟩,rfl⟩

/-- Two square blocks sharing a letter may both be saturated to their union.
The proof keeps real nonempty substitutions even when the gap is empty. -/
theorem mergeSquareBlocks (left right gap : List Nat) (x : Nat)
    (inLeft : x ∈ left) (inRight : x ∈ right) :
    ListDerives (squareList left ++ gap ++ squareList right)
      (squareList (left ++ right) ++ gap ++ squareList (left ++ right)) := by
  let a := squareList left
  let b := squareList right
  let c := squareList (left ++ right)
  have aMember : x ∈ a := (squareList_mem left x).mpr inLeft
  have bMember : x ∈ b := (squareList_mem right x).mpr inRight
  obtain ⟨aw,ha⟩ := wordOfNonempty a (by
    intro empty
    rw [empty] at aMember
    exact List.not_mem_nil aMember)
  obtain ⟨bw,hb⟩ := wordOfNonempty b (by
    intro empty
    rw [empty] at bMember
    exact List.not_mem_nil bMember)
  have gapMember : x ∈ gap ++ b := List.mem_append.mpr (Or.inr bMember)
  obtain ⟨gw,hg⟩ := wordOfNonempty (gap ++ b) (by
    intro empty
    rw [empty] at gapMember
    exact List.not_mem_nil gapMember)
  let hw : Word Nat := ⟨x,[x]⟩
  have hh : hw.toList = [x,x] := rfl

  have leftExpand : ListDerives a (a ++ [x,x] ++ a ++ a) := by
    have content : ∀ y, y ∈ left ↔ y ∈ left ++ [x] ++ left ++ left := by
      intro y
      by_cases same : y = x
      · subst y
        simp [inLeft]
      · simp [same,List.mem_append,or_assoc]
    simpa [a,squareList_append,squareList_cons,squareList_nil,List.append_assoc] using
      squareBlocks_same_content left (left ++ [x] ++ left ++ left) content
  have rightExpand : ListDerives b (b ++ [x,x] ++ b ++ b) := by
    have content : ∀ y, y ∈ right ↔ y ∈ right ++ [x] ++ right ++ right := by
      intro y
      by_cases same : y = x
      · subst y
        simp [inRight]
      · simp [same,List.mem_append,or_assoc]
    simpa [b,squareList_append,squareList_cons,squareList_nil,List.append_assoc] using
      squareBlocks_same_content right (right ++ [x] ++ right ++ right) content
  have first : ListDerives (a ++ gap ++ b) (a ++ [x,x] ++ a ++ a ++ gap ++ b) := by
    simpa [List.append_assoc] using leftExpand.append (gap ++ b)
  have second : ListDerives (a ++ [x,x] ++ a ++ a ++ gap ++ b)
      (a ++ [x,x] ++ a ++ a ++ gap ++ b ++ [x,x] ++ b ++ b) := by
    simpa [List.append_assoc] using rightExpand.prepend (a ++ [x,x] ++ a ++ a ++ gap)
  have third : ListDerives (a ++ [x,x] ++ a ++ a ++ gap ++ b ++ [x,x] ++ b ++ b)
      (a ++ [x,x] ++ gap ++ b ++ a ++ a ++ [x,x] ++ b ++ b) := by
    simpa only [ha,hg,hh,List.append_assoc] using (slideWordSquare hw aw gw).context a (b ++ b)
  have fourth : ListDerives (a ++ [x,x] ++ gap ++ b ++ a ++ a ++ [x,x] ++ b ++ b)
      (a ++ [x,x] ++ gap ++ b ++ b ++ b ++ [x,x] ++ a ++ a) := by
    simpa only [ha,hb,List.append_assoc] using
      (reverseThreeSquares aw bw x).prepend (a ++ [x,x] ++ gap ++ b)
  have fifth : ListDerives (a ++ [x,x] ++ gap ++ b ++ b ++ b ++ [x,x] ++ a ++ a)
      (a ++ [x,x] ++ b ++ b ++ gap ++ b ++ [x,x] ++ a ++ a) := by
    simpa only [hb,hg,hh,List.append_assoc] using (slideWordSquare hw bw gw).symm.context a (a ++ a)

  have normalizeLeft : ListDerives (a ++ [x,x] ++ b ++ b) c := by
    have content : ∀ y, y ∈ left ++ [x] ++ right ++ right ↔ y ∈ left ++ right := by
      intro y
      by_cases same : y = x
      · subst y
        simp [inLeft,inRight]
      · simp [same,List.mem_append,or_assoc,or_left_comm,or_comm]
    simpa [a,b,c,squareList_append,squareList_cons,squareList_nil,List.append_assoc] using
      squareBlocks_same_content (left ++ [x] ++ right ++ right) (left ++ right) content
  have normalizeRight : ListDerives (b ++ [x,x] ++ a ++ a) c := by
    have content : ∀ y, y ∈ right ++ [x] ++ left ++ left ↔ y ∈ left ++ right := by
      intro y
      by_cases same : y = x
      · subst y
        simp [inLeft,inRight]
      · simp [same,List.mem_append,or_assoc,or_left_comm,or_comm]
    simpa [a,b,c,squareList_append,squareList_cons,squareList_nil,List.append_assoc] using
      squareBlocks_same_content (right ++ [x] ++ left ++ left) (left ++ right) content
  have sixth : ListDerives (a ++ [x,x] ++ b ++ b ++ gap ++ b ++ [x,x] ++ a ++ a)
      (c ++ gap ++ b ++ [x,x] ++ a ++ a) := by
    simpa [List.append_assoc] using normalizeLeft.append (gap ++ b ++ [x,x] ++ a ++ a)
  have seventh : ListDerives (c ++ gap ++ b ++ [x,x] ++ a ++ a) (c ++ gap ++ c) := by
    simpa [List.append_assoc] using normalizeRight.prepend (c ++ gap)
  exact first.trans (second.trans (third.trans (fourth.trans (fifth.trans (sixth.trans seventh)))))

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.wordSquareSwap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.slideWordSquare
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.reverseThreeSquares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.mergeSquareBlocks

end SemigroupBasis.CoRoots.Order6SporadicSection18
