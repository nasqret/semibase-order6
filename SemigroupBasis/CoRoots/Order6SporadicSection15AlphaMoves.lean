import SemigroupBasis.CoRoots.Order6SporadicSection15Derivations

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis

/-! ## List-level moves used in Lemma 15.3

This file stops at the local moves used by the paper's alpha-normalization
argument.  In particular, it does not assert termination of the two repair
procedures or existence of an alpha-canonical representative.
-/

/-- Encode an eliminable paper context as a nonempty semigroup word when the
list is nonempty, and as the corresponding omitted context otherwise. -/
private def optionalListWord : List Nat -> Option (Word Nat)
  | [] => none
  | head :: tail => some (S5_107.listWordOfCons head tail)

@[simp] private theorem appendOptional_optionalListWord_toList
    (stem : Word Nat) (letters : List Nat) :
    (appendOptional stem (optionalListWord letters)).toList =
      stem.toList ++ letters := by
  cases letters with
  | nil =>
      simp [optionalListWord, appendOptional]
  | cons head tail =>
      simp [optionalListWord, appendOptional,
        S5_107.listWordOfCons, Word.toList]

@[simp] private theorem appendOptional_optionalListWord_head_tail_append
    (stem : Word Nat) (letters after : List Nat) :
    (appendOptional stem (optionalListWord letters)).head ::
        ((appendOptional stem (optionalListWord letters)).tail ++ after) =
      stem.head :: (stem.tail ++ letters ++ after) := by
  cases letters with
  | nil =>
      simp [optionalListWord, appendOptional]
  | cons head tail =>
      simp [optionalListWord, appendOptional,
        S5_107.listWordOfCons, Word.toList, List.append_assoc]

/-! ### The three displayed occurrence swaps from (15.1b) -/

/-- Swap the first displayed occurrences in
`x H y K x T y`, under arbitrary outer list context. -/
theorem listDerives15_1bLeftSwap
    (before after : List Nat) (x y : Nat)
    (h k t : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [y] ++ k ++ [x] ++ t ++ [y] ++ after)
      (before ++ [y] ++ h ++ [x] ++ k ++ [x] ++ t ++ [y] ++ after) := by
  have core := S5_107.ListDerives.ofWord
    (derives15_1bLeft
      (Word.singleton x) (Word.singleton y)
      (optionalListWord h) (optionalListWord k) (optionalListWord t))
  simpa [pattern15_1bSource, pattern15_1bLeftTarget,
    Word.toList_append, List.append_assoc] using
      S5_107.ListDerives.context before after core

/-- Swap the middle displayed occurrences in
`x H y K x T y`, under arbitrary outer list context. -/
theorem listDerives15_1bMiddleSwap
    (before after : List Nat) (x y : Nat)
    (h k t : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [y] ++ k ++ [x] ++ t ++ [y] ++ after)
      (before ++ [x] ++ h ++ [x] ++ k ++ [y] ++ t ++ [y] ++ after) := by
  have core := S5_107.ListDerives.ofWord
    (derives15_1bMiddle
      (Word.singleton x) (Word.singleton y)
      (optionalListWord h) (optionalListWord k) (optionalListWord t))
  simpa [pattern15_1bSource, pattern15_1bMiddleTarget,
    Word.toList_append, List.append_assoc] using
      S5_107.ListDerives.context before after core

/-- Swap the last displayed occurrences in
`x H y K x T y`, under arbitrary outer list context. -/
theorem listDerives15_1bRightSwap
    (before after : List Nat) (x y : Nat)
    (h k t : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [y] ++ k ++ [x] ++ t ++ [y] ++ after)
      (before ++ [x] ++ h ++ [y] ++ k ++ [y] ++ t ++ [x] ++ after) := by
  have core := S5_107.ListDerives.ofWord
    (derives15_1bRight
      (Word.singleton x) (Word.singleton y)
      (optionalListWord h) (optionalListWord k) (optionalListWord t))
  simpa [pattern15_1bSource, pattern15_1bRightTarget,
    Word.toList_append, List.append_assoc] using
      S5_107.ListDerives.context before after core

/-- Two adjacent occurrences of globally nonsimple letters can be
interchanged.  The count hypotheses refer to the complete displayed word,
not merely to the block being transposed. -/
theorem listDerivesSwapAdjacentNonsimple
    (stem suffix : List Nat) (left right : Nat)
    (leftNonsimple :
      2 <= (stem ++ (left :: right :: suffix)).count left)
    (rightNonsimple :
      2 <= (stem ++ (left :: right :: suffix)).count right) :
    ListDerives
      (stem ++ [left, right] ++ suffix)
      (stem ++ [right, left] ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl _
  · have leftSide : left ∈ stem ∨ left ∈ suffix := by
      by_cases inPrefix : left ∈ stem
      · exact Or.inl inPrefix
      · right
        apply List.count_pos_iff.mp
        have prefixZero : stem.count left = 0 :=
          List.count_eq_zero.mpr inPrefix
        simp only [List.count_append, List.count_cons_self,
          List.count_cons_of_ne (Ne.symm equal), prefixZero,
          Nat.zero_add] at leftNonsimple
        omega
    have rightSide : right ∈ stem ∨ right ∈ suffix := by
      by_cases inPrefix : right ∈ stem
      · exact Or.inl inPrefix
      · right
        apply List.count_pos_iff.mp
        have prefixZero : stem.count right = 0 :=
          List.count_eq_zero.mpr inPrefix
        simp only [List.count_append,
          List.count_cons_of_ne equal, List.count_cons_self,
          prefixZero, Nat.zero_add] at rightNonsimple
        omega
    rcases leftSide with leftInPrefix | leftInSuffix
    · obtain ⟨leftBefore, leftAfter, prefixSplit⟩ :=
        List.mem_iff_append.mp leftInPrefix
      rcases rightSide with rightInPrefix | rightInSuffix
      · have rightInSplit :
          right ∈ leftBefore ∨ right ∈ leftAfter := by
          rw [prefixSplit] at rightInPrefix
          rcases List.mem_append.mp rightInPrefix with
              beforeMember | afterMember
          · exact Or.inl beforeMember
          · rcases List.mem_cons.mp afterMember with atLeft | inAfter
            · exact False.elim (equal atLeft.symm)
            · exact Or.inr inAfter
        rcases rightInSplit with rightBefore | rightAfter
        · obtain ⟨before, middle, beforeSplit⟩ :=
            List.mem_iff_append.mp rightBefore
          have displayed :=
            listDerives15_1bRightSwap
              before suffix right left middle leftAfter []
          simpa [prefixSplit, beforeSplit, List.append_assoc] using
            displayed.symm
        · obtain ⟨middle, tail, afterSplit⟩ :=
            List.mem_iff_append.mp rightAfter
          simpa [prefixSplit, afterSplit, List.append_assoc] using
            listDerives15_1bRightSwap
              leftBefore suffix left right middle tail []
      · obtain ⟨rightBefore, rightAfter, suffixSplit⟩ :=
          List.mem_iff_append.mp rightInSuffix
        have displayed :=
          listDerives15_1bMiddleSwap
            leftBefore rightAfter left right leftAfter [] rightBefore
        simpa [prefixSplit, suffixSplit, List.append_assoc] using
          displayed.symm
    · obtain ⟨leftBefore, leftAfter, suffixSplit⟩ :=
        List.mem_iff_append.mp leftInSuffix
      rcases rightSide with rightInPrefix | rightInSuffix
      · obtain ⟨rightBefore, rightAfter, prefixSplit⟩ :=
          List.mem_iff_append.mp rightInPrefix
        simpa [prefixSplit, suffixSplit, List.append_assoc] using
          listDerives15_1bMiddleSwap
            rightBefore leftAfter right left rightAfter [] leftBefore
      · have rightInSplit :
          right ∈ leftBefore ∨ right ∈ leftAfter := by
          rw [suffixSplit] at rightInSuffix
          rcases List.mem_append.mp rightInSuffix with
              beforeMember | afterMember
          · exact Or.inl beforeMember
          · rcases List.mem_cons.mp afterMember with atLeft | inAfter
            · exact False.elim (equal atLeft.symm)
            · exact Or.inr inAfter
        rcases rightInSplit with rightBefore | rightAfter
        · obtain ⟨before, middle, beforeSplit⟩ :=
            List.mem_iff_append.mp rightBefore
          have displayed :=
            listDerives15_1bLeftSwap
              stem leftAfter right left [] before middle
          simpa [suffixSplit, beforeSplit, List.append_assoc] using
            displayed.symm
        · obtain ⟨middle, after, afterSplit⟩ :=
            List.mem_iff_append.mp rightAfter
          simpa [suffixSplit, afterSplit, List.append_assoc] using
            listDerives15_1bLeftSwap
              stem after left right [] leftBefore middle

/-- Permute a contiguous block whose letters are all globally nonsimple in
the complete source word.  Duplicating occurrences may lie in either outer
context; they need not lie inside `source`. -/
theorem listDerivesPermuteNonsimpleBlock
    (stem suffix : List Nat) {source target : List Nat}
    (nonsimple :
      ∀ letter, letter ∈ source ->
        2 <= (stem ++ source ++ suffix).count letter)
    (permutation : source.Perm target) :
    ListDerives
      (stem ++ source ++ suffix)
      (stem ++ target ++ suffix) := by
  induction permutation generalizing stem with
  | nil =>
      exact S5_107.ListDerives.refl _
  | cons head permutation induction =>
      have derivation := induction (stem ++ [head]) (by
        intro letter member
        have bound := nonsimple letter (List.Mem.tail head member)
        simpa [List.append_assoc] using bound)
      simpa [List.append_assoc] using derivation
  | swap first second rest =>
      have secondBound := nonsimple second (by simp)
      have firstBound := nonsimple first (by simp)
      simpa [List.append_assoc] using
        listDerivesSwapAdjacentNonsimple
          stem (rest ++ suffix) second first
            (by simpa [List.append_assoc] using secondBound)
            (by simpa [List.append_assoc] using firstBound)
  | @trans source middle target firstPermutation _
      firstInduction secondInduction =>
      have firstDerivation := firstInduction stem nonsimple
      have middleNonsimple :
          ∀ letter, letter ∈ middle ->
            2 <= (stem ++ middle ++ suffix).count letter := by
        intro letter member
        have sourceMember : letter ∈ source :=
          (firstPermutation.mem_iff).mpr member
        have bound := nonsimple letter sourceMember
        have countEq : source.count letter = middle.count letter :=
          List.perm_iff_count.mp firstPermutation letter
        simpa [List.count_append, countEq] using bound
      exact firstDerivation.trans
        (secondInduction stem middleNonsimple)

/-! ### The two adjacent-square repairs in the proof of Lemma 15.3 -/

/-- Paper Case 1: a nonempty factor after `x^2` is moved between the two
copies of `x`; the two displayed copies of `y` remain fixed. -/
theorem listDerivesAlphaRepairCase1
    (before after betweenY gapTail : List Nat)
    (x y gapHead : Nat) :
    ListDerives
      (before ++ [x, x] ++ (gapHead :: gapTail) ++
        [y] ++ betweenY ++ [y] ++ after)
      (before ++ [x] ++ (gapHead :: gapTail) ++
        [x, y] ++ betweenY ++ [y] ++ after) := by
  have core := S5_107.ListDerives.ofWord
    (derives15_1cLeft
      (Word.singleton x) (Word.singleton y)
      (S5_107.listWordOfCons gapHead gapTail)
      (optionalListWord betweenY))
  simpa [pattern15_1cLeftSource, pattern15_1cLeftTarget,
    S5_107.listWordOfCons, Word.toList, Word.toList_append,
    List.append_assoc] using
      S5_107.ListDerives.context before after core

/-- Paper Case 2: a nonempty factor between the two copies of `y` is moved
left across their first copy, making `y^2`; the two copies of `x` stay fixed. -/
theorem listDerivesAlphaRepairCase2
    (before after betweenX gapTail : List Nat)
    (x y gapHead : Nat) :
    ListDerives
      (before ++ [x] ++ betweenX ++ [x, y] ++
        (gapHead :: gapTail) ++ [y] ++ after)
      (before ++ [x] ++ betweenX ++ [x] ++
        (gapHead :: gapTail) ++ [y, y] ++ after) := by
  have core := S5_107.ListDerives.ofWord
    ((derives15_1dLeft
      (Word.singleton x) (Word.singleton y)
      (S5_107.listWordOfCons gapHead gapTail)
      (optionalListWord betweenX)).symm)
  simpa [pattern15_1dLeftSource, pattern15_1dLeftTarget,
    S5_107.listWordOfCons, Word.toList, Word.toList_append,
    List.append_assoc] using
      S5_107.ListDerives.context before after core

/-! ### Anchored alpha-unit transpositions from (15.1e) -/

/-- Forward placement of (15.1e).  The two blocks are explicitly nonempty,
while the factor between the two copies of `rightAnchor` may be empty. -/
theorem listDerivesAlphaUnitSwapForward
    (before after optionalMiddle leftTail rightTail : List Nat)
    (leftAnchor rightAnchor leftHead rightHead : Nat) :
    ListDerives
      (before ++ [leftAnchor] ++ (leftHead :: leftTail) ++
        [leftAnchor] ++ (rightHead :: rightTail) ++
        [rightAnchor] ++ optionalMiddle ++ [rightAnchor] ++ after)
      (before ++ [leftAnchor] ++ (rightHead :: rightTail) ++
        [leftAnchor] ++ (leftHead :: leftTail) ++
        [rightAnchor] ++ optionalMiddle ++ [rightAnchor] ++ after) := by
  have core := S5_107.ListDerives.ofWord
    (derives15_1eForward
      (S5_107.listWordOfCons leftHead leftTail)
      (S5_107.listWordOfCons rightHead rightTail)
      (Word.singleton leftAnchor) (Word.singleton rightAnchor)
      (optionalListWord optionalMiddle))
  simpa [pattern15_1eForwardSource, pattern15_1eForwardTarget,
    S5_107.listWordOfCons, Word.toList, Word.toList_append,
    List.append_assoc] using
      S5_107.ListDerives.context before after core

/-- Reverse placement of (15.1e).  This is the symmetric alpha-unit
transposition when the auxiliary repeated anchor lies to the left. -/
theorem listDerivesAlphaUnitSwapReverse
    (before after optionalMiddle leftTail rightTail : List Nat)
    (leftAnchor rightAnchor leftHead rightHead : Nat) :
    ListDerives
      (before ++ [leftAnchor] ++ optionalMiddle ++ [leftAnchor] ++
        (leftHead :: leftTail) ++ [rightAnchor] ++
        (rightHead :: rightTail) ++ [rightAnchor] ++ after)
      (before ++ [leftAnchor] ++ optionalMiddle ++ [leftAnchor] ++
        (rightHead :: rightTail) ++ [rightAnchor] ++
        (leftHead :: leftTail) ++ [rightAnchor] ++ after) := by
  have core := S5_107.ListDerives.ofWord
    (derives15_1eReverse
      (S5_107.listWordOfCons leftHead leftTail)
      (S5_107.listWordOfCons rightHead rightTail)
      (Word.singleton rightAnchor) (Word.singleton leftAnchor)
      (optionalListWord optionalMiddle))
  simpa [pattern15_1eReverseSource, pattern15_1eReverseTarget,
    S5_107.listWordOfCons, Word.toList, Word.toList_append,
    List.append_assoc] using
      S5_107.ListDerives.context before after core

end SemigroupBasis.CoRoots.Order6SporadicSection15
