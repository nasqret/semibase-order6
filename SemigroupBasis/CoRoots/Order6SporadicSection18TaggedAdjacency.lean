import SemigroupBasis.CoRoots.Order6SporadicSection18TagSubstitution

/-! Identify the blocks immediately before and after a canonical simple gap.
Actual word substitution is connected to the fully proved tagged witnesses,
then BY's literal block-set theorem distinguishes the selected block labels. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open Actual

theorem tagged_sameEval_forces_marked_eq {left right leftAlphabet rightAlphabet : List Nat}
    {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (leftWitness : CanonicalWitness left leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right rightAlphabet rightFirst rightRest)
    (a b : List Nat) (aPresent : BlockOccurs a (leftFirst :: leftRest))
    (bPresent : BlockOccurs b (rightFirst :: rightRest))
    (same : SameEval (render ((leftFirst :: leftRest).map (tagSlot a)))
      (render ((rightFirst :: rightRest).map (tagSlot b)))) : a = b := by
  have leftTagged := leftWitness.tag a aPresent
  have rightTagged := rightWitness.tag b bPresent
  obtain ⟨slot, member, blockEqual⟩ := aPresent
  have taggedPresent : BlockOccurs (tagBlock a a) ((leftFirst :: leftRest).map (tagSlot a)) := by
    refine ⟨tagSlot a slot, List.mem_map.mpr ⟨slot, member, rfl⟩, ?_⟩
    change tagBlock a slot.block = tagBlock a a
    rw [blockEqual]
  have matching := (leftTagged.same_block_sets rightTagged same (tagBlock a a)).mp taggedPresent
  obtain ⟨tagged, taggedMember, equal⟩ := matching
  change tagged ∈ (rightFirst :: rightRest).map (tagSlot b) at taggedMember
  obtain ⟨original, _, taggedEqual⟩ := List.mem_map.mp taggedMember
  subst tagged
  change tagBlock b original.block = tagBlock a a at equal
  have zeroPresent : 0 ∈ tagBlock b original.block := by
    rw [equal]
    exact (tagBlock_zero_mem a a).mpr rfl
  have selected := (tagBlock_zero_mem b original.block).mp zeroPresent
  have decoded : original.block = a := by
    simpa only [decode_tagBlock] using congrArg decodeBlock equal
  exact decoded.symm.trans selected

theorem CanonicalWitness.tag_after_last_gap {whole alphabet : List Nat} {first : Slot} {rest : List Slot}
    (witness : CanonicalWitness whole alphabet first rest)
    (before : List Slot) (slot : Slot) (after : List Slot)
    (shape : first :: rest = before ++ slot :: after) (gapHead : List Nat) (marker : Nat)
    (gapShape : slot.gap = gapHead ++ [marker]) :
    SameEval (render ((first :: rest).map (tagSlot slot.block))) (taggedWord false marker whole) := by
  have member : slot ∈ first :: rest := by rw [shape]; simp
  have nonempty := (witness.2.2.2.2.2.2.2.1.1 slot member).1
  have simple := witness.gap_simple slot member marker (by rw [gapShape]; simp)
  have rendered := witness.2.2.2.2.2.2.2.2
  have wordShape : whole = (render before ++ gapHead) ++ marker :: (squareList slot.block ++ render after) := by
    rw [shape, render_append] at rendered
    simpa only [render, gapShape, List.append_assoc, List.cons_append, List.nil_append] using rendered.symm
  have singleEqual : singleTaggedWord slot.block before slot after = taggedWord false marker whole := by
    rw [taggedWord_unique false marker whole (render before ++ gapHead)
      (squareList slot.block ++ render after) wordShape simple]
    simp [singleTaggedWord, gapShape, tagBlock, tagLetter, squareList_cons,
      squareList_shift, List.map_append, List.append_assoc]
  have one := tag_all_sameEval_single slot.block nonempty before slot after rfl
  rw [← shape, singleEqual] at one
  exact one

theorem CanonicalWitness.tag_before_first_gap {whole alphabet : List Nat} {first : Slot} {rest : List Slot}
    (witness : CanonicalWitness whole alphabet first rest)
    (before : List Slot) (slot next : Slot) (after : List Slot)
    (shape : first :: rest = before ++ slot :: next :: after) (marker : Nat) (gapTail : List Nat)
    (gapShape : next.gap = marker :: gapTail) :
    SameEval (render ((first :: rest).map (tagSlot slot.block))) (taggedWord true marker whole) := by
  have member : slot ∈ first :: rest := by rw [shape]; simp
  have nextMember : next ∈ first :: rest := by rw [shape]; simp
  have nonempty := (witness.2.2.2.2.2.2.2.1.1 slot member).1
  have simple := witness.gap_simple next nextMember marker (by rw [gapShape]; simp)
  have rendered := witness.2.2.2.2.2.2.2.2
  have wordShape : whole = (render before ++ slot.gap ++ squareList slot.block) ++
      marker :: (gapTail ++ squareList next.block ++ render after) := by
    rw [shape, render_append] at rendered
    simpa only [render, gapShape, List.append_assoc, List.cons_append] using rendered.symm
  have suffixEqual : (render before).map Nat.succ ++ slot.gap.map Nat.succ ++
      (squareList slot.block).map Nat.succ ++ [0, 0] ++ (render (next :: after)).map Nat.succ =
      taggedWord true marker whole := by
    rw [taggedWord_unique true marker whole (render before ++ slot.gap ++ squareList slot.block)
      (gapTail ++ squareList next.block ++ render after) wordShape simple]
    simp [render, gapShape, tagLetter, List.map_append, List.append_assoc]
  have one := tag_all_sameEval_single slot.block nonempty before slot (next :: after) rfl
  rw [← shape] at one
  have suffix := singleTaggedWord_sameEval_suffix slot.block nonempty before slot (next :: after) rfl
  rw [suffixEqual] at suffix
  exact one.trans suffix

theorem CanonicalWitness.same_following_block {left right leftAlphabet rightAlphabet : List Nat}
    {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (leftWitness : CanonicalWitness left leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right rightAlphabet rightFirst rightRest)
    (same : SameEval left right)
    (leftBefore : List Slot) (leftSlot : Slot) (leftAfter : List Slot)
    (rightBefore : List Slot) (rightSlot : Slot) (rightAfter : List Slot)
    (leftShape : leftFirst :: leftRest = leftBefore ++ leftSlot :: leftAfter)
    (rightShape : rightFirst :: rightRest = rightBefore ++ rightSlot :: rightAfter)
    (leftGapHead rightGapHead : List Nat) (marker : Nat)
    (leftGap : leftSlot.gap = leftGapHead ++ [marker])
    (rightGap : rightSlot.gap = rightGapHead ++ [marker]) : leftSlot.block = rightSlot.block := by
  have leftTagged := leftWitness.tag_after_last_gap leftBefore leftSlot leftAfter leftShape leftGapHead marker leftGap
  have rightTagged := rightWitness.tag_after_last_gap rightBefore rightSlot rightAfter rightShape rightGapHead marker rightGap
  apply tagged_sameEval_forces_marked_eq leftWitness rightWitness leftSlot.block rightSlot.block
    ⟨leftSlot, by rw [leftShape]; simp, rfl⟩ ⟨rightSlot, by rw [rightShape]; simp, rfl⟩
  exact leftTagged.trans ((same.taggedWord false marker).trans rightTagged.symm)

theorem CanonicalWitness.same_preceding_block {left right leftAlphabet rightAlphabet : List Nat}
    {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (leftWitness : CanonicalWitness left leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right rightAlphabet rightFirst rightRest)
    (same : SameEval left right)
    (leftBefore : List Slot) (leftSlot leftNext : Slot) (leftAfter : List Slot)
    (rightBefore : List Slot) (rightSlot rightNext : Slot) (rightAfter : List Slot)
    (leftShape : leftFirst :: leftRest = leftBefore ++ leftSlot :: leftNext :: leftAfter)
    (rightShape : rightFirst :: rightRest = rightBefore ++ rightSlot :: rightNext :: rightAfter)
    (marker : Nat) (leftGapTail rightGapTail : List Nat)
    (leftGap : leftNext.gap = marker :: leftGapTail)
    (rightGap : rightNext.gap = marker :: rightGapTail) : leftSlot.block = rightSlot.block := by
  have leftTagged := leftWitness.tag_before_first_gap leftBefore leftSlot leftNext leftAfter leftShape marker leftGapTail leftGap
  have rightTagged := rightWitness.tag_before_first_gap rightBefore rightSlot rightNext rightAfter rightShape marker rightGapTail rightGap
  apply tagged_sameEval_forces_marked_eq leftWitness rightWitness leftSlot.block rightSlot.block
    ⟨leftSlot, by rw [leftShape]; simp, rfl⟩ ⟨rightSlot, by rw [rightShape]; simp, rfl⟩
  exact leftTagged.trans ((same.taggedWord true marker).trans rightTagged.symm)

theorem CanonicalWitness.same_block_after_equal_gap {left right leftAlphabet rightAlphabet : List Nat}
    {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (leftWitness : CanonicalWitness left leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right rightAlphabet rightFirst rightRest)
    (same : SameEval left right) (leftSlot rightSlot : Slot)
    (leftMember : leftSlot ∈ leftRest) (rightMember : rightSlot ∈ rightRest)
    (gapEqual : leftSlot.gap = rightSlot.gap) : leftSlot.block = rightSlot.block := by
  have nonempty := leftWitness.2.2.2.2.2.1 leftSlot leftMember
  have reverseNonempty : leftSlot.gap.reverse ≠ [] := by simpa using nonempty
  obtain ⟨marker, reversed, reverseShape⟩ := List.exists_cons_of_ne_nil reverseNonempty
  have leftGap : leftSlot.gap = reversed.reverse ++ [marker] := by
    simpa only [List.reverse_reverse, List.reverse_cons] using congrArg List.reverse reverseShape
  have rightGap := gapEqual.symm.trans leftGap
  obtain ⟨leftBefore, leftAfter, leftShape⟩ := List.mem_iff_append.mp (List.Mem.tail leftFirst leftMember)
  obtain ⟨rightBefore, rightAfter, rightShape⟩ := List.mem_iff_append.mp (List.Mem.tail rightFirst rightMember)
  exact leftWitness.same_following_block rightWitness same leftBefore leftSlot leftAfter
    rightBefore rightSlot rightAfter leftShape rightShape reversed.reverse reversed.reverse marker leftGap rightGap

theorem CanonicalWitness.same_block_before_equal_gap {left right leftAlphabet rightAlphabet : List Nat}
    {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (leftWitness : CanonicalWitness left leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right rightAlphabet rightFirst rightRest)
    (same : SameEval left right)
    (leftBefore : List Slot) (leftSlot leftNext : Slot) (leftAfter : List Slot)
    (rightBefore : List Slot) (rightSlot rightNext : Slot) (rightAfter : List Slot)
    (leftShape : leftFirst :: leftRest = leftBefore ++ leftSlot :: leftNext :: leftAfter)
    (rightShape : rightFirst :: rightRest = rightBefore ++ rightSlot :: rightNext :: rightAfter)
    (gapEqual : leftNext.gap = rightNext.gap) : leftSlot.block = rightSlot.block := by
  have prefixShape : leftFirst :: leftRest = (leftBefore ++ [leftSlot]) ++ leftNext :: leftAfter := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using leftShape
  have nonempty := leftWitness.noninitial_gap_nonempty (leftBefore ++ [leftSlot]) leftNext leftAfter
    prefixShape (by simp)
  obtain ⟨marker, gapTail, leftGap⟩ := List.exists_cons_of_ne_nil nonempty
  have rightGap := gapEqual.symm.trans leftGap
  exact leftWitness.same_preceding_block rightWitness same leftBefore leftSlot leftNext leftAfter
    rightBefore rightSlot rightNext rightAfter leftShape rightShape marker gapTail gapTail leftGap rightGap

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.tagged_sameEval_forces_marked_eq
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.tag_after_last_gap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.tag_before_first_gap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.same_following_block
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.same_preceding_block
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.same_block_after_equal_gap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.same_block_before_equal_gap

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
