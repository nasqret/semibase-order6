import SemigroupBasis.CoRoots.Order6SporadicSection18MarkedWindow

/-! Actual C7 semantics preserves the canonical nonsimple-block partition.
The extremal-window orientation and ONE global marked valuation rule out mixing;
the argument in both directions then identifies the literal sorted block lists. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

theorem ordered_nat_lists_eq (left right : List Nat)
    (leftOrdered : left.Pairwise (· < ·)) (rightOrdered : right.Pairwise (· < ·))
    (same : ∀ x, x ∈ left ↔ x ∈ right) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          exact False.elim (List.not_mem_nil ((same head).mpr (List.Mem.head tail)))
  | cons head tail ih =>
      cases right with
      | nil => exact False.elim (List.not_mem_nil ((same head).mp (List.Mem.head tail)))
      | cons next remaining =>
          have leftFacts := List.pairwise_cons.mp leftOrdered
          have rightFacts := List.pairwise_cons.mp rightOrdered
          have heads : head = next := by
            by_cases equal : head = next
            · exact equal
            · have inRight : head ∈ remaining :=
                (List.mem_cons.mp ((same head).mp (List.Mem.head tail))).resolve_left equal
              have inLeft : next ∈ tail :=
                (List.mem_cons.mp ((same next).mpr (List.Mem.head remaining))).resolve_left (Ne.symm equal)
              have less := leftFacts.1 next inLeft
              have greater := rightFacts.1 head inRight
              omega
          subst next
          have tails : ∀ x, x ∈ tail ↔ x ∈ remaining := by
            intro x
            constructor
            · intro member
              rcases List.mem_cons.mp ((same x).mp (List.Mem.tail head member)) with equal | present
              · exact False.elim ((Nat.ne_of_lt (leftFacts.1 x member)) equal.symm)
              · exact present
            · intro member
              rcases List.mem_cons.mp ((same x).mpr (List.Mem.tail head member)) with equal | present
              · exact False.elim ((Nat.ne_of_lt (rightFacts.1 x member)) equal.symm)
              · exact present
          exact congrArg (List.cons head) (ih remaining leftFacts.2 rightFacts.2 tails)

theorem CanonicalWitness.block_mem_whole {whole alphabet : List Nat} {first : Slot}
    {rest : List Slot} (witness : CanonicalWitness whole alphabet first rest)
    (slot : Slot) (member : slot ∈ first :: rest) (x : Nat) (inBlock : x ∈ slot.block) :
    x ∈ whole := by
  have inRender := blockMember_render (show BlockMember (first :: rest) x from ⟨slot, member, inBlock⟩)
  simpa only [witness.2.2.2.2.2.2.2.2] using inRender

theorem CanonicalWitness.mem_nonsimple_block {whole alphabet : List Nat} {first : Slot}
    {rest : List Slot} (witness : CanonicalWitness whole alphabet first rest)
    (x : Nat) (member : x ∈ whole) (nonsimple : whole.count x ≠ 1) :
    BlockMember (first :: rest) x := by
  apply (render_nonsimple_iff whole (first :: rest)
    (fun slot member x inGap => witness.gap_simple slot member x inGap) x nonsimple).mp
  simpa only [witness.2.2.2.2.2.2.2.2] using member

theorem CanonicalWitness.target_overlap_forces_source_block_eq
    {left right leftAlphabet rightAlphabet : List Nat}
    {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (leftWitness : CanonicalWitness left leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right rightAlphabet rightFirst rightRest)
    (same : Actual.SameEval left right)
    (sourceOne sourceTwo target : Slot)
    (oneMember : sourceOne ∈ leftFirst :: leftRest) (twoMember : sourceTwo ∈ leftFirst :: leftRest)
    (targetMember : target ∈ rightFirst :: rightRest)
    (x y : Nat) (xOne : x ∈ sourceOne.block) (yTwo : y ∈ sourceTwo.block)
    (xTarget : x ∈ target.block) (yTarget : y ∈ target.block) :
    sourceOne.block = sourceTwo.block := by
  by_cases equal : sourceOne.block = sourceTwo.block
  · exact equal
  · have canonical := leftWitness.2.2.2.2.2.2.2.1
    obtain ⟨anchor, other, before, window, after, orientation, shape, anchored,
      _, _, otherPresent, outside, separated⟩ :=
      canonical_oriented_window canonical sourceOne.block sourceTwo.block equal
        ⟨sourceOne, oneMember, rfl⟩ ⟨sourceTwo, twoMember, rfl⟩
    obtain ⟨anchorSlot, anchorMember, anchorBlock⟩ := anchored.anchor_present
    obtain ⟨otherSlot, otherMember, otherBlock⟩ := otherPresent
    have windowNonempty : window ≠ [] := by
      intro empty
      rw [empty] at anchorMember
      cases anchorMember
    apply False.elim
    rcases orientation with original | switched
    · have xWindow : BlockMember window x := by
        refine ⟨anchorSlot, anchorMember, ?_⟩
        rw [anchorBlock, original.1]
        exact xOne
      have yOutside : BlockMember (before ++ after) y := by
        refine ⟨otherSlot, otherMember, ?_⟩
        rw [otherBlock, original.2]
        exact yTwo
      exact leftWitness.excludes_target_window_mix rightWitness same before window after shape
        windowNonempty outside separated target targetMember x y xTarget yTarget xWindow yOutside
    · have yWindow : BlockMember window y := by
        refine ⟨anchorSlot, anchorMember, ?_⟩
        rw [anchorBlock, switched.1]
        exact yTwo
      have xOutside : BlockMember (before ++ after) x := by
        refine ⟨otherSlot, otherMember, ?_⟩
        rw [otherBlock, switched.2]
        exact xOne
      exact leftWitness.excludes_target_window_mix rightWitness same before window after shape
        windowNonempty outside separated target targetMember y x yTarget xTarget yWindow xOutside

/-- A source block has an equal literal target block, not merely a containing
block. The reverse-direction separator prevents splitting; the forward one
prevents merging. Sortedness removes the residual list-order ambiguity. -/
theorem CanonicalWitness.matching_block {left right leftAlphabet rightAlphabet : List Nat}
    {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (leftWitness : CanonicalWitness left leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right rightAlphabet rightFirst rightRest)
    (same : Actual.SameEval left right) (source : Slot) (sourceMember : source ∈ leftFirst :: leftRest) :
    ∃ target ∈ rightFirst :: rightRest, target.block = source.block := by
  have sourceGood := leftWitness.2.2.2.2.2.2.2.1.1 source sourceMember
  obtain ⟨x, tail, sourceShape⟩ := List.exists_cons_of_ne_nil sourceGood.1
  have xSource : x ∈ source.block := by rw [sourceShape]; simp
  have xRight : x ∈ right := (same.mem x).mp (leftWitness.block_mem_whole source sourceMember x xSource)
  have xRightNonsimple : right.count x ≠ 1 := by
    intro simple
    exact leftWitness.block_nonsimple source sourceMember x xSource ((same.countOne x).mpr simple)
  obtain ⟨target, targetMember, xTarget⟩ := rightWitness.mem_nonsimple_block x xRight xRightNonsimple
  have sameBack : Actual.SameEval right left := fun valuation acc => (same valuation acc).symm
  have sameContent : ∀ y, y ∈ target.block ↔ y ∈ source.block := by
    intro y
    constructor
    · intro yTarget
      have yLeft : y ∈ left := (same.mem y).mpr (rightWitness.block_mem_whole target targetMember y yTarget)
      have yLeftNonsimple : left.count y ≠ 1 := by
        intro simple
        exact rightWitness.block_nonsimple target targetMember y yTarget ((same.countOne y).mp simple)
      obtain ⟨other, otherMember, yOther⟩ := leftWitness.mem_nonsimple_block y yLeft yLeftNonsimple
      have equal := leftWitness.target_overlap_forces_source_block_eq rightWitness same
        source other target sourceMember otherMember targetMember x y xSource yOther xTarget yTarget
      rw [equal]
      exact yOther
    · intro ySource
      have yRight : y ∈ right := (same.mem y).mp (leftWitness.block_mem_whole source sourceMember y ySource)
      have yRightNonsimple : right.count y ≠ 1 := by
        intro simple
        exact leftWitness.block_nonsimple source sourceMember y ySource ((same.countOne y).mpr simple)
      obtain ⟨other, otherMember, yOther⟩ := rightWitness.mem_nonsimple_block y yRight yRightNonsimple
      have equal := rightWitness.target_overlap_forces_source_block_eq leftWitness sameBack
        target other source targetMember otherMember sourceMember x y xTarget yOther xSource ySource
      rw [equal]
      exact yOther
  have targetGood := rightWitness.2.2.2.2.2.2.2.1.1 target targetMember
  exact ⟨target, targetMember, ordered_nat_lists_eq target.block source.block
    (targetGood.ordered rightWitness.1) (sourceGood.ordered leftWitness.1) sameContent⟩

theorem CanonicalWitness.same_block_sets {left right leftAlphabet rightAlphabet : List Nat}
    {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (leftWitness : CanonicalWitness left leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right rightAlphabet rightFirst rightRest)
    (same : Actual.SameEval left right) (block : List Nat) :
    BlockOccurs block (leftFirst :: leftRest) ↔ BlockOccurs block (rightFirst :: rightRest) := by
  constructor
  · rintro ⟨source, member, equal⟩
    obtain ⟨target, targetMember, matching⟩ := leftWitness.matching_block rightWitness same source member
    exact ⟨target, targetMember, matching.trans equal⟩
  · rintro ⟨source, member, equal⟩
    have sameBack : Actual.SameEval right left := fun valuation acc => (same valuation acc).symm
    obtain ⟨target, targetMember, matching⟩ := rightWitness.matching_block leftWitness sameBack source member
    exact ⟨target, targetMember, matching.trans equal⟩

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.ordered_nat_lists_eq
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.block_mem_whole
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.mem_nonsimple_block
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.target_overlap_forces_source_block_eq
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.matching_block
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.same_block_sets

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
