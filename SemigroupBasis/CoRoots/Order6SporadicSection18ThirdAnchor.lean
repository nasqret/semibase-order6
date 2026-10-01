import SemigroupBasis.CoRoots.Order6SporadicSection18ResidualEdges

/-! Lemma18.10's third anchor, without assuming it. Noncrossing separates the
closed prefix loop from an anchor-free suffix. Residual semantic edge ownership
then contradicts the no-return cut if the desired edge is taken first. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis

theorem right_closed_window_disjoint {chain : List Slot} (crossing : CrossingClosed chain)
    (before middle after : List Slot) (first last : Slot) (endsEqual : first.block = last.block)
    (shape : chain = before ++ first :: (middle ++ last :: after))
    (afterAvoid : AvoidBlock first.block after)
    (inside outside : Slot) (inWindow : inside ∈ first :: (middle ++ [last])) (inAfter : outside ∈ after) :
    inside.block ≠ outside.block := by
  intro equal
  have anchor : inside.block = first.block := by
    rcases List.mem_cons.mp inWindow with slotEqual | member
    · subst inside
      rfl
    · rcases List.mem_append.mp member with inMiddle | inLast
      · exact crossing_window_right crossing before middle after first last inside outside
          endsEqual shape inMiddle inAfter equal
      · have slotEqual := List.mem_singleton.mp inLast
        exact (congrArg Slot.block slotEqual).trans endsEqual.symm
  exact afterAvoid outside inAfter (equal.symm.trans anchor)

theorem third_anchor_of_residual_edges {chain : List Slot} (crossing : CrossingClosed chain)
    (before middle : List Slot) (current last wanted : Slot) (sourceTail after : List Slot)
    (shape : chain = before ++ current :: (middle ++ last :: wanted :: after))
    (endsEqual : current.block = last.block)
    (covers : ∀ slot ∈ middle ++ [last], slot ∈ wanted :: sourceTail)
    (edges : ∀ edge ∈ stepEdges current.block (wanted :: sourceTail),
      edge ∈ stepEdges current.block ((middle ++ [last]) ++ wanted :: after)) :
    BlockOccurs current.block (wanted :: after) := by
  classical
  by_cases present : BlockOccurs current.block (wanted :: after)
  · exact present
  · have afterAvoid : AvoidBlock current.block (wanted :: after) := by
      intro slot member equal
      exact present ⟨slot, member, equal⟩
    let inside := fun block => BlockOccurs block (current :: (middle ++ [last]))
    have afterOutside : ∀ slot ∈ wanted :: after, ¬ inside slot.block := by
      intro slot member inCut
      change BlockOccurs slot.block (current :: (middle ++ [last])) at inCut
      obtain ⟨inner, innerMember, equal⟩ := inCut
      exact right_closed_window_disjoint crossing before middle (wanted :: after) current last
        endsEqual shape afterAvoid inner slot innerMember member equal
    have startInside : inside current.block := ⟨current, List.Mem.head _, rfl⟩
    have beforeInside : ∀ slot ∈ middle ++ [last], inside slot.block := by
      intro slot member
      exact ⟨slot, List.Mem.tail current member, rfl⟩
    exact False.elim (edge_cut_prevents_prefix_reordering inside current.block wanted sourceTail
      (middle ++ [last]) after (by simp) startInside beforeInside afterOutside covers edges)

theorem canonical_third_anchor_at_split {left right : Word Nat}
    {leftAlphabet rightAlphabet : List Nat} {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (same : Actual.SameEval left.toList right.toList)
    (leftWitness : CanonicalWitness left.toList leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right.toList rightAlphabet rightFirst rightRest)
    (common : List Slot) (current wanted : Slot) (sourceTail middle : List Slot) (last : Slot) (after : List Slot)
    (leftShape : leftFirst :: leftRest = common ++ current :: wanted :: sourceTail)
    (rightShape : rightFirst :: rightRest = common ++ current :: (middle ++ last :: wanted :: after)) :
    BlockOccurs current.block (wanted :: after) := by
  have beforeWanted : rightFirst :: rightRest = (common ++ current :: middle) ++ last :: wanted :: after := by
    simpa only [List.append_assoc, List.cons_append] using rightShape
  have endsEqual := leftWitness.same_block_before_equal_gap rightWitness same common current wanted sourceTail
    (common ++ current :: middle) last wanted after leftShape beforeWanted rfl
  have residualShape : rightFirst :: rightRest = common ++ current :: ((middle ++ [last]) ++ wanted :: after) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using rightShape
  have permutation := canonicalResidualPermutation same leftWitness rightWitness common current
    (wanted :: sourceTail) ((middle ++ [last]) ++ wanted :: after) leftShape residualShape
  apply third_anchor_of_residual_edges rightWitness.2.2.2.2.2.2.2.1.2.2 common middle current last wanted
    sourceTail after rightShape endsEqual
  · intro slot member
    exact permutation.mem_iff.mpr (List.mem_append.mpr (Or.inl member))
  · intro edge member
    exact (canonicalResidualEdgeMembership same leftWitness rightWitness common current
      (wanted :: sourceTail) ((middle ++ [last]) ++ wanted :: after) leftShape residualShape edge).mp member

private theorem exists_last_slot (chain : List Slot) (nonempty : chain ≠ []) :
    ∃ before last, chain = before ++ [last] := by
  have reverseNonempty : chain.reverse ≠ [] := by simpa using nonempty
  obtain ⟨last, reversed, shape⟩ := List.exists_cons_of_ne_nil reverseNonempty
  exact ⟨reversed.reverse, last, by simpa only [List.reverse_reverse, List.reverse_cons] using congrArg List.reverse shape⟩

/-- At an actual first mismatch, the target admits two NONEMPTY consecutive
loops based at current.block. The second starts with the desired source slot.
Both loop-end anchors and the entire target decomposition are proved. -/
theorem canonical_mismatch_has_two_loops {left right : Word Nat}
    {leftAlphabet rightAlphabet : List Nat} {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (same : Actual.SameEval left.toList right.toList)
    (leftWitness : CanonicalWitness left.toList leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right.toList rightAlphabet rightFirst rightRest)
    (common : List Slot) (current wanted other : Slot) (sourceTail targetTail : List Slot)
    (leftShape : leftFirst :: leftRest = common ++ current :: wanted :: sourceTail)
    (rightShape : rightFirst :: rightRest = common ++ current :: other :: targetTail)
    (different : wanted ≠ other) :
    ∃ (loop1 loop2Tail after beforePivot : List Slot) (pivot : Slot) (beforeThird : List Slot) (third : Slot),
      loop1 = beforePivot ++ [pivot] ∧ wanted :: loop2Tail = beforeThird ++ [third] ∧
      pivot.block = current.block ∧ third.block = current.block ∧
      rightFirst :: rightRest = common ++ current :: (loop1 ++ (wanted :: loop2Tail) ++ after) := by
  have permutation := canonicalResidualPermutation same leftWitness rightWitness common current
    (wanted :: sourceTail) (other :: targetTail) leftShape rightShape
  have wantedMember : wanted ∈ other :: targetTail := permutation.mem_iff.mp (List.Mem.head sourceTail)
  obtain ⟨beforeWanted, afterWanted, residualShape⟩ := List.mem_iff_append.mp wantedMember
  have beforeNonempty : beforeWanted ≠ [] := by
    intro empty
    rw [empty, List.nil_append] at residualShape
    exact different (List.cons.inj residualShape).1.symm
  obtain ⟨middle, pivot, beforeShape⟩ := exists_last_slot beforeWanted beforeNonempty
  have targetSplit : rightFirst :: rightRest = common ++ current :: (middle ++ pivot :: wanted :: afterWanted) := by
    rw [rightShape, residualShape, beforeShape]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have beforeWantedShape : rightFirst :: rightRest = (common ++ current :: middle) ++ pivot :: wanted :: afterWanted := by
    simpa only [List.append_assoc, List.cons_append] using targetSplit
  have pivotEqual := leftWitness.same_block_before_equal_gap rightWitness same common current wanted sourceTail
    (common ++ current :: middle) pivot wanted afterWanted leftShape beforeWantedShape rfl
  obtain ⟨third, thirdMember, thirdEqual⟩ := canonical_third_anchor_at_split same leftWitness rightWitness common current
    wanted sourceTail middle pivot afterWanted leftShape targetSplit
  obtain ⟨beforeThird, afterThird, thirdShape⟩ := List.mem_iff_append.mp thirdMember
  let loop2 := beforeThird ++ [third]
  have nonempty2 : loop2 ≠ [] := by simp [loop2]
  obtain ⟨head, loop2Tail, loop2Shape⟩ := List.exists_cons_of_ne_nil nonempty2
  have suffixShape : wanted :: afterWanted = loop2 ++ afterThird := by
    simpa only [loop2, List.append_assoc, List.cons_append, List.nil_append] using thirdShape
  have heads : wanted = head := (List.cons.inj (show wanted :: afterWanted = head :: (loop2Tail ++ afterThird) from by
    simpa only [loop2Shape, List.cons_append] using suffixShape)).1
  subst head
  refine ⟨middle ++ [pivot], loop2Tail, afterThird, middle, pivot, beforeThird, third,
    rfl, loop2Shape.symm, pivotEqual.symm, thirdEqual, ?_⟩
  rw [rightShape, residualShape, beforeShape, suffixShape, loop2Shape]
  simp only [List.append_assoc]

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.right_closed_window_disjoint
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.third_anchor_of_residual_edges
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonical_third_anchor_at_split
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonical_mismatch_has_two_loops

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
