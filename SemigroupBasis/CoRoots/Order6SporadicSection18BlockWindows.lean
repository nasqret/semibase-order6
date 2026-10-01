import SemigroupBasis.CoRoots.Order6SporadicSection18SaturationExists

/-! Extremal block windows for Lemma18.8. Both single-occurrence and repeated
anchors are covered. CrossingClosed excludes a block label from straddling a
window boundary; OverlapClosed turns that positional fact into disjoint actual
letter supports. No global-content-to-position inference is assumed. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

def AvoidBlock (anchor : List Nat) (chain : List Slot) : Prop :=
  ∀ slot ∈ chain, slot.block ≠ anchor

inductive AnchoredWindow (anchor : List Nat) : List Slot → Prop where
  | single (gap : List Nat) : AnchoredWindow anchor [⟨gap, anchor⟩]
  | repeated (firstGap lastGap : List Nat) (middle : List Slot) :
      AnchoredWindow anchor (⟨firstGap, anchor⟩ :: (middle ++ [⟨lastGap, anchor⟩]))

theorem AnchoredWindow.ends {anchor : List Nat} {window : List Slot}
    (anchored : AnchoredWindow anchor window) :
    ∃ before gap, window = before ++ [⟨gap, anchor⟩] := by
  cases anchored with
  | single gap => exact ⟨[], gap, rfl⟩
  | repeated firstGap lastGap middle => exact ⟨⟨firstGap, anchor⟩ :: middle, lastGap, rfl⟩

theorem OverlapClosed.tail {first : Slot} {chain : List Slot}
    (closed : OverlapClosed (first :: chain)) : OverlapClosed chain := by
  intro before middle after g1 g2 left right x shape inLeft inRight
  apply closed (first :: before) middle after g1 g2 left right x
  · simpa only [List.cons_append] using congrArg (List.cons first) shape
  · exact inLeft
  · exact inRight

theorem overlapClosed_members :
    ∀ (chain : List Slot), OverlapClosed chain →
      ∀ (left : Slot), left ∈ chain → ∀ (right : Slot), right ∈ chain →
        ∀ x, x ∈ left.block → x ∈ right.block → left.block = right.block
  | [], _, _, impossible, _, _, _, _, _ => False.elim (List.not_mem_nil impossible)
  | first :: rest, closed, left, leftMember, right, rightMember, x, inLeft, inRight => by
      rcases List.mem_cons.mp leftMember with leftEq | leftTail
      · subst left
        rcases List.mem_cons.mp rightMember with rightEq | rightTail
        · subst right
          rfl
        · obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp rightTail
          exact closed [] before after first.gap right.gap first.block right.block x
            (by rw [shape]; rfl) inLeft inRight
      · rcases List.mem_cons.mp rightMember with rightEq | rightTail
        · subst right
          obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp leftTail
          exact (closed [] before after first.gap left.gap first.block left.block x
            (by rw [shape]; rfl) inRight inLeft).symm
        · exact overlapClosed_members rest closed.tail left leftTail right rightTail x inLeft inRight

/-- A block appearing both before and between equal endpoint blocks creates
the forbidden B A B A crossing, unless its label is the endpoint label. -/
theorem crossing_window_left {chain : List Slot} (closed : CrossingClosed chain)
    (before middle after : List Slot) (first last inside outside : Slot)
    (endsEqual : first.block = last.block)
    (shape : chain = before ++ (first :: (middle ++ (last :: after))))
    (inMiddle : inside ∈ middle) (inBefore : outside ∈ before)
    (sameBlock : inside.block = outside.block) : inside.block = first.block := by
  obtain ⟨before1, before2, beforeShape⟩ := List.mem_iff_append.mp inBefore
  obtain ⟨middle1, middle2, middleShape⟩ := List.mem_iff_append.mp inMiddle
  have insideSlot : (⟨inside.gap, outside.block⟩ : Slot) = inside := by
    rw [← sameBlock]
  have lastSlot : (⟨last.gap, first.block⟩ : Slot) = last := by
    rw [endsEqual]
  have crossing := closed before1 before2 middle1 middle2 after
    outside.gap first.gap inside.gap last.gap outside.block first.block (by
      rw [shape, beforeShape, middleShape]
      simp only [insideSlot, lastSlot, List.append_assoc, List.cons_append])
  exact sameBlock.trans crossing

/-- The symmetric boundary produces A B A B. -/
theorem crossing_window_right {chain : List Slot} (closed : CrossingClosed chain)
    (before middle after : List Slot) (first last inside outside : Slot)
    (endsEqual : first.block = last.block)
    (shape : chain = before ++ (first :: (middle ++ (last :: after))))
    (inMiddle : inside ∈ middle) (inAfter : outside ∈ after)
    (sameBlock : inside.block = outside.block) : inside.block = first.block := by
  obtain ⟨middle1, middle2, middleShape⟩ := List.mem_iff_append.mp inMiddle
  obtain ⟨after1, after2, afterShape⟩ := List.mem_iff_append.mp inAfter
  have outsideSlot : (⟨outside.gap, inside.block⟩ : Slot) = outside := by
    rw [sameBlock]
  have lastSlot : (⟨last.gap, first.block⟩ : Slot) = last := by
    rw [endsEqual]
  have crossing := closed before middle1 middle2 after1 after2
    first.gap inside.gap last.gap outside.gap first.block inside.block (by
      rw [shape, middleShape, afterShape]
      simp only [outsideSlot, lastSlot, List.append_assoc, List.cons_append])
  exact crossing.symm

/-- Every block that occurs has a first/last-occurrence window, including
the case in which its label occurs in exactly one slot. -/
theorem exists_anchoredWindow (anchor : List Nat) :
    ∀ chain : List Slot, (∃ slot ∈ chain, slot.block = anchor) →
      ∃ before window after, chain = before ++ window ++ after ∧
        AnchoredWindow anchor window ∧ AvoidBlock anchor before ∧ AvoidBlock anchor after
  | [], present => by
      obtain ⟨slot, impossible, _⟩ := present
      cases impossible
  | first :: rest, present => by
      classical
      by_cases firstEq : first.block = anchor
      · have firstSlot : first = ⟨first.gap, anchor⟩ := by rw [← firstEq]
        by_cases more : ∃ slot ∈ rest, slot.block = anchor
        · obtain ⟨before, window, after, shape, anchored, _, afterAvoid⟩ :=
            exists_anchoredWindow anchor rest more
          obtain ⟨lastBefore, lastGap, lastShape⟩ := anchored.ends
          refine ⟨[], first :: (before ++ window), after, ?_, ?_, ?_, afterAvoid⟩
          · simpa only [List.nil_append, List.cons_append, List.append_assoc] using
              congrArg (List.cons first) shape
          · rw [firstSlot, lastShape]
            simpa only [List.append_assoc] using
              AnchoredWindow.repeated (anchor := anchor) first.gap lastGap (before ++ lastBefore)
          · intro slot impossible
            cases impossible
        · refine ⟨[], [first], rest, by simp, ?_, ?_, ?_⟩
          · rw [firstSlot]
            exact AnchoredWindow.single first.gap
          · intro slot impossible
            cases impossible
          · intro slot member equal
            exact more ⟨slot, member, equal⟩
      · have tailPresent : ∃ slot ∈ rest, slot.block = anchor := by
          obtain ⟨slot, member, equal⟩ := present
          rcases List.mem_cons.mp member with slotEq | member
          · subst slot
            exact False.elim (firstEq equal)
          · exact ⟨slot, member, equal⟩
        obtain ⟨before, window, after, shape, anchored, beforeAvoid, afterAvoid⟩ :=
          exists_anchoredWindow anchor rest tailPresent
        refine ⟨first :: before, window, after, ?_, anchored, ?_, afterAvoid⟩
        · simpa only [List.cons_append] using congrArg (List.cons first) shape
        · intro slot member
          rcases List.mem_cons.mp member with equal | member
          · subst slot
            exact firstEq
          · exact beforeAvoid slot member

theorem window_labels_disjoint {chain window : List Slot} {anchor : List Nat}
    (closed : CrossingClosed chain) (before after : List Slot)
    (shape : chain = before ++ window ++ after) (anchored : AnchoredWindow anchor window)
    (beforeAvoid : AvoidBlock anchor before) (afterAvoid : AvoidBlock anchor after)
    (inside outside : Slot) (inWindow : inside ∈ window) (outWindow : outside ∈ before ++ after) :
    inside.block ≠ outside.block := by
  intro sameBlock
  have insideAnchor : inside.block = anchor := by
    cases anchored with
    | single gap =>
        have equal := List.mem_singleton.mp inWindow
        rw [equal]
    | repeated firstGap lastGap middle =>
        rcases List.mem_cons.mp inWindow with equal | member
        · rw [equal]
        · rcases List.mem_append.mp member with inMiddle | inLast
          · have repeatedShape : chain = before ++
                (⟨firstGap, anchor⟩ :: (middle ++ (⟨lastGap, anchor⟩ :: after))) := by
              simpa only [List.append_assoc, List.cons_append, List.nil_append] using shape
            rcases List.mem_append.mp outWindow with inBefore | inAfter
            · exact crossing_window_left closed before middle after
                ⟨firstGap, anchor⟩ ⟨lastGap, anchor⟩ inside outside rfl repeatedShape
                inMiddle inBefore sameBlock
            · exact crossing_window_right closed before middle after
                ⟨firstGap, anchor⟩ ⟨lastGap, anchor⟩ inside outside rfl repeatedShape
                inMiddle inAfter sameBlock
          · have equal := List.mem_singleton.mp inLast
            rw [equal]
  have outsideAnchor : outside.block = anchor := sameBlock.symm.trans insideAnchor
  rcases List.mem_append.mp outWindow with inBefore | inAfter
  · exact beforeAvoid outside inBefore outsideAnchor
  · exact afterAvoid outside inAfter outsideAnchor

/-- Actual block-letter supports on the two sides of an extremal window are
disjoint. Positional crossing and semantic support overlap play distinct roles. -/
theorem window_support_disjoint {chain window : List Slot} {anchor : List Nat}
    (overlap : OverlapClosed chain) (crossing : CrossingClosed chain) (before after : List Slot)
    (shape : chain = before ++ window ++ after) (anchored : AnchoredWindow anchor window)
    (beforeAvoid : AvoidBlock anchor before) (afterAvoid : AvoidBlock anchor after)
    (inside outside : Slot) (inWindow : inside ∈ window) (outWindow : outside ∈ before ++ after)
    (x : Nat) (inInside : x ∈ inside.block) : x ∉ outside.block := by
  intro inOutside
  have insideChain : inside ∈ chain := by
    rw [shape]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr inWindow)))
  have outsideChain : outside ∈ chain := by
    rw [shape]
    rcases List.mem_append.mp outWindow with inBefore | inAfter
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl inBefore)))
    · exact List.mem_append.mpr (Or.inr inAfter)
  have blocksEqual := overlapClosed_members chain overlap inside insideChain outside outsideChain
    x inInside inOutside
  exact window_labels_disjoint crossing before after shape anchored beforeAvoid afterAvoid
    inside outside inWindow outWindow blocksEqual

theorem canonical_anchoredWindow {alphabet : List Nat} {chain : List Slot}
    (canonical : CanonicalChain alphabet chain) (anchor : List Nat)
    (present : ∃ slot ∈ chain, slot.block = anchor) :
    ∃ before window after, chain = before ++ window ++ after ∧
      AnchoredWindow anchor window ∧ AvoidBlock anchor before ∧ AvoidBlock anchor after ∧
      ∀ inside ∈ window, ∀ outside ∈ before ++ after, ∀ x ∈ inside.block, x ∉ outside.block := by
  obtain ⟨before, window, after, shape, anchored, beforeAvoid, afterAvoid⟩ :=
    exists_anchoredWindow anchor chain present
  refine ⟨before, window, after, shape, anchored, beforeAvoid, afterAvoid, ?_⟩
  intro inside inWindow outside outWindow x inInside
  exact window_support_disjoint canonical.2.1 canonical.2.2 before after shape anchored
    beforeAvoid afterAvoid inside outside inWindow outWindow x inInside

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.AnchoredWindow.ends
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.OverlapClosed.tail
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.overlapClosed_members
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.crossing_window_left
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.crossing_window_right
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.exists_anchoredWindow
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.window_labels_disjoint
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.window_support_disjoint
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonical_anchoredWindow

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
