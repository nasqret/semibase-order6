import SemigroupBasis.CoRoots.Order6SporadicSection18BlockWindows

/-! Orient two distinct occurring block labels so that one has an occurrence
outside the other's extremal window. If one orientation fails, the other label
lies strictly inside the first window; its own extremal window then has the
first anchor outside. No unproved first-occurrence ordering is assumed. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

def BlockOccurs (anchor : List Nat) (chain : List Slot) : Prop :=
  ∃ slot ∈ chain, slot.block = anchor

def SeparatingWindow (chain : List Slot) (anchor other : List Nat) : Prop :=
  ∃ before window after, chain = before ++ window ++ after ∧
    AnchoredWindow anchor window ∧ AvoidBlock anchor before ∧ AvoidBlock anchor after ∧
      BlockOccurs other (before ++ after)

theorem AnchoredWindow.anchor_present {anchor : List Nat} {window : List Slot}
    (anchored : AnchoredWindow anchor window) : BlockOccurs anchor window := by
  cases anchored with
  | single gap => exact ⟨⟨gap, anchor⟩, List.Mem.head [], rfl⟩
  | repeated firstGap lastGap middle =>
      exact ⟨⟨firstGap, anchor⟩, List.Mem.head _, rfl⟩

theorem outside_occurs_nonempty {anchor : List Nat} {before after : List Slot}
    (present : BlockOccurs anchor (before ++ after)) : before ≠ [] ∨ after ≠ [] := by
  by_cases beforeEmpty : before = []
  · right
    intro afterEmpty
    obtain ⟨slot, member, _⟩ := present
    rw [beforeEmpty, afterEmpty] at member
    cases member
  · exact Or.inl beforeEmpty

theorem exists_oriented_window (chain : List Slot) (first second : List Nat)
    (different : first ≠ second) (firstPresent : BlockOccurs first chain)
    (secondPresent : BlockOccurs second chain) :
    SeparatingWindow chain first second ∨ SeparatingWindow chain second first := by
  classical
  obtain ⟨before, window, after, shape, anchored, beforeAvoid, afterAvoid⟩ :=
    exists_anchoredWindow first chain firstPresent
  by_cases outside : BlockOccurs second (before ++ after)
  · exact Or.inl ⟨before, window, after, shape, anchored, beforeAvoid, afterAvoid, outside⟩
  · have secondBefore : AvoidBlock second before := by
      intro slot member equal
      exact outside ⟨slot, List.mem_append.mpr (Or.inl member), equal⟩
    have secondAfter : AvoidBlock second after := by
      intro slot member equal
      exact outside ⟨slot, List.mem_append.mpr (Or.inr member), equal⟩
    have inside : BlockOccurs second window := by
      obtain ⟨slot, member, equal⟩ := secondPresent
      rw [shape] at member
      rcases List.mem_append.mp member with member | inAfter
      · rcases List.mem_append.mp member with inBefore | inWindow
        · exact False.elim (secondBefore slot inBefore equal)
        · exact ⟨slot, inWindow, equal⟩
      · exact False.elim (secondAfter slot inAfter equal)
    cases anchored with
    | single gap =>
        obtain ⟨slot, member, equal⟩ := inside
        have slotEq := List.mem_singleton.mp member
        subst slot
        exact False.elim (different equal)
    | repeated firstGap lastGap middle =>
        have middlePresent : BlockOccurs second middle := by
          obtain ⟨slot, member, equal⟩ := inside
          rcases List.mem_cons.mp member with slotEq | member
          · subst slot
            exact False.elim (different equal)
          · rcases List.mem_append.mp member with inMiddle | inLast
            · exact ⟨slot, inMiddle, equal⟩
            · have slotEq := List.mem_singleton.mp inLast
              subst slot
              exact False.elim (different equal)
        obtain ⟨innerBefore, innerWindow, innerAfter, innerShape, innerAnchored,
          innerBeforeAvoid, innerAfterAvoid⟩ := exists_anchoredWindow second middle middlePresent
        let newBefore := before ++ (⟨firstGap, first⟩ :: innerBefore)
        let newAfter := innerAfter ++ (⟨lastGap, first⟩ :: after)
        right
        refine ⟨newBefore, innerWindow, newAfter, ?_, innerAnchored, ?_, ?_, ?_⟩
        · rw [shape, innerShape]
          simp only [newBefore, newAfter, List.append_assoc, List.cons_append, List.nil_append]
        · intro slot member
          rcases List.mem_append.mp member with inBefore | member
          · exact secondBefore slot inBefore
          · rcases List.mem_cons.mp member with slotEq | inInner
            · subst slot
              exact different
            · exact innerBeforeAvoid slot inInner
        · intro slot member
          rcases List.mem_append.mp member with inInner | member
          · exact innerAfterAvoid slot inInner
          · rcases List.mem_cons.mp member with slotEq | inAfter
            · subst slot
              exact different
            · exact secondAfter slot inAfter
        · refine ⟨⟨firstGap, first⟩, ?_, rfl⟩
          simp [newBefore]

/-- The chosen orientation, nonempty outside boundary and support separation
all concern the SAME extremal window in the original canonical chain. -/
theorem canonical_oriented_window {alphabet : List Nat} {chain : List Slot}
    (canonical : CanonicalChain alphabet chain) (first second : List Nat)
    (different : first ≠ second) (firstPresent : BlockOccurs first chain)
    (secondPresent : BlockOccurs second chain) :
    ∃ anchor other before window after,
      ((anchor = first ∧ other = second) ∨ (anchor = second ∧ other = first)) ∧
      chain = before ++ window ++ after ∧ AnchoredWindow anchor window ∧
      AvoidBlock anchor before ∧ AvoidBlock anchor after ∧ BlockOccurs other (before ++ after) ∧
      (before ≠ [] ∨ after ≠ []) ∧
      ∀ inside ∈ window, ∀ outside ∈ before ++ after, ∀ x ∈ inside.block, x ∉ outside.block := by
  obtain ⟨anchor, other, orientation, separating⟩ :
      ∃ anchor other,
        ((anchor = first ∧ other = second) ∨ (anchor = second ∧ other = first)) ∧
        SeparatingWindow chain anchor other := by
    rcases exists_oriented_window chain first second different firstPresent secondPresent with
      original | switched
    · exact ⟨first, second, Or.inl ⟨rfl, rfl⟩, original⟩
    · exact ⟨second, first, Or.inr ⟨rfl, rfl⟩, switched⟩
  obtain ⟨before, window, after, shape, anchored, beforeAvoid, afterAvoid, outside⟩ := separating
  refine ⟨anchor, other, before, window, after, orientation, shape, anchored, beforeAvoid,
    afterAvoid, outside, outside_occurs_nonempty outside, ?_⟩
  intro inside inWindow out outWindow x inInside
  exact window_support_disjoint canonical.2.1 canonical.2.2 before after shape anchored
    beforeAvoid afterAvoid inside out inWindow outWindow x inInside

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.AnchoredWindow.anchor_present
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.outside_occurs_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.exists_oriented_window
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonical_oriented_window

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
