import SemigroupBasis.CoRoots.Order6SporadicSection18BoundaryMarkers

/-! Boundary-marker regions and their exact nonsimple support. The final
disjointness theorem also handles SIMPLE letters, using their whole-word count
and the literal marked split rather than incorrectly disjoining a whole next gap. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

def BlockMember (chain : List Slot) (x : Nat) : Prop :=
  ∃ slot ∈ chain, x ∈ slot.block

theorem blockMember_render {chain : List Slot} {x : Nat} (present : BlockMember chain x) :
    x ∈ render chain := by
  induction chain with
  | nil => obtain ⟨slot, member, _⟩ := present; cases member
  | cons head tail ih =>
      obtain ⟨slot, member, inBlock⟩ := present
      rcases List.mem_cons.mp member with equal | inTail
      · subst slot
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
          (Or.inr ((squareList_mem head.block x).mpr inBlock))))
      · exact List.mem_append.mpr (Or.inr (ih ⟨slot, inTail, inBlock⟩))

theorem render_nonsimple_iff (whole : List Nat) (chain : List Slot)
    (gapsSimple : ∀ slot ∈ chain, ∀ x ∈ slot.gap, whole.count x = 1)
    (x : Nat) (nonsimple : whole.count x ≠ 1) :
    x ∈ render chain ↔ BlockMember chain x := by
  constructor
  · intro present
    induction chain with
    | nil => cases present
    | cons head tail ih =>
        rcases List.mem_append.mp present with inHead | inTail
        · rcases List.mem_append.mp inHead with inGap | inSquare
          · exact False.elim (nonsimple (gapsSimple head (List.Mem.head _) x inGap))
          · exact ⟨head, List.Mem.head _, (squareList_mem head.block x).mp inSquare⟩
        · obtain ⟨slot, member, inBlock⟩ := ih
            (fun slot member x inGap => gapsSimple slot (List.Mem.tail _ member) x inGap) inTail
          exact ⟨slot, List.Mem.tail _ member, inBlock⟩
  · exact blockMember_render

inductive MarkerForm (whole before inside after : List Nat) : Prop
  | middle (left right : Nat)
      (shape : whole = before ++ left :: (inside ++ right :: after))
      (leftSimple : whole.count left = 1) (rightSimple : whole.count right = 1)
      (different : left ≠ right) (clear : Actual.PairClear left right (before ++ inside ++ after))
  | initial (right : Nat) (beforeEmpty : before = [])
      (shape : whole = inside ++ right :: after)
      (rightSimple : whole.count right = 1) (clear : right ∉ inside ++ after)
  | final (left : Nat) (afterEmpty : after = [])
      (shape : whole = before ++ left :: inside)
      (leftSimple : whole.count left = 1) (clear : left ∉ before ++ inside)

structure BoundaryRegions (whole : List Nat) (window outside : List Slot) where
  before : List Nat
  inside : List Nat
  after : List Nat
  form : MarkerForm whole before inside after
  insideSupport : ∀ x, whole.count x ≠ 1 → (x ∈ inside ↔ BlockMember window x)
  outsideSupport : ∀ x, whole.count x ≠ 1 → (x ∈ before ++ after ↔ BlockMember outside x)

private theorem gap_excludes_nonsimple {whole alphabet : List Nat} {first : Slot}
    {rest : List Slot} (witness : CanonicalWitness whole alphabet first rest)
    (slot : Slot) (member : slot ∈ first :: rest) (x : Nat) (nonsimple : whole.count x ≠ 1) :
    x ∉ slot.gap := fun present => nonsimple (witness.gap_simple slot member x present)

private theorem subchain_render_iff {whole alphabet : List Nat} {first : Slot}
    {rest : List Slot} (witness : CanonicalWitness whole alphabet first rest)
    (chain : List Slot) (subchain : ∀ slot ∈ chain, slot ∈ first :: rest)
    (x : Nat) (nonsimple : whole.count x ≠ 1) :
    x ∈ render chain ↔ BlockMember chain x :=
  render_nonsimple_iff whole chain
    (fun slot member x present => witness.gap_simple slot (subchain slot member) x present) x nonsimple

theorem MiddleBoundary.regions {whole alphabet : List Nat} {first : Slot} {rest : List Slot}
    {before window after : List Slot} (data : MiddleBoundary whole before window after)
    (witness : CanonicalWitness whole alphabet first rest)
    (shape : first :: rest = before ++ window ++ after) :
    Nonempty (BoundaryRegions whole window (before ++ after)) := by
  have subWindow : ∀ slot ∈ window, slot ∈ first :: rest := by
    intro slot member
    rw [shape]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member)))
  have subOutside : ∀ slot ∈ before ++ after, slot ∈ first :: rest := by
    intro slot member
    rw [shape]
    rcases List.mem_append.mp member with inBefore | inAfter
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl inBefore)))
    · exact List.mem_append.mpr (Or.inr inAfter)
  have nextMember : data.next ∈ first :: rest := by
    have inAfter : data.next ∈ after := by simp [data.afterShape]
    rw [shape]
    exact List.mem_append.mpr (Or.inr inAfter)
  refine ⟨⟨render before,
    data.leftTail ++ squareList data.head.block ++ render data.tail ++ data.rightHead,
    squareList data.next.block ++ render data.remaining,
    MarkerForm.middle data.left data.right data.wordShape data.leftSimple data.rightSimple
      data.different data.clear, ?_, ?_⟩⟩
  · intro x nonsimple
    have notLeft : x ≠ data.left := by
      intro equal
      exact nonsimple (equal ▸ data.leftSimple)
    have notRightHead : x ∉ data.rightHead := by
      intro member
      apply gap_excludes_nonsimple witness data.next nextMember x nonsimple
      rw [data.rightGap]
      exact List.mem_append.mpr (Or.inl member)
    have support := subchain_render_iff witness window subWindow x nonsimple
    simpa only [data.windowShape, render, data.leftGap, List.mem_append, List.mem_cons, notLeft,
      notRightHead, false_or, or_false, or_assoc] using support
  · intro x nonsimple
    have notNext := gap_excludes_nonsimple witness data.next nextMember x nonsimple
    have support := subchain_render_iff witness (before ++ after) subOutside x nonsimple
    simpa only [render_append, data.afterShape, render, List.mem_append,
      notNext, false_or, or_assoc] using support

theorem InitialBoundary.regions {whole alphabet : List Nat} {first : Slot} {rest : List Slot}
    {before window after : List Slot} (data : InitialBoundary whole before window after)
    (witness : CanonicalWitness whole alphabet first rest)
    (shape : first :: rest = before ++ window ++ after) :
    Nonempty (BoundaryRegions whole window (before ++ after)) := by
  have subWindow : ∀ slot ∈ window, slot ∈ first :: rest := by
    intro slot member
    rw [shape]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member)))
  have subOutside : ∀ slot ∈ before ++ after, slot ∈ first :: rest := by
    intro slot member
    rw [shape]
    rcases List.mem_append.mp member with inBefore | inAfter
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl inBefore)))
    · exact List.mem_append.mpr (Or.inr inAfter)
  have nextMember : data.next ∈ first :: rest := by
    have inAfter : data.next ∈ after := by simp [data.afterShape]
    rw [shape]
    exact List.mem_append.mpr (Or.inr inAfter)
  refine ⟨⟨[], squareList data.head.block ++ render data.tail ++ data.rightHead,
    squareList data.next.block ++ render data.remaining,
    MarkerForm.initial data.right rfl data.wordShape data.rightSimple data.clear, ?_, ?_⟩⟩
  · intro x nonsimple
    have notRightHead : x ∉ data.rightHead := by
      intro member
      apply gap_excludes_nonsimple witness data.next nextMember x nonsimple
      rw [data.rightGap]
      exact List.mem_append.mpr (Or.inl member)
    have support := subchain_render_iff witness window subWindow x nonsimple
    simpa only [data.windowShape, render, data.firstGap, List.nil_append, List.mem_append, notRightHead,
      or_false, or_assoc] using support
  · intro x nonsimple
    have notNext := gap_excludes_nonsimple witness data.next nextMember x nonsimple
    have support := subchain_render_iff witness (before ++ after) subOutside x nonsimple
    simpa only [data.beforeEmpty, data.afterShape, render, List.nil_append,
      List.mem_append, notNext, false_or, or_assoc] using support

theorem FinalBoundary.regions {whole alphabet : List Nat} {first : Slot} {rest : List Slot}
    {before window after : List Slot} (data : FinalBoundary whole before window after)
    (witness : CanonicalWitness whole alphabet first rest)
    (shape : first :: rest = before ++ window ++ after) :
    Nonempty (BoundaryRegions whole window (before ++ after)) := by
  have subWindow : ∀ slot ∈ window, slot ∈ first :: rest := by
    intro slot member
    rw [shape]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member)))
  have subOutside : ∀ slot ∈ before ++ after, slot ∈ first :: rest := by
    intro slot member
    rw [shape]
    rcases List.mem_append.mp member with inBefore | inAfter
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl inBefore)))
    · exact List.mem_append.mpr (Or.inr inAfter)
  refine ⟨⟨render before, data.leftTail ++ squareList data.head.block ++ render data.tail, [],
    MarkerForm.final data.left rfl data.wordShape data.leftSimple data.clear, ?_, ?_⟩⟩
  · intro x nonsimple
    have notLeft : x ≠ data.left := by
      intro equal
      exact nonsimple (equal ▸ data.leftSimple)
    have support := subchain_render_iff witness window subWindow x nonsimple
    simpa only [data.windowShape, render, data.leftGap, List.mem_append, List.mem_cons, notLeft,
      false_or, or_assoc] using support
  · intro x nonsimple
    have support := subchain_render_iff witness (before ++ after) subOutside x nonsimple
    simpa only [data.afterEmpty, List.append_nil] using support

private theorem countOne_regions_disjoint (whole before left inside right after : List Nat)
    (shape : whole = before ++ left ++ inside ++ right ++ after) (x : Nat)
    (simple : whole.count x = 1) (inInside : x ∈ inside) : x ∉ before ++ after := by
  intro inOutside
  have insidePositive := List.count_pos_iff.mpr inInside
  have outsidePositive := List.count_pos_iff.mpr inOutside
  rw [shape] at simple
  simp only [List.count_append] at simple outsidePositive
  omega

theorem MarkerForm.simple_disjoint {whole before inside after : List Nat}
    (form : MarkerForm whole before inside after) (x : Nat)
    (simple : whole.count x = 1) (inInside : x ∈ inside) : x ∉ before ++ after := by
  cases form with
  | middle left right shape _ _ _ _ =>
      apply countOne_regions_disjoint whole before [left] inside [right] after
        ?_ x simple inInside
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using shape
  | initial right beforeEmpty shape _ _ =>
      apply countOne_regions_disjoint whole before [] inside [right] after
        ?_ x simple inInside
      simpa only [beforeEmpty, List.nil_append, List.append_assoc, List.cons_append] using shape
  | final left afterEmpty shape _ _ =>
      apply countOne_regions_disjoint whole before [left] inside [] after
        ?_ x simple inInside
      simpa only [afterEmpty, List.append_nil, List.append_assoc, List.cons_append,
        List.nil_append] using shape

theorem BoundaryRegions.disjoint {whole : List Nat} {window outside : List Slot}
    (regions : BoundaryRegions whole window outside)
    (separated : ∀ inside ∈ window, ∀ out ∈ outside, ∀ x ∈ inside.block, x ∉ out.block)
    (x : Nat) (inInside : x ∈ regions.inside) : x ∉ regions.before ++ regions.after := by
  by_cases simple : whole.count x = 1
  · exact regions.form.simple_disjoint x simple inInside
  · intro inOutside
    obtain ⟨inside, member, inBlock⟩ := (regions.insideSupport x simple).mp inInside
    obtain ⟨out, outMember, outBlock⟩ := (regions.outsideSupport x simple).mp inOutside
    exact separated inside member out outMember x inBlock outBlock

theorem CanonicalWitness.boundary_regions {whole alphabet : List Nat} {first : Slot}
    {rest : List Slot} (witness : CanonicalWitness whole alphabet first rest)
    (before window after : List Slot) (shape : first :: rest = before ++ window ++ after)
    (windowNonempty : window ≠ []) (outside : before ≠ [] ∨ after ≠ []) :
    Nonempty (BoundaryRegions whole window (before ++ after)) := by
  rcases witness.boundary_markers before window after shape windowNonempty outside with
    middle | initial | final
  · cases middle with
    | intro data => exact data.regions witness shape
  · cases initial with
    | intro data => exact data.regions witness shape
  · cases final with
    | intro data => exact data.regions witness shape

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.blockMember_render
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.render_nonsimple_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.MiddleBoundary.regions
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.InitialBoundary.regions
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.FinalBoundary.regions
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.MarkerForm.simple_disjoint
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.BoundaryRegions.disjoint
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.boundary_regions

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
