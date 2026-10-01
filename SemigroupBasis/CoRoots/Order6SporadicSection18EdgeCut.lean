import SemigroupBasis.CoRoots.Order6SporadicSection18CanonicalPermutation

/-! A no-return cut argument for the residual canonical walks in Lemma18.10.
Edges retain BOTH the predecessor block and the full destination slot. A path
starting outside a predecessor-closed cut cannot later cover an inside vertex. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

def stepEdges (start : List Nat) : List Slot → List (List Nat × Slot)
  | [] => []
  | slot :: rest => (start, slot) :: stepEdges slot.block rest

theorem stepEdge_target_mem {start : List Nat} {chain : List Slot} {previous : List Nat} {slot : Slot}
    (member : (previous, slot) ∈ stepEdges start chain) : slot ∈ chain := by
  induction chain generalizing start with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with equal | member
      · have slotEqual : slot = head := congrArg Prod.snd equal
        subst slot
        exact List.Mem.head _
      · exact List.Mem.tail head (ih member)

theorem stepEdges_enter_cut (inside : List Nat → Prop) (after : List Slot)
    (afterOutside : ∀ slot ∈ after, ¬ inside slot.block) :
    ∀ (before : List Slot) (start : List Nat), inside start →
      (∀ slot ∈ before, inside slot.block) →
      ∀ previous slot, (previous, slot) ∈ stepEdges start (before ++ after) →
        inside slot.block → inside previous
  | [], _, _, _, _, slot, member, inCut =>
      False.elim (afterOutside slot (stepEdge_target_mem member) inCut)
  | head :: tail, start, startInside, beforeInside, previous, slot, member, inCut => by
      rcases List.mem_cons.mp member with equal | member
      · have previousEqual : previous = start := congrArg Prod.fst equal
        simpa only [previousEqual] using startInside
      · exact stepEdges_enter_cut inside after afterOutside tail head.block
          (beforeInside head (List.Mem.head tail))
          (fun s present => beforeInside s (List.Mem.tail head present)) previous slot member inCut

theorem stepEdges_no_return (inside : List Nat → Prop) :
    ∀ (chain : List Slot) (start : List Nat), (¬ inside start) →
      (∀ previous slot, (previous, slot) ∈ stepEdges start chain → inside slot.block → inside previous) →
      ∀ slot ∈ chain, ¬ inside slot.block
  | [], _, _, _, _, member => False.elim (List.not_mem_nil member)
  | head :: tail, start, startOutside, closed, slot, member => by
      have headOutside : ¬ inside head.block := fun inCut =>
        startOutside (closed start head (List.Mem.head _) inCut)
      rcases List.mem_cons.mp member with equal | inTail
      · subst slot
        exact headOutside
      · exact stepEdges_no_return inside tail head.block headOutside
          (fun previous next present => closed previous next (List.Mem.tail (start, head) present)) slot inTail

/-- If a target prefix lies inside a cut and its entire suffix lies outside,
a source beginning with that suffix's first edge cannot still cover the prefix
using only target edges. Edge ownership, not a free permutation, is essential. -/
theorem edge_cut_prevents_prefix_reordering (inside : List Nat → Prop)
    (start : List Nat) (wanted : Slot) (sourceTail before after : List Slot)
    (beforeNonempty : before ≠ []) (startInside : inside start)
    (beforeInside : ∀ slot ∈ before, inside slot.block)
    (afterOutside : ∀ slot ∈ wanted :: after, ¬ inside slot.block)
    (covers : ∀ slot ∈ before, slot ∈ wanted :: sourceTail)
    (edges : ∀ edge ∈ stepEdges start (wanted :: sourceTail),
      edge ∈ stepEdges start (before ++ wanted :: after)) : False := by
  have targetClosed := stepEdges_enter_cut inside (wanted :: after) afterOutside before start startInside beforeInside
  have wantedOutside := afterOutside wanted (List.Mem.head after)
  have tailClosed : ∀ previous slot, (previous, slot) ∈ stepEdges wanted.block sourceTail →
      inside slot.block → inside previous := by
    intro previous slot member inCut
    exact targetClosed previous slot (edges (previous, slot) (List.Mem.tail (start, wanted) member)) inCut
  have tailOutside := stepEdges_no_return inside sourceTail wanted.block wantedOutside tailClosed
  obtain ⟨head, tail, shape⟩ := List.exists_cons_of_ne_nil beforeNonempty
  have member : head ∈ before := by rw [shape]; exact List.Mem.head tail
  have inCut := beforeInside head member
  rcases List.mem_cons.mp (covers head member) with equal | inTail
  · exact wantedOutside (by simpa only [equal] using inCut)
  · exact tailOutside head inTail inCut

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.stepEdge_target_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.stepEdges_enter_cut
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.stepEdges_no_return
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.edge_cut_prevents_prefix_reordering

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
