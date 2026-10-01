import SemigroupBasis.CoRoots.Order6SporadicSection18FreshTag

/-! The fresh-tag operation preserves the COMPLETE canonical witness.
The decoder transports positions and crossing closure back to the original
chain; exact counts prove that zero is nonsimple and old simplicity is unchanged. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

theorem tag_overlap_members (marked : List Nat) (chain : List Slot) (closed : OverlapClosed chain)
    (left right : Slot) (leftMember : left ∈ chain.map (tagSlot marked))
    (rightMember : right ∈ chain.map (tagSlot marked)) (x : Nat)
    (xLeft : x ∈ left.block) (xRight : x ∈ right.block) : left.block = right.block := by
  obtain ⟨originalLeft, originalLeftMember, leftEqual⟩ := List.mem_map.mp leftMember
  obtain ⟨originalRight, originalRightMember, rightEqual⟩ := List.mem_map.mp rightMember
  subst left
  subst right
  change tagBlock marked originalLeft.block = tagBlock marked originalRight.block
  change x ∈ tagBlock marked originalLeft.block at xLeft
  change x ∈ tagBlock marked originalRight.block at xRight
  cases x with
  | zero =>
      rw [(tagBlock_zero_mem marked originalLeft.block).mp xLeft,
        (tagBlock_zero_mem marked originalRight.block).mp xRight]
  | succ old =>
      have equal := overlapClosed_members chain closed originalLeft originalLeftMember
        originalRight originalRightMember old
        ((tagBlock_succ_mem marked originalLeft.block old).mp xLeft)
        ((tagBlock_succ_mem marked originalRight.block old).mp xRight)
      rw [equal]

theorem OverlapClosed.tag {chain : List Slot} (closed : OverlapClosed chain) (marked : List Nat) :
    OverlapClosed (chain.map (tagSlot marked)) := by
  intro before middle after g1 g2 left right x shape xLeft xRight
  have leftMember : (⟨g1, left⟩ : Slot) ∈ chain.map (tagSlot marked) := by rw [shape]; simp
  have rightMember : (⟨g2, right⟩ : Slot) ∈ chain.map (tagSlot marked) := by rw [shape]; simp
  exact tag_overlap_members marked chain closed ⟨g1, left⟩ ⟨g2, right⟩ leftMember rightMember x xLeft xRight

private theorem decode_tagChain (marked : List Nat) (chain : List Slot) :
    (chain.map (tagSlot marked)).map decodeSlot = chain := by
  induction chain with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, decode_tagSlot, ih]

private theorem tagged_block_range (marked : List Nat) (chain : List Slot) (slot : Slot)
    (member : slot ∈ chain.map (tagSlot marked)) : tagBlock marked (decodeBlock slot.block) = slot.block := by
  obtain ⟨original, _, equal⟩ := List.mem_map.mp member
  subst slot
  change tagBlock marked (decodeBlock (tagBlock marked original.block)) = tagBlock marked original.block
  rw [decode_tagBlock]

theorem CrossingClosed.tag {chain : List Slot} (closed : CrossingClosed chain) (marked : List Nat) :
    CrossingClosed (chain.map (tagSlot marked)) := by
  intro before middle1 middle2 middle3 after g1 g2 g3 g4 left right shape
  have decoded := congrArg (List.map decodeSlot) shape
  rw [decode_tagChain] at decoded
  have originalShape : chain = before.map decodeSlot ++
      (⟨g1.map Nat.pred, decodeBlock left⟩ :: (middle1.map decodeSlot ++
      (⟨g2.map Nat.pred, decodeBlock right⟩ :: (middle2.map decodeSlot ++
      (⟨g3.map Nat.pred, decodeBlock left⟩ :: (middle3.map decodeSlot ++
      (⟨g4.map Nat.pred, decodeBlock right⟩ :: after.map decodeSlot))))))) := by
    simpa only [List.map_append, List.map_cons, decodeSlot] using decoded
  have equal := closed (before.map decodeSlot) (middle1.map decodeSlot) (middle2.map decodeSlot)
    (middle3.map decodeSlot) (after.map decodeSlot) (g1.map Nat.pred) (g2.map Nat.pred)
    (g3.map Nat.pred) (g4.map Nat.pred) (decodeBlock left) (decodeBlock right) originalShape
  have leftMember : (⟨g1, left⟩ : Slot) ∈ chain.map (tagSlot marked) := by rw [shape]; simp
  have rightMember : (⟨g2, right⟩ : Slot) ∈ chain.map (tagSlot marked) := by rw [shape]; simp
  calc
    left = tagBlock marked (decodeBlock left) := (tagged_block_range marked chain ⟨g1, left⟩ leftMember).symm
    _ = tagBlock marked (decodeBlock right) := congrArg (tagBlock marked) equal
    _ = right := tagged_block_range marked chain ⟨g2, right⟩ rightMember

theorem CanonicalChain.tag {alphabet : List Nat} {chain : List Slot}
    (canonical : CanonicalChain alphabet chain) (marked : List Nat) :
    CanonicalChain (0 :: alphabet.map Nat.succ) (chain.map (tagSlot marked)) := by
  refine ⟨?_, canonical.2.1.tag marked, canonical.2.2.tag marked⟩
  intro slot member
  obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
  subst slot
  exact (canonical.1 original originalMember).tag marked

/-- A tag on an occurring block is globally nonsimple. Every old letter's exact
count is preserved, not merely its support or capped multiplicity. -/
theorem CanonicalWitness.tag {whole alphabet : List Nat} {first : Slot} {rest : List Slot}
    (witness : CanonicalWitness whole alphabet first rest) (marked : List Nat)
    (present : BlockOccurs marked (first :: rest)) :
    CanonicalWitness (render ((first :: rest).map (tagSlot marked)))
      (0 :: alphabet.map Nat.succ) (tagSlot marked first) (rest.map (tagSlot marked)) := by
  obtain ⟨alphabetOrdered, _, exactAlphabet, restNonempty, firstEmpty, laterNonempty,
    gapsSimple, canonical, rendered⟩ := witness
  let taggedWhole := render ((first :: rest).map (tagSlot marked))
  have counts : ∀ x, taggedWhole.count x.succ = whole.count x := by
    intro x
    simpa only [taggedWhole, rendered] using tag_render_succ_count marked (first :: rest) x
  have members : ∀ x, x.succ ∈ taggedWhole ↔ x ∈ whole := by
    intro x
    simpa only [taggedWhole, rendered] using tag_render_succ_mem marked (first :: rest) x
  have ordered : (0 :: alphabet.map Nat.succ).Pairwise (· < ·) := by
    apply List.pairwise_cons.mpr
    constructor
    · intro x member
      obtain ⟨old, _, equal⟩ := List.mem_map.mp member
      subst x
      exact Nat.zero_lt_succ old
    · simpa only [List.pairwise_map, Nat.succ_lt_succ_iff] using alphabetOrdered
  have nodup : (0 :: alphabet.map Nat.succ).Nodup :=
    List.nodup_iff_pairwise_ne.mpr (ordered.imp (fun less => Nat.ne_of_lt less))
  refine ⟨ordered, nodup, ?_, ?_, ?_, ?_, ?_, canonical.tag marked, rfl⟩
  · intro x
    cases x with
    | zero =>
        have bound : 2 ≤ taggedWhole.count 0 := tag_render_zero_count_ge_two marked (first :: rest) present
        have member : 0 ∈ taggedWhole := List.count_pos_iff.mp (by omega)
        have nonsimple : taggedWhole.count 0 ≠ 1 := by omega
        constructor
        · intro _
          exact ⟨member, nonsimple⟩
        · intro _
          exact List.Mem.head _
    | succ old =>
        have alphabetMember : old.succ ∈ 0 :: alphabet.map Nat.succ ↔ old ∈ alphabet := by simp
        change old.succ ∈ 0 :: alphabet.map Nat.succ ↔ old.succ ∈ taggedWhole ∧ taggedWhole.count old.succ ≠ 1
        rw [alphabetMember, members old, counts old]
        exact exactAlphabet old
  · intro empty
    have lengths := congrArg List.length empty
    simp only [List.length_map, List.length_nil] at lengths
    exact restNonempty (List.eq_nil_of_length_eq_zero lengths)
  · change first.gap.map Nat.succ = []
    rw [firstEmpty]
    rfl
  · intro slot member empty
    obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
    subst slot
    have lengths := congrArg List.length empty
    change (original.gap.map Nat.succ).length = 0 at lengths
    rw [List.length_map] at lengths
    exact laterNonempty original originalMember (List.eq_nil_of_length_eq_zero lengths)
  · intro slot member x inGap
    change slot ∈ (first :: rest).map (tagSlot marked) at member
    obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
    subst slot
    change x ∈ original.gap.map Nat.succ at inGap
    obtain ⟨old, oldMember, equal⟩ := List.mem_map.mp inGap
    subst x
    change taggedWhole.count old.succ = 1
    rw [counts old]
    exact gapsSimple original originalMember old oldMember

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.tag_overlap_members
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.OverlapClosed.tag
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CrossingClosed.tag
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalChain.tag
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.tag

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
