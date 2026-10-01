import SemigroupBasis.CoRoots.Order6SporadicSection18BlockPartition

/-! Fresh-square tagging for the canonical adjacency argument. Old letters
are shifted by Nat.succ; zero is adjoined exactly to the chosen block label.
This module is combinatorial and makes no adjacency or semantic-transfer claim. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

def tagBlock (marked block : List Nat) : List Nat :=
  if block = marked then 0 :: block.map Nat.succ else block.map Nat.succ

def tagSlot (marked : List Nat) (slot : Slot) : Slot :=
  ⟨slot.gap.map Nat.succ, tagBlock marked slot.block⟩

def decodeLetter : Nat → Option Nat
  | 0 => none
  | Nat.succ x => some x

def decodeBlock (block : List Nat) : List Nat := block.filterMap decodeLetter

def decodeSlot (slot : Slot) : Slot := ⟨slot.gap.map Nat.pred, decodeBlock slot.block⟩

theorem tagBlock_succ_mem (marked block : List Nat) (x : Nat) :
    x.succ ∈ tagBlock marked block ↔ x ∈ block := by
  by_cases equal : block = marked <;> simp [tagBlock, equal]

theorem tagBlock_zero_mem (marked block : List Nat) :
    0 ∈ tagBlock marked block ↔ block = marked := by
  by_cases equal : block = marked <;> simp [tagBlock, equal]

private theorem decode_shift (block : List Nat) : decodeBlock (block.map Nat.succ) = block := by
  induction block with
  | nil => rfl
  | cons head tail ih =>
      simpa only [decodeBlock, List.map_cons, List.filterMap_cons, decodeLetter] using
        congrArg (List.cons head) ih

theorem decode_tagBlock (marked block : List Nat) : decodeBlock (tagBlock marked block) = block := by
  by_cases equal : block = marked
  · simpa only [tagBlock, if_pos equal, decodeBlock, List.filterMap_cons, decodeLetter] using decode_shift block
  · simpa only [tagBlock, if_neg equal] using decode_shift block

theorem tagBlock_injective (marked : List Nat) : Function.Injective (tagBlock marked) := by
  intro left right equal
  have decoded := congrArg decodeBlock equal
  simpa only [decode_tagBlock] using decoded

theorem decode_tagSlot (marked : List Nat) (slot : Slot) : decodeSlot (tagSlot marked slot) = slot := by
  cases slot with
  | mk gap block =>
      simp [decodeSlot, tagSlot, decode_tagBlock, List.map_map, Function.comp_def]

theorem normalize_tagBlock (marked alphabet block : List Nat) :
    normalizeBlock (0 :: alphabet.map Nat.succ) (tagBlock marked block) =
      if block = marked then 0 :: (normalizeBlock alphabet block).map Nat.succ
      else (normalizeBlock alphabet block).map Nat.succ := by
  have filtered : (alphabet.map Nat.succ).filter (fun x => decide (x ∈ tagBlock marked block)) =
      (alphabet.filter (fun x => decide (x ∈ block))).map Nat.succ := by
    induction alphabet with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons, List.filter_cons, tagBlock_succ_mem, ih]
        by_cases member : head ∈ block <;> simp [member]
  unfold normalizeBlock
  rw [List.filter_cons, filtered]
  by_cases equal : block = marked <;> simp [tagBlock_zero_mem, equal]

theorem GoodBlock.tag {alphabet block : List Nat} (good : GoodBlock alphabet block) (marked : List Nat) :
    GoodBlock (0 :: alphabet.map Nat.succ) (tagBlock marked block) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨head, tail, shape⟩ := List.exists_cons_of_ne_nil good.1
    have member : head.succ ∈ tagBlock marked block := (tagBlock_succ_mem marked block head).mpr (by simp [shape])
    intro empty
    rw [empty] at member
    cases member
  · rw [normalize_tagBlock, good.2]
    rfl

theorem shift_count (letters : List Nat) (x : Nat) :
    (letters.map Nat.succ).count x.succ = letters.count x := by
  induction letters with
  | nil => rfl
  | cons head tail ih =>
      by_cases equal : head = x <;> simp [equal, ih]

private theorem tagBlock_succ_count (marked block : List Nat) (x : Nat) :
    (tagBlock marked block).count x.succ = block.count x := by
  by_cases equal : block = marked <;> simp [tagBlock, equal, shift_count]

theorem squareList_count (block : List Nat) (x : Nat) :
    (squareList block).count x = 2 * block.count x := by
  induction block with
  | nil => rfl
  | cons head tail ih =>
      by_cases equal : head = x <;>
        simp [squareList_cons, equal, ih] <;> omega

theorem render_block_count_ge_two (chain : List Slot) (slot : Slot) (member : slot ∈ chain)
    (x : Nat) (inBlock : x ∈ slot.block) : 2 ≤ (render chain).count x := by
  obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp member
  have positive := List.count_pos_iff.mpr inBlock
  rw [shape, render_append]
  simp only [render, List.count_append, squareList_count]
  omega

theorem tag_render_succ_count (marked : List Nat) (chain : List Slot) (x : Nat) :
    (render (chain.map (tagSlot marked))).count x.succ = (render chain).count x := by
  induction chain with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, render, tagSlot, List.count_append,
        squareList_count, tagBlock_succ_count, shift_count, ih]

theorem tag_render_succ_mem (marked : List Nat) (chain : List Slot) (x : Nat) :
    x.succ ∈ render (chain.map (tagSlot marked)) ↔ x ∈ render chain := by
  rw [← List.count_pos_iff, ← List.count_pos_iff, tag_render_succ_count]

theorem tag_render_zero_count_ge_two (marked : List Nat) (chain : List Slot)
    (present : BlockOccurs marked chain) : 2 ≤ (render (chain.map (tagSlot marked))).count 0 := by
  obtain ⟨slot, member, blockEqual⟩ := present
  apply render_block_count_ge_two (chain.map (tagSlot marked)) (tagSlot marked slot)
    (List.mem_map.mpr ⟨slot, member, rfl⟩) 0
  change 0 ∈ tagBlock marked slot.block
  exact (tagBlock_zero_mem marked slot.block).mpr blockEqual

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.tagBlock_succ_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.tagBlock_zero_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.decode_tagBlock
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.tagBlock_injective
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.decode_tagSlot
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.normalize_tagBlock
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.GoodBlock.tag
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.shift_count
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.squareList_count
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.render_block_count_ge_two
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.tag_render_succ_count
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.tag_render_succ_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.tag_render_zero_count_ge_two

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
