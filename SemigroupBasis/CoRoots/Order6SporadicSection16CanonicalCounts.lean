import SemigroupBasis.CoRoots.Order6SporadicSection16CanonicalIni

/-! Exact multiplicities in the Section16 canonical renderer. Prefix
variables occur once, the anchor occurs at least twice, and each distinct
block label occurs exactly once or twice according to its doubled flag.
These are the representation-boundary facts needed by canonical uniqueness. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16.CanonicalCounts

open SemigroupBasis
open CanonicalIni

def blockMultiplicity (block : CanonicalBlock) : Nat := if block.doubled then 2 else 1

theorem count_renderBlock (anchor letter : Nat) (block : CanonicalBlock) (notAnchor : letter ≠ anchor) :
    (renderBlock anchor block).count letter = if block.letter = letter then blockMultiplicity block else 0 := by
  cases doubled : block.doubled <;> cases marker : block.markerAfter <;>
    by_cases same : block.letter = letter <;>
      simp [renderBlock, blockMultiplicity, doubled, marker, same, Ne.symm notAnchor]

theorem count_renderBlocks_absent (anchor letter : Nat) (blocks : List CanonicalBlock)
    (notAnchor : letter ≠ anchor) (absent : letter ∉ blocks.map CanonicalBlock.letter) :
    (renderBlocks anchor blocks).count letter = 0 := by
  apply List.count_eq_zero.mpr
  intro member
  rcases renderBlocks_mem anchor letter blocks member with same | later
  · exact notAnchor same
  · exact absent later

theorem count_renderBlocks_own (anchor : Nat) (block : CanonicalBlock)
    (notAnchor : block.letter ≠ anchor) : ∀ blocks : List CanonicalBlock,
    (blocks.map CanonicalBlock.letter).Nodup → block ∈ blocks →
      (renderBlocks anchor blocks).count block.letter = blockMultiplicity block
  | [], _, member => by simp at member
  | first :: rest, distinct, member => by
      have nodup : (first.letter :: rest.map CanonicalBlock.letter).Nodup := distinct
      rcases List.mem_cons.mp member with same | later
      · subst first
        rw [renderBlocks_cons, List.count_append, count_renderBlock anchor block.letter block notAnchor,
          count_renderBlocks_absent anchor block.letter rest notAnchor (List.nodup_cons.mp nodup).1]
        simp
      · have different : first.letter ≠ block.letter := by
          intro same
          apply (List.nodup_cons.mp nodup).1
          exact List.mem_map.mpr ⟨block,later,same.symm⟩
        rw [renderBlocks_cons, List.count_append, count_renderBlock anchor block.letter first notAnchor,
          if_neg different, count_renderBlocks_own anchor block notAnchor rest (List.nodup_cons.mp nodup).2 later]
        simp

theorem canonicalLabels_nodup (data : CanonicalData) (wellFormed : CanonicalWellFormed data) :
    (data.initial ++ data.anchor :: data.blocks.map CanonicalBlock.letter).Nodup := by
  simpa [canonicalLabels, List.append_assoc] using wellFormed.1

theorem initial_absent_suffix (data : CanonicalData) (wellFormed : CanonicalWellFormed data)
    (letter : Nat) (inInitial : letter ∈ data.initial) :
    letter ∉ [data.anchor,data.anchor] ++ renderBlocks data.anchor data.blocks := by
  have parts := List.nodup_append.mp (canonicalLabels_nodup data wellFormed)
  intro member
  have inLabels : letter ∈ data.anchor :: data.blocks.map CanonicalBlock.letter := by
    rcases List.mem_append.mp member with inAnchor | inBlocks
    · have same : letter = data.anchor := by simpa using inAnchor
      exact List.mem_cons.mpr (Or.inl same)
    · rcases renderBlocks_mem data.anchor letter data.blocks inBlocks with same | later
      · exact List.mem_cons.mpr (Or.inl same)
      · exact List.mem_cons_of_mem data.anchor later
  exact parts.2.2 letter inInitial letter inLabels rfl

theorem count_initial (data : CanonicalData) (wellFormed : CanonicalWellFormed data)
    (letter : Nat) (inInitial : letter ∈ data.initial) :
    (renderCanonical data).count letter = 1 := by
  have parts := List.nodup_append.mp (canonicalLabels_nodup data wellFormed)
  have suffixZero := List.count_eq_zero.mpr (initial_absent_suffix data wellFormed letter inInitial)
  unfold renderCanonical
  rw [List.append_assoc, List.count_append, parts.1.count, if_pos inInitial, suffixZero]

theorem count_anchor (data : CanonicalData) : 2 ≤ (renderCanonical data).count data.anchor := by
  simp only [renderCanonical, List.count_append, List.count_cons_self, List.count_nil]
  omega

theorem block_freshness (data : CanonicalData) (wellFormed : CanonicalWellFormed data)
    (block : CanonicalBlock) (member : block ∈ data.blocks) :
    block.letter ∉ data.initial ∧ block.letter ≠ data.anchor := by
  have parts := List.nodup_append.mp (canonicalLabels_nodup data wellFormed)
  have labelMember : block.letter ∈ data.blocks.map CanonicalBlock.letter := List.mem_map.mpr ⟨block,member,rfl⟩
  constructor
  · intro initialMember
    exact parts.2.2 block.letter initialMember block.letter (List.mem_cons_of_mem data.anchor labelMember) rfl
  · intro same
    apply (List.nodup_cons.mp parts.2.1).1
    simpa only [same] using labelMember

theorem count_block (data : CanonicalData) (wellFormed : CanonicalWellFormed data)
    (block : CanonicalBlock) (member : block ∈ data.blocks) :
    (renderCanonical data).count block.letter = blockMultiplicity block := by
  have parts := List.nodup_append.mp (canonicalLabels_nodup data wellFormed)
  have fresh := block_freshness data wellFormed block member
  have initialZero := List.count_eq_zero.mpr fresh.1
  have anchorZero : [data.anchor,data.anchor].count block.letter = 0 := by simp [Ne.symm fresh.2]
  unfold renderCanonical
  rw [List.count_append, List.count_append, initialZero, anchorZero,
      count_renderBlocks_own data.anchor block fresh.2 data.blocks (List.nodup_cons.mp parts.2.1).2 member]
  simp only [Nat.zero_add]

theorem simple_block_iff (data : CanonicalData) (wellFormed : CanonicalWellFormed data)
    (block : CanonicalBlock) (member : block ∈ data.blocks) :
    (renderCanonical data).count block.letter = 1 ↔ block.doubled = false := by
  rw [count_block data wellFormed block member]
  cases doubled : block.doubled <;> simp [blockMultiplicity, doubled]

#print axioms count_initial
#print axioms count_anchor
#print axioms count_block
#print axioms simple_block_iff

end SemigroupBasis.CoRoots.Order6SporadicSection16.CanonicalCounts
