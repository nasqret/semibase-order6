import SemigroupBasis.CoRoots.S5_870GapBlocks

/-!
# Shared gap-block facts for Hull 21.1

This module collects the parser facts used by both parts of the Hull 21.1
normalization proof.  They are independent of the published identity basis:
append decomposition, well-formed suffix splitting, the count interpretation
of second occurrences, and support preservation under reversal of block order.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull21_1BlockFacts

abbrev GapBlock :=
  SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock

theorem renderGapBlocks_append
    (left right : List GapBlock) :
    SemigroupBasis.CoRoots.S5_870.renderGapBlocks (left ++ right) =
      SemigroupBasis.CoRoots.S5_870.renderGapBlocks left ++
        SemigroupBasis.CoRoots.S5_870.renderGapBlocks right := by
  induction left with
  | nil => rfl
  | cons block rest induction =>
      simp [SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
        induction, List.append_assoc]

theorem gapBlockMarkers_append
    (left right : List GapBlock) :
    SemigroupBasis.CoRoots.S5_870.gapBlockMarkers (left ++ right) =
      SemigroupBasis.CoRoots.S5_870.gapBlockMarkers left ++
        SemigroupBasis.CoRoots.S5_870.gapBlockMarkers right := by
  exact List.map_append

theorem gapBlockSeconds_append
    (left right : List GapBlock) :
    SemigroupBasis.CoRoots.S5_870.gapBlockSeconds (left ++ right) =
      SemigroupBasis.CoRoots.S5_870.gapBlockSeconds left ++
        SemigroupBasis.CoRoots.S5_870.gapBlockSeconds right := by
  exact List.flatMap_append

def seenAfterGapBlocks
    (seen : List Nat) (blocks : List GapBlock) : List Nat :=
  (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks).reverse ++
    seen

theorem gapBlocksWellFormed_append
    {seen : List Nat} {left right : List GapBlock}
    (formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed
        seen (left ++ right)) :
    SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed seen left ∧
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed
        (seenAfterGapBlocks seen left) right := by
  induction left generalizing seen with
  | nil =>
      exact
        ⟨SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed.nil seen,
          by simpa [seenAfterGapBlocks] using formed⟩
  | cons block rest induction =>
      cases formed with
      | cons _ _ _ markerFresh secondsSeen tailFormed =>
          obtain ⟨restFormed, rightFormed⟩ := induction tailFormed
          refine
            ⟨SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed.cons
                seen block rest markerFresh secondsSeen restFormed,
              ?_⟩
          simpa [seenAfterGapBlocks,
            SemigroupBasis.CoRoots.S5_870.gapBlockMarkers,
            List.append_assoc] using rightFormed

/-- A letter occurs in a gap precisely when its total multiplicity in the
rendered well-formed block list is at least two. -/
theorem mem_gapBlockSeconds_iff_two_le_count
    {blocks : List GapBlock}
    (formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed [] blocks)
    (tested : Nat) :
    tested ∈ SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks ↔
      2 ≤
        (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks).count
          tested := by
  rw [SemigroupBasis.CoRoots.S5_870.count_renderGapBlocks]
  have markersNodup := formed.markersNodup
  have markerCountLe :
      (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks).count
          tested ≤ 1 := by
    rw [markersNodup.count]
    split <;> omega
  constructor
  · intro inSeconds
    have inMarkers :
        tested ∈
          SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks :=
      (formed.secondsInSeenOrMarkers tested inSeconds).resolve_left
        (by simp)
    have markerCount :
        (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks).count
            tested = 1 := by
      rw [markersNodup.count]
      simp [inMarkers]
    have secondsPositive :
        0 <
          (SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks).count
            tested :=
      List.count_pos_iff.mpr inSeconds
    rw [markerCount]
    omega
  · intro total
    have secondsPositive :
        0 <
          (SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks).count
            tested := by
      omega
    exact List.count_pos_iff.mp secondsPositive

theorem mem_gapBlockSeconds_reverse
    (tested : Nat) :
    ∀ blocks : List GapBlock,
      tested ∈
          SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks.reverse ↔
        tested ∈
          SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks
  | [] => by
      simp [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds]
  | block :: rest => by
      simp [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
        List.flatMap_append, mem_gapBlockSeconds_reverse tested rest,
        or_comm]

theorem mem_reverse_before_append_last_seconds_iff
    (tested : Nat) (before : List GapBlock) (lastBlock : GapBlock) :
    tested ∈
        SemigroupBasis.CoRoots.S5_870.gapBlockSeconds before.reverse ++
          lastBlock.seconds ↔
      tested ∈
        SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
          (before ++ [lastBlock]) := by
  simp [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
    List.flatMap_append, mem_gapBlockSeconds_reverse tested, or_comm]

end Order6Hull21_1BlockFacts
end CoRoots
end SemigroupBasis
