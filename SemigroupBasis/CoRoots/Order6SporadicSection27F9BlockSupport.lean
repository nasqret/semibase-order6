import SemigroupBasis.CoRoots.Order6Hull21_1BlockFacts
import SemigroupBasis.CoRoots.Order6SporadicSection27F9G1Canonical

namespace SemigroupBasis.CoRoots.Order6SporadicSection27
namespace F9BlockSupport

open SemigroupBasis.CoRoots.S5_870
open SemigroupBasis.CoRoots.Order6Hull21_1BlockFacts

/-!
## First-occurrence block support and chronology

These facts connect rendered-prefix membership with the marker order used by
the literal condition-(II)/(III) frames.  They are independent of the F9
multiplication table and certificate layer.
-/

/-- A rendered block list has exactly the union of its marker and gap-letter
supports. -/
theorem mem_renderGapBlocks_iff
    (tested : Nat) (blocks : List FirstOccurrenceGapBlock) :
    tested ∈ renderGapBlocks blocks ↔
      tested ∈ gapBlockMarkers blocks ∨
        tested ∈ gapBlockSeconds blocks := by
  induction blocks with
  | nil =>
      simp [renderGapBlocks, gapBlockMarkers, gapBlockSeconds]
  | cons block rest induction =>
      change
        tested ∈ block.marker :: (block.seconds ++ renderGapBlocks rest) ↔
          tested ∈ block.marker :: gapBlockMarkers rest ∨
            tested ∈ block.seconds ++ gapBlockSeconds rest
      simp only [List.mem_cons, List.mem_append, induction]
      constructor
      · intro member
        rcases member with atMarker | remainder
        · exact Or.inl (Or.inl atMarker)
        · rcases remainder with inSeconds | remainder
          · exact Or.inr (Or.inl inSeconds)
          · rcases remainder with inMarkers | inRest
            · exact Or.inl (Or.inr inMarkers)
            · exact Or.inr (Or.inr inRest)
      · intro member
        rcases member with inMarkers | remainder
        · rcases inMarkers with atMarker | inRestMarkers
          · exact Or.inl atMarker
          · exact Or.inr (Or.inr (Or.inl inRestMarkers))
        · rcases remainder with inSeconds | inRestSeconds
          · exact Or.inr (Or.inl inSeconds)
          · exact Or.inr (Or.inr (Or.inr inRestSeconds))

/-- Every letter in a rendered well-formed prefix is one of that prefix's
first-occurrence markers. -/
private theorem marker_mem_of_mem_renderGapBlocks
    {blocks : List FirstOccurrenceGapBlock} {tested : Nat}
    (formed : GapBlocksWellFormed [] blocks)
    (member : tested ∈ renderGapBlocks blocks) :
    tested ∈ gapBlockMarkers blocks := by
  rcases (mem_renderGapBlocks_iff tested blocks).mp member with
    inMarkers | inSeconds
  · exact inMarkers
  · exact
      (formed.secondsInSeenOrMarkers tested inSeconds).resolve_left (by simp)

/-- A marker belonging to a later block cannot occur in the rendered strict
prefix. -/
theorem tailMarker_not_mem_renderGapBlocks
    {priorBlocks tailBlocks : List FirstOccurrenceGapBlock}
    {marker : Nat}
    (formed : GapBlocksWellFormed [] (priorBlocks ++ tailBlocks))
    (markerInTail : marker ∈ gapBlockMarkers tailBlocks) :
    marker ∉ renderGapBlocks priorBlocks := by
  obtain ⟨priorFormed, tailFormed⟩ :=
    gapBlocksWellFormed_append
      (left := priorBlocks) (right := tailBlocks) formed
  have markerNotSeen :
      marker ∉ seenAfterGapBlocks [] priorBlocks := by
    intro inSeen
    exact tailFormed.markersAvoidSeen marker inSeen markerInTail
  have markerNotPriorMarkers : marker ∉ gapBlockMarkers priorBlocks := by
    simpa [seenAfterGapBlocks] using markerNotSeen
  have markerNotPriorSeconds : marker ∉ gapBlockSeconds priorBlocks := by
    intro inSeconds
    rcases priorFormed.secondsInSeenOrMarkers marker inSeconds with
      inSeen | inMarkers
    · simp at inSeen
    · exact markerNotPriorMarkers inMarkers
  intro rendered
  rcases (mem_renderGapBlocks_iff marker priorBlocks).mp rendered with
    inMarkers | inSeconds
  · exact markerNotPriorMarkers inMarkers
  · exact markerNotPriorSeconds inSeconds

/-- In particular, the marker that starts the next block is absent from the
rendered blocks before it. -/
theorem futureMarker_not_mem_renderGapBlocks
    {priorBlocks : List FirstOccurrenceGapBlock}
    {nextBlock : FirstOccurrenceGapBlock}
    {rest : List FirstOccurrenceGapBlock}
    (formed :
      GapBlocksWellFormed [] (priorBlocks ++ nextBlock :: rest)) :
    nextBlock.marker ∉ renderGapBlocks priorBlocks := by
  exact tailMarker_not_mem_renderGapBlocks
    (priorBlocks := priorBlocks) (tailBlocks := nextBlock :: rest)
    formed (by simp [gapBlockMarkers])

/-- A rendered-prefix letter precedes every marker in the displayed block
suffix in literal first-occurrence order. -/
theorem earlierIn_of_mem_renderGapBlocks_prefix
    {priorBlocks tailBlocks : List FirstOccurrenceGapBlock}
    {earlier later : Nat}
    (formed : GapBlocksWellFormed [] (priorBlocks ++ tailBlocks))
    (earlierMember : earlier ∈ renderGapBlocks priorBlocks)
    (laterMarker : later ∈ gapBlockMarkers tailBlocks) :
    EarlierIn (gapBlockMarkers (priorBlocks ++ tailBlocks))
      earlier later := by
  obtain ⟨priorFormed, _⟩ :=
    gapBlocksWellFormed_append
      (left := priorBlocks) (right := tailBlocks) formed
  have earlierMarker : earlier ∈ gapBlockMarkers priorBlocks :=
    marker_mem_of_mem_renderGapBlocks priorFormed earlierMember
  obtain ⟨before, priorAfter, priorShape⟩ :=
    List.mem_iff_append.mp earlierMarker
  obtain ⟨tailBefore, after, tailShape⟩ :=
    List.mem_iff_append.mp laterMarker
  refine ⟨before, priorAfter ++ tailBefore, after, ?_⟩
  rw [gapBlockMarkers_append, priorShape, tailShape]
  simp [List.append_assoc]

end F9BlockSupport
end SemigroupBasis.CoRoots.Order6SporadicSection27
