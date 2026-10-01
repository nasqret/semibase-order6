import SemigroupBasis.CoRoots.Order6SporadicSection14Separators
import SemigroupBasis.CoRoots.S5_870Invariant

namespace SemigroupBasis.CoRoots.Order6SporadicSection14

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_870

/-! ## Explicit canonical block representations -/

def keepBlock (block : FirstOccurrenceGapBlock) :
    FirstOccurrenceGapBlock :=
  { marker := block.marker, seconds := keepLast block.seconds }

def cleanBlock (block : FirstOccurrenceGapBlock) :
    FirstOccurrenceGapBlock :=
  { marker := block.marker, seconds := cleanCurrent block }

def alphaCanonicalBlocks :
    List FirstOccurrenceGapBlock -> List FirstOccurrenceGapBlock
  | [] => []
  | [block] => [keepBlock block]
  | block :: next :: rest =>
      cleanBlock block :: alphaCanonicalBlocks (next :: rest)

def cleanCanonicalBlocks
    (blocks : List FirstOccurrenceGapBlock) :
    List FirstOccurrenceGapBlock :=
  blocks.map cleanBlock

def betaCanonicalBlocks :
    List FirstOccurrenceGapBlock -> List FirstOccurrenceGapBlock
  | [] => []
  | [block] => [keepBlock block]
  | block :: next :: rest =>
      cleanCanonicalBlocks (block :: next :: rest)

theorem render_alphaCanonicalBlocks :
    forall blocks : List FirstOccurrenceGapBlock,
      renderGapBlocks (alphaCanonicalBlocks blocks) =
        renderAlphaCanonical blocks
  | [] => rfl
  | [block] => by
      simp [alphaCanonicalBlocks, keepBlock, renderGapBlocks,
        renderAlphaCanonical]
  | block :: next :: rest => by
      simp only [alphaCanonicalBlocks, renderGapBlocks,
        cleanBlock, renderAlphaCanonical]
      rw [render_alphaCanonicalBlocks (next :: rest)]

theorem render_cleanCanonicalBlocks :
    forall blocks : List FirstOccurrenceGapBlock,
      renderGapBlocks (cleanCanonicalBlocks blocks) =
        renderCleanCanonical blocks
  | [] => rfl
  | block :: rest => by
      simp only [cleanCanonicalBlocks, List.map_cons, renderGapBlocks,
        cleanBlock, renderCleanCanonical]
      simpa only [cleanCanonicalBlocks] using
        congrArg (fun suffix =>
          block.marker :: (cleanCurrent block ++ suffix))
          (render_cleanCanonicalBlocks rest)

theorem render_betaCanonicalBlocks :
    forall blocks : List FirstOccurrenceGapBlock,
      renderGapBlocks (betaCanonicalBlocks blocks) =
        renderBetaCanonical blocks
  | [] => rfl
  | [block] => by
      simp [betaCanonicalBlocks, keepBlock, renderGapBlocks,
        renderBetaCanonical]
  | block :: next :: rest => by
      simpa [betaCanonicalBlocks] using
        render_cleanCanonicalBlocks (block :: next :: rest)

theorem markers_alphaCanonicalBlocks :
    forall blocks : List FirstOccurrenceGapBlock,
      gapBlockMarkers (alphaCanonicalBlocks blocks) =
        gapBlockMarkers blocks
  | [] => rfl
  | [block] => rfl
  | block :: next :: rest => by
      simp only [alphaCanonicalBlocks, gapBlockMarkers, List.map_cons,
        cleanBlock, FirstOccurrenceGapBlock.marker]
      congr 1
      simpa [gapBlockMarkers] using
        markers_alphaCanonicalBlocks (next :: rest)

theorem markers_cleanCanonicalBlocks
    (blocks : List FirstOccurrenceGapBlock) :
    gapBlockMarkers (cleanCanonicalBlocks blocks) =
      gapBlockMarkers blocks := by
  induction blocks with
  | nil => rfl
  | cons block rest induction =>
      simp [cleanCanonicalBlocks, cleanBlock, gapBlockMarkers, induction]

theorem markers_betaCanonicalBlocks :
    forall blocks : List FirstOccurrenceGapBlock,
      gapBlockMarkers (betaCanonicalBlocks blocks) =
        gapBlockMarkers blocks
  | [] => rfl
  | [block] => rfl
  | block :: next :: rest => by
      simpa [betaCanonicalBlocks] using
        markers_cleanCanonicalBlocks (block :: next :: rest)

/-- A reduced gap is empty or consists of one allowed earlier marker. -/
def ChoiceIn (allowed : List Nat) (seconds : List Nat) : Prop :=
  seconds = [] ∨
    ∃ selected, selected ∈ allowed ∧ seconds = [selected]

private theorem keepLast_choice
    (allowed letters : List Nat)
    (known : forall letter, letter ∈ letters -> letter ∈ allowed) :
    ChoiceIn allowed (keepLast letters) := by
  induction letters with
  | nil => exact Or.inl (by simp [keepLast])
  | cons first rest induction =>
      cases rest with
      | nil =>
          exact Or.inr
            ⟨first, known first (by simp), by simp [keepLast]⟩
      | cons second tail =>
          simpa [keepLast] using
            induction (fun letter member =>
              known letter (List.Mem.tail first member))

private theorem cleanCurrent_choice
    (seen : List Nat) (block : FirstOccurrenceGapBlock)
    (known : forall letter, letter ∈ block.seconds ->
      letter ∈ block.marker :: seen) :
    ChoiceIn seen (cleanCurrent block) := by
  rcases keepLast_choice (block.marker :: seen) block.seconds known with
    empty | ⟨selected, selectedKnown, selectedShape⟩
  · left
    simp [cleanCurrent, empty]
  · by_cases atMarker : selected = block.marker
    · subst selected
      left
      simp [cleanCurrent, selectedShape]
    · right
      refine ⟨selected, ?_, ?_⟩
      · exact (List.mem_cons.mp selectedKnown).resolve_left atMarker
      · simp [cleanCurrent, selectedShape, atMarker]

/-- Every block is clean: its optional retained marker comes from the
strictly earlier marker list. -/
inductive CleanBlocks :
    List Nat -> List FirstOccurrenceGapBlock -> Prop
  | nil (seen : List Nat) : CleanBlocks seen []
  | cons (seen : List Nat) (block : FirstOccurrenceGapBlock)
      (rest : List FirstOccurrenceGapBlock)
      (markerFresh : block.marker ∉ seen)
      (choice : ChoiceIn seen block.seconds)
      (tail : CleanBlocks (block.marker :: seen) rest) :
      CleanBlocks seen (block :: rest)

/-- Alpha blocks are clean except that the terminal block may retain its own
marker. -/
inductive AlphaBlocks :
    List Nat -> List FirstOccurrenceGapBlock -> Prop
  | nil (seen : List Nat) : AlphaBlocks seen []
  | last (seen : List Nat) (block : FirstOccurrenceGapBlock)
      (markerFresh : block.marker ∉ seen)
      (choice : ChoiceIn (block.marker :: seen) block.seconds) :
      AlphaBlocks seen [block]
  | cons (seen : List Nat) (block next : FirstOccurrenceGapBlock)
      (rest : List FirstOccurrenceGapBlock)
      (markerFresh : block.marker ∉ seen)
      (choice : ChoiceIn seen block.seconds)
      (tail : AlphaBlocks (block.marker :: seen) (next :: rest)) :
      AlphaBlocks seen (block :: next :: rest)

/-- Beta blocks either contain at most one marker, where `x` and `x^2` are
both retained, or contain at least two markers and are clean throughout. -/
inductive BetaBlocks :
    List Nat -> List FirstOccurrenceGapBlock -> Prop
  | nil (seen : List Nat) : BetaBlocks seen []
  | single (seen : List Nat) (block : FirstOccurrenceGapBlock)
      (markerFresh : block.marker ∉ seen)
      (choice : ChoiceIn (block.marker :: seen) block.seconds) :
      BetaBlocks seen [block]
  | many (seen : List Nat) (block next : FirstOccurrenceGapBlock)
      (rest : List FirstOccurrenceGapBlock)
      (clean : CleanBlocks seen (block :: next :: rest)) :
      BetaBlocks seen (block :: next :: rest)

namespace CleanBlocks

theorem wellFormed
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (normal : CleanBlocks seen blocks) :
    GapBlocksWellFormed seen blocks := by
  induction normal with
  | nil seen => exact GapBlocksWellFormed.nil seen
  | cons seen block rest markerFresh choice tail induction =>
      apply GapBlocksWellFormed.cons seen block rest markerFresh
      · intro letter member
        rcases choice with empty | ⟨selected, selectedSeen, shape⟩
        · simp [empty] at member
        · rw [shape] at member
          simp only [List.mem_singleton] at member
          subst letter
          exact List.Mem.tail block.marker selectedSeen
      · exact induction

end CleanBlocks

namespace AlphaBlocks

theorem wellFormed
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (normal : AlphaBlocks seen blocks) :
    GapBlocksWellFormed seen blocks := by
  induction normal with
  | nil seen => exact GapBlocksWellFormed.nil seen
  | last seen block markerFresh choice =>
      apply GapBlocksWellFormed.cons seen block [] markerFresh
      · intro letter member
        rcases choice with empty | ⟨selected, selectedSeen, shape⟩
        · simp [empty] at member
        · rw [shape] at member
          simp only [List.mem_singleton] at member
          subst letter
          exact selectedSeen
      · exact GapBlocksWellFormed.nil (block.marker :: seen)
  | cons seen block next rest markerFresh choice tail induction =>
      apply GapBlocksWellFormed.cons seen block (next :: rest) markerFresh
      · intro letter member
        rcases choice with empty | ⟨selected, selectedSeen, shape⟩
        · simp [empty] at member
        · rw [shape] at member
          simp only [List.mem_singleton] at member
          subst letter
          exact List.Mem.tail block.marker selectedSeen
      · exact induction

end AlphaBlocks

namespace BetaBlocks

theorem wellFormed
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (normal : BetaBlocks seen blocks) :
    GapBlocksWellFormed seen blocks := by
  cases normal with
  | nil => exact GapBlocksWellFormed.nil seen
  | single block markerFresh choice =>
      apply GapBlocksWellFormed.cons seen block [] markerFresh
      · intro letter member
        rcases choice with empty | ⟨selected, selectedSeen, shape⟩
        · simp [empty] at member
        · rw [shape] at member
          simp only [List.mem_singleton] at member
          subst letter
          exact selectedSeen
      · exact GapBlocksWellFormed.nil (block.marker :: seen)
  | many block next rest clean =>
      exact CleanBlocks.wellFormed clean

end BetaBlocks

theorem cleanCanonicalBlocks_normal
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks) :
    CleanBlocks seen (cleanCanonicalBlocks blocks) := by
  induction formed with
  | nil seen => exact CleanBlocks.nil seen
  | cons seen block rest markerFresh secondsSeen tail induction =>
      exact CleanBlocks.cons seen (cleanBlock block)
        (cleanCanonicalBlocks rest) markerFresh
        (cleanCurrent_choice seen block secondsSeen) induction

theorem alphaCanonicalBlocks_normal
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks) :
    AlphaBlocks seen (alphaCanonicalBlocks blocks) := by
  cases formed with
  | nil seen => exact AlphaBlocks.nil seen
  | cons seen block rest markerFresh secondsSeen tail =>
      cases rest with
      | nil =>
          exact AlphaBlocks.last seen (keepBlock block) markerFresh
            (keepLast_choice (block.marker :: seen) block.seconds
              secondsSeen)
      | cons next remaining =>
          cases remaining with
          | nil =>
              exact AlphaBlocks.cons seen (cleanBlock block)
                (keepBlock next) [] markerFresh
                (cleanCurrent_choice seen block secondsSeen)
                (alphaCanonicalBlocks_normal tail)
          | cons third remaining =>
              exact AlphaBlocks.cons seen (cleanBlock block)
                (cleanBlock next)
                (alphaCanonicalBlocks (third :: remaining)) markerFresh
                (cleanCurrent_choice seen block secondsSeen)
                (alphaCanonicalBlocks_normal tail)

theorem betaCanonicalBlocks_normal
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks) :
    BetaBlocks seen (betaCanonicalBlocks blocks) := by
  cases formed with
  | nil seen => exact BetaBlocks.nil seen
  | cons seen block rest markerFresh secondsSeen tail =>
      cases rest with
      | nil =>
          exact BetaBlocks.single seen (keepBlock block) markerFresh
            (keepLast_choice (block.marker :: seen) block.seconds
              secondsSeen)
      | cons next remaining =>
          exact BetaBlocks.many seen (cleanBlock block)
            (cleanBlock next) (cleanCanonicalBlocks remaining) <| by
              simpa [cleanCanonicalBlocks] using
                cleanCanonicalBlocks_normal
                  (GapBlocksWellFormed.cons seen block
                    (next :: remaining) markerFresh secondsSeen tail)

theorem alphaCanonicalWord_toList_blocks (word : Word Nat) :
    (alphaCanonicalWord word).toList =
      renderGapBlocks
        (alphaCanonicalBlocks (gapBlocksList word.toList)) := by
  rw [alphaCanonicalWord_toList]
  simp [alphaCanonicalList, render_alphaCanonicalBlocks]

theorem betaCanonicalWord_toList_blocks (word : Word Nat) :
    (betaCanonicalWord word).toList =
      renderGapBlocks
        (betaCanonicalBlocks (gapBlocksList word.toList)) := by
  rw [betaCanonicalWord_toList]
  simp [betaCanonicalList, render_betaCanonicalBlocks]

end SemigroupBasis.CoRoots.Order6SporadicSection14
