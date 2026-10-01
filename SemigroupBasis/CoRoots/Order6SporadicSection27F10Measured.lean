import SemigroupBasis.CoRoots.Order6SporadicSection27F10Sparse
import SemigroupBasis.CoRoots.Order6SporadicSection27MeasuredSparsification

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27.F10

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_870

private abbrev ListDerives := S5_107.ListDerives basis

/-! ## Measured A/B/C sparsification -/

/-- Measured counterpart of `listDerivesSparseSeconds`.  It follows the same
A/B/C choices while recording that deleting one member of every collapsed
pair cannot increase `betaWeight`. -/
theorem listDerivesSparseSecondsMeasured
    (markers allowed suffix : List Nat) :
    ∀ (source stem : List Nat),
      (∀ letter, letter ∈ allowed → letter ∈ stem) →
      (∀ letter, letter ∈ source → letter ∈ allowed) →
      ∃ reduced,
        ChoiceIn allowed reduced ∧
          ListDerives
            (stem ++ source ++ suffix)
            (stem ++ reduced ++ suffix) ∧
          betaWeight markers (stem ++ reduced ++ suffix) ≤
            betaWeight markers (stem ++ source ++ suffix)
  | [], stem, _, _ => by
      exact ⟨[], Or.inl rfl,
        S5_107.ListDerives.refl (basis := basis) _, by simp⟩
  | letter :: rest, stem, allowedInStem, sourceAllowed => by
      have letterAllowed : letter ∈ allowed :=
        sourceAllowed letter (List.Mem.head rest)
      have letterSeen : letter ∈ stem :=
        allowedInStem letter letterAllowed
      have allowedInExtended :
          ∀ tested, tested ∈ allowed → tested ∈ stem ++ [letter] := by
        intro tested member
        exact List.mem_append.mpr <| Or.inl <|
          allowedInStem tested member
      have restAllowed :
          ∀ tested, tested ∈ rest → tested ∈ allowed := by
        intro tested member
        exact sourceAllowed tested (List.Mem.tail letter member)
      obtain ⟨reduced, choice, recurse, recurseWeight⟩ :=
        listDerivesSparseSecondsMeasured
          markers allowed suffix rest (stem ++ [letter])
          allowedInExtended restAllowed
      rcases choice with empty | ⟨selected, selectedAllowed, shape⟩
      · subst reduced
        refine ⟨[letter], Or.inr ⟨letter, letterAllowed, rfl⟩, ?_, ?_⟩
        · simpa [List.append_assoc] using recurse
        · simpa [List.append_assoc] using recurseWeight
      · subst reduced
        have selectedSeen : selected ∈ stem :=
          allowedInStem selected selectedAllowed
        obtain ⟨retained, retainedSide, collapse⟩ :=
          listDerivesCollapsePairAfterSeen
            stem suffix letter selected letterSeen selectedSeen
        have retainedAllowed : retained ∈ allowed := by
          rcases retainedSide with atLetter | atSelected
          · simpa [atLetter] using letterAllowed
          · simpa [atSelected] using selectedAllowed
        have recurseShape :
            ListDerives
              (stem ++ (letter :: rest) ++ suffix)
              (stem ++ [letter, selected] ++ suffix) := by
          simpa [List.append_assoc] using recurse
        have recurseWeightShape :
            betaWeight markers (stem ++ [letter, selected] ++ suffix) ≤
              betaWeight markers
                (stem ++ (letter :: rest) ++ suffix) := by
          simpa [List.append_assoc] using recurseWeight
        have collapseWeight :
            betaWeight markers (stem ++ [retained] ++ suffix) ≤
              betaWeight markers
                (stem ++ [letter, selected] ++ suffix) := by
          rcases retainedSide with atLetter | atSelected
          · subst retained
            simp only [betaWeight_append, betaWeight_cons, betaWeight_nil]
            omega
          · subst retained
            simp only [betaWeight_append, betaWeight_cons, betaWeight_nil]
            omega
        exact ⟨[retained],
          Or.inr ⟨retained, retainedAllowed, rfl⟩,
          recurseShape.trans collapse,
          Nat.le_trans collapseWeight recurseWeightShape⟩

/-- Lift measured sparsification through a well-formed gap-block list.  The
output remains sparse, retains the exact marker list, and has no larger
`betaWeight` in the complete rendered context. -/
theorem listDerivesSparseBlocksMeasured
    (markers : List Nat)
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks)
    (stem : List Nat)
    (seenInStem : ∀ letter, letter ∈ seen → letter ∈ stem) :
    ∃ targetBlocks,
      SparseBlocks seen targetBlocks ∧
        gapBlockMarkers targetBlocks = gapBlockMarkers blocks ∧
        ListDerives
          (stem ++ renderGapBlocks blocks)
          (stem ++ renderGapBlocks targetBlocks) ∧
        betaWeight markers (stem ++ renderGapBlocks targetBlocks) ≤
          betaWeight markers (stem ++ renderGapBlocks blocks) := by
  induction formed generalizing stem with
  | nil seen =>
      refine ⟨[], SparseBlocks.nil seen, rfl, ?_, ?_⟩
      · simpa [renderGapBlocks] using
          S5_107.ListDerives.refl (basis := basis) stem
      · simp [renderGapBlocks]
  | cons seen block rest markerFresh secondsSeen tailFormed induction =>
      have allowedInCurrentStem :
          ∀ letter, letter ∈ block.marker :: seen →
            letter ∈ stem ++ [block.marker] := by
        intro letter member
        rcases List.mem_cons.mp member with atMarker | inSeen
        · subst letter
          simp
        · exact List.mem_append.mpr <| Or.inl <|
            seenInStem letter inSeen
      obtain ⟨reduced, choice, current, currentWeightRaw⟩ :=
        listDerivesSparseSecondsMeasured
          markers (block.marker :: seen) (renderGapBlocks rest)
          block.seconds (stem ++ [block.marker])
          allowedInCurrentStem secondsSeen
      let nextStem := stem ++ [block.marker] ++ reduced
      have nextSeenInStem :
          ∀ letter, letter ∈ block.marker :: seen →
            letter ∈ nextStem := by
        intro letter member
        rcases List.mem_cons.mp member with atMarker | inSeen
        · subst letter
          simp [nextStem]
        · exact List.mem_append.mpr <| Or.inl <|
            List.mem_append.mpr <| Or.inl <|
              seenInStem letter inSeen
      obtain ⟨targetRest, sparseRest, markersRest,
          recurse, recurseWeightRaw⟩ :=
        induction nextStem nextSeenInStem
      let targetBlock : FirstOccurrenceGapBlock :=
        { marker := block.marker, seconds := reduced }
      have sparseAll : SparseBlocks seen (targetBlock :: targetRest) := by
        apply SparseBlocks.cons seen targetBlock targetRest
        · simpa [targetBlock] using markerFresh
        · simpa [targetBlock] using choice
        · exact sparseRest
      have currentShape :
          ListDerives
            (stem ++ renderGapBlocks (block :: rest))
            (nextStem ++ renderGapBlocks rest) := by
        simpa [renderGapBlocks, nextStem, List.append_assoc] using current
      have combined := currentShape.trans recurse
      have currentWeight :
          betaWeight markers (nextStem ++ renderGapBlocks rest) ≤
            betaWeight markers
              (stem ++ renderGapBlocks (block :: rest)) := by
        simpa [renderGapBlocks, nextStem, List.append_assoc] using
          currentWeightRaw
      have recurseWeight :
          betaWeight markers
              (stem ++ renderGapBlocks (targetBlock :: targetRest)) ≤
            betaWeight markers (nextStem ++ renderGapBlocks rest) := by
        simpa [renderGapBlocks, targetBlock, nextStem,
          List.append_assoc] using recurseWeightRaw
      refine ⟨targetBlock :: targetRest, sparseAll, ?_, ?_, ?_⟩
      · simpa [gapBlockMarkers, targetBlock] using
          congrArg (List.cons block.marker) markersRest
      · simpa [renderGapBlocks, targetBlock, nextStem,
          List.append_assoc] using combined
      · exact Nat.le_trans recurseWeight currentWeight

/-- Measured top-level A/B/C sparsification.  This is the interface needed
after every D repair in the terminating F10 alpha normalizer. -/
theorem listDerivesToSparseBlocksMeasured
    (markers letters : List Nat) :
    ∃ targetBlocks,
      SparseBlocks [] targetBlocks ∧
        gapBlockMarkers targetBlocks =
          firstOccurrenceSequenceList letters ∧
        ListDerives letters (renderGapBlocks targetBlocks) ∧
        betaWeight markers (renderGapBlocks targetBlocks) ≤
          betaWeight markers letters := by
  obtain ⟨targetBlocks, sparse, targetMarkers,
      derivation, weight⟩ :=
    listDerivesSparseBlocksMeasured markers
      (gapBlocksList_wellFormed letters) [] (by simp)
  refine ⟨targetBlocks, sparse, ?_, ?_, ?_⟩
  · calc
      gapBlockMarkers targetBlocks =
          gapBlockMarkers (gapBlocksList letters) := targetMarkers
      _ = firstOccurrenceSequenceList letters :=
        gapBlockMarkers_gapBlocksList letters
  · simpa [render_gapBlocksList] using derivation
  · simpa [render_gapBlocksList] using weight

end SemigroupBasis.CoRoots.Order6SporadicSection27.F10

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.listDerivesSparseSecondsMeasured
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.listDerivesSparseBlocksMeasured
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.listDerivesToSparseBlocksMeasured
