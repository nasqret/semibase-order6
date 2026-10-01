import SemigroupBasis.CoRoots.Order6SporadicSection27F10Derivations
import SemigroupBasis.CoRoots.Order6SporadicSection27F9G1Canonical

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27.F10

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_870

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

/-! ## A/B/C sparsification -/

/-- Collapse two already-seen later occurrences to one of them, according to
their witnessed order in `stem`.  Law B exposes the C orientation when the
displayed pair is reversed; law A handles the equal-letter case. -/
theorem listDerivesCollapsePairAfterSeen
    (stem suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ stem) (rightSeen : right ∈ stem) :
    ∃ retained,
      (retained = left ∨ retained = right) ∧
        ListDerives
          (stem ++ [left, right] ++ suffix)
          (stem ++ [retained] ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact ⟨left, Or.inl rfl,
      listDerivesContractAdjacentAfterSeen
        stem suffix left leftSeen⟩
  · obtain ⟨leftBefore, leftAfter, stemShape⟩ :=
      List.mem_iff_append.mp leftSeen
    have rightInSplit :
        right ∈ leftBefore ∨ right ∈ leftAfter := by
      rw [stemShape] at rightSeen
      rcases List.mem_append.mp rightSeen with beforeMember | afterMember
      · exact Or.inl beforeMember
      · rcases List.mem_cons.mp afterMember with atLeft | inAfter
        · exact False.elim (equal atLeft.symm)
        · exact Or.inr inAfter
    rcases rightInSplit with rightBefore | rightAfter
    · obtain ⟨before, middle, beforeShape⟩ :=
        List.mem_iff_append.mp rightBefore
      refine ⟨right, Or.inr rfl, ?_⟩
      simpa [stemShape, beforeShape, List.append_assoc] using
        listDerivesCDisplayed
          right left before middle leftAfter suffix
    · obtain ⟨middle, after, afterShape⟩ :=
        List.mem_iff_append.mp rightAfter
      have swapped :=
        listDerivesSwapAfterSeen
          stem suffix left right leftSeen rightSeen
      have collapsed :
          ListDerives
            (stem ++ [right, left] ++ suffix)
            (stem ++ [left] ++ suffix) := by
        simpa [stemShape, afterShape, List.append_assoc] using
          listDerivesCDisplayed
            left right leftBefore middle after suffix
      exact ⟨left, Or.inl rfl, swapped.trans collapsed⟩

/-- Every list of already-seen letters derives to an empty or singleton
choice from the same allowed marker prefix.  This existential form is enough
for completeness and avoids imposing an artificial numeric variable order. -/
theorem listDerivesSparseSeconds (allowed suffix : List Nat) :
    ∀ (source stem : List Nat),
      (∀ letter, letter ∈ allowed → letter ∈ stem) →
      (∀ letter, letter ∈ source → letter ∈ allowed) →
      ∃ reduced,
        ChoiceIn allowed reduced ∧
          ListDerives
            (stem ++ source ++ suffix)
            (stem ++ reduced ++ suffix)
  | [], stem, _, _ => by
      exact ⟨[], Or.inl rfl,
        S5_107.ListDerives.refl (basis := basis) _⟩
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
      obtain ⟨reduced, choice, recurse⟩ :=
        listDerivesSparseSeconds allowed suffix rest
          (stem ++ [letter]) allowedInExtended restAllowed
      rcases choice with empty | ⟨selected, selectedAllowed, shape⟩
      · subst reduced
        refine ⟨[letter], Or.inr ⟨letter, letterAllowed, rfl⟩, ?_⟩
        simpa [List.append_assoc] using recurse
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
        exact ⟨[retained],
          Or.inr ⟨retained, retainedAllowed, rfl⟩,
          recurseShape.trans collapse⟩

/-! ## Lifting sparsification through first-occurrence blocks -/

/-- Sparsify every gap block while preserving its first-occurrence marker.
The output remains explicitly indexed by the same reverse `seen` prefix. -/
theorem listDerivesSparseBlocks
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks)
    (stem : List Nat)
    (seenInStem : ∀ letter, letter ∈ seen → letter ∈ stem) :
    ∃ targetBlocks,
      SparseBlocks seen targetBlocks ∧
        gapBlockMarkers targetBlocks = gapBlockMarkers blocks ∧
          ListDerives
            (stem ++ renderGapBlocks blocks)
            (stem ++ renderGapBlocks targetBlocks) := by
  induction formed generalizing stem with
  | nil seen =>
      refine ⟨[], SparseBlocks.nil seen, rfl, ?_⟩
      simpa [renderGapBlocks] using
        S5_107.ListDerives.refl (basis := basis) stem
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
      obtain ⟨reduced, choice, current⟩ :=
        listDerivesSparseSeconds
          (block.marker :: seen) (renderGapBlocks rest)
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
      obtain ⟨targetRest, sparseRest, markersRest, recurse⟩ :=
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
      refine ⟨targetBlock :: targetRest, sparseAll, ?_, ?_⟩
      · simpa [gapBlockMarkers, targetBlock] using
          congrArg (List.cons block.marker) markersRest
      · simpa [renderGapBlocks, targetBlock, nextStem,
          List.append_assoc] using combined

/-- Every list of letters derives to a literal
condition-(I) form with exactly the same first-occurrence sequence. -/
theorem listDerivesToSparseBlocks (letters : List Nat) :
    ∃ targetBlocks,
      SparseBlocks [] targetBlocks ∧
        gapBlockMarkers targetBlocks = firstOccurrenceSequenceList letters ∧
          ListDerives letters (renderGapBlocks targetBlocks) := by
  obtain ⟨targetBlocks, sparse, markers, derivation⟩ :=
    listDerivesSparseBlocks
      (gapBlocksList_wellFormed letters) [] (by simp)
  refine ⟨targetBlocks, sparse, ?_, ?_⟩
  · calc
      gapBlockMarkers targetBlocks =
          gapBlockMarkers (gapBlocksList letters) := markers
      _ = firstOccurrenceSequenceList letters :=
        gapBlockMarkers_gapBlocksList letters
  · simpa [render_gapBlocksList] using derivation

end SemigroupBasis.CoRoots.Order6SporadicSection27.F10

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.listDerivesCollapsePairAfterSeen
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.listDerivesSparseSeconds
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.listDerivesSparseBlocks
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.listDerivesToSparseBlocks
