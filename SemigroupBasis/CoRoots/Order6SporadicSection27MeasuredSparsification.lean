import SemigroupBasis.CoRoots.Order6SporadicSection27BetaWitnesses
import SemigroupBasis.CoRoots.Order6SporadicSection27AlphaNormalization

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_870

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

/-! ## First-occurrence reconstruction and known replacements -/

/-- Scanning a list of already-known letters does not change the accumulated
first-occurrence sequence. -/
private theorem firstOccurrenceSequenceAux_append_known
    (seen suffix : List Nat) :
    ∀ (known : List Nat),
      (∀ letter, letter ∈ known → letter ∈ seen) →
        firstOccurrenceSequenceAux seen (known ++ suffix) =
          firstOccurrenceSequenceAux seen suffix
  | [], _ => rfl
  | head :: tail, allKnown => by
      have headKnown : head ∈ seen :=
        allKnown head (List.Mem.head tail)
      have tailKnown : ∀ letter, letter ∈ tail → letter ∈ seen := by
        intro letter member
        exact allKnown letter (List.Mem.tail head member)
      simp [firstOccurrenceSequenceAux, headKnown,
        firstOccurrenceSequenceAux_append_known seen suffix tail tailKnown]

/-- A well-formed gap-block rendering has exactly its block-marker list as its
first-occurrence sequence, even when the initial `seen` accumulator is
nonempty. -/
theorem firstOccurrenceSequenceAux_renderGapBlocks
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks) :
    firstOccurrenceSequenceAux seen (renderGapBlocks blocks) =
      gapBlockMarkers blocks := by
  induction formed with
  | nil =>
      simp [renderGapBlocks, gapBlockMarkers, firstOccurrenceSequenceAux]
  | cons seen block rest markerFresh secondsSeen tail induction =>
      change
        firstOccurrenceSequenceAux seen
            (block.marker :: (block.seconds ++ renderGapBlocks rest)) =
          block.marker :: gapBlockMarkers rest
      rw [firstOccurrenceSequenceAux]
      simp only [markerFresh, if_neg, gapBlockMarkers, List.map_cons]
      rw [firstOccurrenceSequenceAux_append_known
        (block.marker :: seen) (renderGapBlocks rest)
        block.seconds secondsSeen]
      exact congrArg (List.cons block.marker) induction

/-- Initial-state specialization of
`firstOccurrenceSequenceAux_renderGapBlocks`. -/
theorem firstOccurrenceSequenceList_renderGapBlocks
    {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed [] blocks) :
    firstOccurrenceSequenceList (renderGapBlocks blocks) =
      gapBlockMarkers blocks := by
  exact firstOccurrenceSequenceAux_renderGapBlocks formed

/-- Removing an occurrence that is already present in `seen` or in the
processed prefix does not alter the first-occurrence sequence. -/
private theorem firstOccurrenceSequenceAux_remove_known
    (removed : Nat) :
    ∀ (seen before after : List Nat),
      removed ∈ seen ∨ removed ∈ before →
        firstOccurrenceSequenceAux seen
            (before ++ removed :: after) =
          firstOccurrenceSequenceAux seen (before ++ after)
  | seen, [], after, known => by
      have member : removed ∈ seen := by
        simpa using known
      simp [firstOccurrenceSequenceAux, member]
  | seen, head :: rest, after, known => by
      by_cases headMember : head ∈ seen
      · have nextKnown : removed ∈ seen ∨ removed ∈ rest := by
          rcases known with seenMember | beforeMember
          · exact Or.inl seenMember
          · rcases List.mem_cons.mp beforeMember with equal | restMember
            · subst head
              exact Or.inl headMember
            · exact Or.inr restMember
        simpa [firstOccurrenceSequenceAux, headMember] using
          firstOccurrenceSequenceAux_remove_known
            removed seen rest after nextKnown
      · have nextKnown :
            removed ∈ head :: seen ∨ removed ∈ rest := by
          rcases known with seenMember | beforeMember
          · exact Or.inl (by simp [seenMember])
          · rcases List.mem_cons.mp beforeMember with equal | restMember
            · subst head
              exact Or.inl (by simp)
            · exact Or.inr restMember
        simpa [firstOccurrenceSequenceAux, headMember] using
          congrArg (List.cons head)
            (firstOccurrenceSequenceAux_remove_known
              removed (head :: seen) rest after nextKnown)

/-- Replacing one already-known occurrence by another already-known letter
preserves the full first-occurrence sequence. -/
theorem firstOccurrenceSequenceAux_replace_known
    (seen before after : List Nat) (removed inserted : Nat)
    (removedKnown : removed ∈ seen ∨ removed ∈ before)
    (insertedKnown : inserted ∈ seen ∨ inserted ∈ before) :
    firstOccurrenceSequenceAux seen (before ++ removed :: after) =
      firstOccurrenceSequenceAux seen (before ++ inserted :: after) := by
  calc
    firstOccurrenceSequenceAux seen (before ++ removed :: after) =
        firstOccurrenceSequenceAux seen (before ++ after) :=
      firstOccurrenceSequenceAux_remove_known
        removed seen before after removedKnown
    _ = firstOccurrenceSequenceAux seen (before ++ inserted :: after) :=
      (firstOccurrenceSequenceAux_remove_known
        inserted seen before after insertedKnown).symm

/-- Empty-initial-state form of known replacement. -/
theorem firstOccurrenceSequenceList_replace_known
    (before after : List Nat) (removed inserted : Nat)
    (removedKnown : removed ∈ before)
    (insertedKnown : inserted ∈ before) :
    firstOccurrenceSequenceList (before ++ removed :: after) =
      firstOccurrenceSequenceList (before ++ inserted :: after) := by
  simpa [firstOccurrenceSequenceList] using
    firstOccurrenceSequenceAux_replace_known
      [] before after removed inserted
      (Or.inr removedKnown) (Or.inr insertedKnown)

/-- A literal D repair changes only a later occurrence of an already-seen
letter, so it preserves the first-occurrence sequence. -/
theorem CrossingWitness.firstOccurrenceSequenceList_target
    {markers source : List Nat}
    (witness : CrossingWitness markers source) :
    firstOccurrenceSequenceList witness.target =
      firstOccurrenceSequenceList source := by
  let prefixList :=
    witness.pre ++ [witness.earlier] ++ witness.gapOne ++
      [witness.later] ++ witness.gapTwo ++ [witness.earlier] ++
        witness.gapThree
  have laterKnown : witness.later ∈ prefixList := by
    simp [prefixList]
  have earlierKnown : witness.earlier ∈ prefixList := by
    simp [prefixList]
  have replacement :=
    firstOccurrenceSequenceList_replace_known
      prefixList witness.post witness.later witness.earlier
      laterKnown earlierKnown
  generalize targetEq : witness.target = repaired
  rw [witness.source_eq]
  rw [← targetEq]
  simpa [CrossingWitness.target, prefixList, List.append_assoc] using
    replacement.symm

/-- A literal E repair likewise replaces only a later occurrence and preserves
the first-occurrence sequence. -/
theorem AdjacentWitness.firstOccurrenceSequenceList_target
    {markers source : List Nat}
    (witness : AdjacentWitness markers source) :
    firstOccurrenceSequenceList witness.target =
      firstOccurrenceSequenceList source := by
  let prefixList :=
    witness.pre ++ [witness.earlier] ++ witness.gapOne ++
      [witness.earlier, witness.later] ++ witness.gapTwo
  have laterKnown : witness.later ∈ prefixList := by
    simp [prefixList]
  have earlierKnown : witness.earlier ∈ prefixList := by
    simp [prefixList]
  have replacement :=
    firstOccurrenceSequenceList_replace_known
      prefixList witness.post witness.later witness.earlier
      laterKnown earlierKnown
  generalize targetEq : witness.target = repaired
  rw [witness.source_eq]
  rw [← targetEq]
  simpa [AdjacentWitness.target, prefixList, List.append_assoc] using
    replacement.symm

/-! ## Arithmetic support for measured sparsification -/

private theorem measuredListSum_append :
    ∀ left right : List Nat,
      (left ++ right).sum = left.sum + right.sum
  | [], right => by simp
  | head :: tail, right => by
      rw [List.cons_append, List.sum_cons,
        measuredListSum_append tail right, List.sum_cons]
      omega

@[simp]
theorem betaWeight_nil (markers : List Nat) :
    betaWeight markers [] = 0 := by
  simp [betaWeight]

@[simp]
theorem betaWeight_cons
    (markers : List Nat) (letter : Nat) (letters : List Nat) :
    betaWeight markers (letter :: letters) =
      markers.idxOf letter + betaWeight markers letters := by
  simp [betaWeight]

@[simp]
theorem betaWeight_append
    (markers left right : List Nat) :
    betaWeight markers (left ++ right) =
      betaWeight markers left + betaWeight markers right := by
  simp only [betaWeight, List.map_append, measuredListSum_append]

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
after every D/E repair in the terminating beta normalizer. -/
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

end SemigroupBasis.CoRoots.Order6SporadicSection27
