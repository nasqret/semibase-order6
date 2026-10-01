import SemigroupBasis.CoRoots.Order6SporadicSection15AlphaParsedBridge
import SemigroupBasis.CoRoots.Order6SporadicSection15BetaScaffoldMoves
import SemigroupBasis.CoRoots.Order6SporadicSection15BetaSelectedHigh
import SemigroupBasis.CoRoots.Order6SporadicSection15BetaSeparatedMarkers

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

namespace BetaScaffoldMoves

/-! ## Source decomposition for the beta scaffold

The terminated parser fixes the globally simple gaps and exposes every other
letter as a marker slot.  The first theorem below strengthens the alpha
marker-gap permutation API: the separated-marker move permits arbitrary
middle lists, so marker-freeness of the gaps is not needed.

The terminal theorem below completes the source-to-scaffold route.  It uses a
high-count marker to pass through a common expansion: internal empty gaps are
first moved to the front, both marker inventories are expanded to the same
high-marker multiset, and the markers are then permuted against the common
gap schedule.
-/

/-- Any permutation of globally nonsimple marker slots is derivable while the
positional gaps remain fixed.  Unlike the alpha occurrence-pairing theorem,
this uses `listDerivesSwapSeparatedNonsimple` and therefore imposes no
marker-freeness condition on the gaps. -/
theorem listDerivesPermuteNonsimpleMarkerGaps
    (before after : List Nat) (gaps : List (List Nat))
    {source target : List Nat}
    (balanced : gaps.length = source.length)
    (nonsimple :
      forall marker, marker ∈ source ->
        2 <=
          (before ++
            AlphaOccurrencePairing.renderMarkerGaps source gaps ++
            after).count marker)
    (permutation : source.Perm target) :
    ListDerives
      (before ++
        AlphaOccurrencePairing.renderMarkerGaps source gaps ++ after)
      (before ++
        AlphaOccurrencePairing.renderMarkerGaps target gaps ++ after) := by
  induction permutation generalizing before gaps with
  | nil =>
      have gapsEmpty : gaps = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using balanced
      subst gaps
      exact S5_107.ListDerives.refl _
  | @cons head source target permutation induction =>
      cases gaps with
      | nil =>
          simp at balanced
      | cons gap gaps =>
          have tailBalanced : gaps.length = source.length := by
            simpa using balanced
          have tailNonsimple :
              forall marker, marker ∈ source ->
                2 <=
                  ((before ++ [head] ++ gap) ++
                    AlphaOccurrencePairing.renderMarkerGaps source gaps ++
                    after).count marker := by
            intro marker markerIn
            have bound :=
              nonsimple marker (List.Mem.tail head markerIn)
            simpa [AlphaOccurrencePairing.renderMarkerGaps,
              List.append_assoc] using bound
          have tailDerivation :=
            induction (before ++ [head] ++ gap) gaps
              tailBalanced tailNonsimple
          simpa [AlphaOccurrencePairing.renderMarkerGaps,
            List.append_assoc] using tailDerivation
  | swap first second rest =>
      cases gaps with
      | nil =>
          simp at balanced
      | cons firstGap remaining =>
          cases remaining with
          | nil =>
              simp at balanced
          | cons secondGap gaps =>
              have secondBound := nonsimple second (by simp)
              have firstBound := nonsimple first (by simp)
              simpa [AlphaOccurrencePairing.renderMarkerGaps,
                List.append_assoc] using
                listDerivesSwapSeparatedNonsimple
                  before firstGap
                  (secondGap ++
                    AlphaOccurrencePairing.renderMarkerGaps rest gaps ++
                    after)
                  second first
                  (by
                    simpa [AlphaOccurrencePairing.renderMarkerGaps,
                      List.append_assoc] using secondBound)
                  (by
                    simpa [AlphaOccurrencePairing.renderMarkerGaps,
                      List.append_assoc] using firstBound)
  | @trans source middle target firstPermutation secondPermutation
      firstInduction secondInduction =>
      have firstDerivation :=
        firstInduction before gaps balanced nonsimple
      have middleBalanced : gaps.length = middle.length :=
        balanced.trans firstPermutation.length_eq
      have middleNonsimple :
          forall marker, marker ∈ middle ->
            2 <=
              (before ++
                AlphaOccurrencePairing.renderMarkerGaps middle gaps ++
                after).count marker := by
        intro marker markerIn
        have sourceIn : marker ∈ source :=
          (firstPermutation.mem_iff).mpr markerIn
        have bound := nonsimple marker sourceIn
        have renderedCount :=
          AlphaOccurrencePairing.renderMarkerGaps_count_eq_of_perm
            gaps balanced firstPermutation marker
        simp only [List.count_append] at bound |-
        omega
      exact firstDerivation.trans
        (secondInduction before gaps middleBalanced middleNonsimple)

/-- The beta branch contains a high-count marker, so its terminated factor
decomposition is nonempty. -/
theorem factors_ne_nil_of_branch_beta
    {letters : List Nat}
    (branch : CanonicalData.canonicalBranch letters = .beta) :
    ParsedWords.factors letters ≠ [] := by
  obtain ⟨marker, markerHigh⟩ :=
    CanonicalData.exists_count_ge_three_of_branch_beta branch
  have markerMember : marker ∈ AlphaParsedBridge.markerLabels letters := by
    simpa [AlphaParsedBridge.markerLabels, ParsedWords.factors] using
      (S5_107.mem_terminatedFactorMarkers_iff marker letters).2 (by omega)
  intro factorsEmpty
  simp [AlphaParsedBridge.markerLabels, factorsEmpty,
    S5_107.terminatedFactorMarkers] at markerMember

/-- On the beta branch, the parser's literal prefix is the established initial
globally simple block. -/
theorem initialBlock_eq_initialSimpleBlock_of_branch_beta
    {letters : List Nat}
    (branch : CanonicalData.canonicalBranch letters = .beta) :
    AlphaParsedBridge.initialBlock letters =
      S5_107.initialSimpleBlock letters := by
  obtain ⟨first, rest, shape⟩ :=
    List.exists_cons_of_ne_nil (factors_ne_nil_of_branch_beta branch)
  exact
    AlphaParsedBridge.initialBlock_eq_initialSimpleBlock_of_factors_cons
      letters first rest shape

/-- A beta word is literally its initial simple block followed by the parser's
balanced marker-gap rendering. -/
theorem reconstruct_with_initialSimpleBlock_of_branch_beta
    (letters : List Nat)
    (branch : CanonicalData.canonicalBranch letters = .beta) :
    S5_107.initialSimpleBlock letters ++
        AlphaOccurrencePairing.renderMarkerGaps
          (AlphaParsedBridge.markerLabels letters)
          (AlphaParsedBridge.postMarkerGaps letters) =
      letters := by
  rw [← initialBlock_eq_initialSimpleBlock_of_branch_beta branch]
  exact AlphaParsedBridge.reconstruct letters

/-- Every projected parser marker is globally nonsimple in the source word. -/
theorem parsedMarker_nonsimple
    (letters : List Nat) (marker : Nat)
    (member : marker ∈ AlphaParsedBridge.markerLabels letters) :
    2 <= letters.count marker := by
  apply (S5_107.mem_terminatedFactorMarkers_iff marker letters).1
  simpa [AlphaParsedBridge.markerLabels, ParsedWords.factors] using member

/-- Every label used in the scaffold's cube block occurs among the parsed
source markers. -/
theorem highLabel_mem_parsedMarkers
    (letters : List Nat) (marker : Nat)
    (member : marker ∈ BetaScaffoldData.highLabels letters) :
    marker ∈ AlphaParsedBridge.markerLabels letters := by
  have markerHigh : 3 <= letters.count marker :=
    (CanonicalData.sortedHighCountLetters_mem_iff marker letters).1 (by
      simpa [BetaScaffoldData.highLabels] using member)
  simpa [AlphaParsedBridge.markerLabels, ParsedWords.factors] using
    (S5_107.mem_terminatedFactorMarkers_iff marker letters).2 (by omega)

/-- Every label used in the scaffold's square prefix occurs among the parsed
source markers. -/
theorem doubledLabel_mem_parsedMarkers
    (letters : List Nat) (marker : Nat)
    (member : marker ∈ BetaScaffoldData.doubledLabels letters) :
    marker ∈ AlphaParsedBridge.markerLabels letters := by
  have markerDoubled : letters.count marker = 2 :=
    (CanonicalData.sortedDoubledLetters_mem_iff marker letters).1 (by
      simpa [BetaScaffoldData.doubledLabels] using member)
  simpa [AlphaParsedBridge.markerLabels, ParsedWords.factors] using
    (S5_107.mem_terminatedFactorMarkers_iff marker letters).2 (by omega)

/-- The parsed marker labels of a beta word may be permuted arbitrarily while
every parsed simple gap remains in its source position. -/
theorem listDerivesPermuteParsedMarkers_of_branch_beta
    (letters : List Nat)
    (branch : CanonicalData.canonicalBranch letters = .beta)
    {target : List Nat}
    (permutation :
      (AlphaParsedBridge.markerLabels letters).Perm target) :
    ListDerives letters
      (S5_107.initialSimpleBlock letters ++
        AlphaOccurrencePairing.renderMarkerGaps target
          (AlphaParsedBridge.postMarkerGaps letters)) := by
  have sourceNonsimple :
      forall marker, marker ∈ AlphaParsedBridge.markerLabels letters ->
        2 <=
          (S5_107.initialSimpleBlock letters ++
            AlphaOccurrencePairing.renderMarkerGaps
              (AlphaParsedBridge.markerLabels letters)
              (AlphaParsedBridge.postMarkerGaps letters) ++
            []).count marker := by
    intro marker markerIn
    simpa [reconstruct_with_initialSimpleBlock_of_branch_beta
      letters branch] using parsedMarker_nonsimple letters marker markerIn
  have permuted := listDerivesPermuteNonsimpleMarkerGaps
    (S5_107.initialSimpleBlock letters) []
    (AlphaParsedBridge.postMarkerGaps letters)
    (AlphaParsedBridge.postMarkerGaps_length_eq_markerLabels_length letters)
    sourceNonsimple permutation
  rw [reconstruct_with_initialSimpleBlock_of_branch_beta
    letters branch] at permuted
  simpa only [List.append_nil] using permuted

/-! ### Empty-slot changes supplied by one selected high marker -/

/-- Duplicate the head marker slot and place an empty positional gap after the
new copy.  The surrounding `before` context lets callers expose any selected
slot first by `listDerivesPermuteNonsimpleMarkerGaps`. -/
theorem listDerivesDuplicateHighMarkerGapHead
    (before after gap : List Nat) (marker : Nat)
    (markers : List Nat) (gaps : List (List Nat))
    (high :
      3 <=
        (before ++
          AlphaOccurrencePairing.renderMarkerGaps
            (marker :: markers) (gap :: gaps) ++
          after).count marker) :
    ListDerives
      (before ++
        AlphaOccurrencePairing.renderMarkerGaps
          (marker :: markers) (gap :: gaps) ++ after)
      (before ++
        AlphaOccurrencePairing.renderMarkerGaps
          (marker :: marker :: markers) ([] :: gap :: gaps) ++ after) := by
  have selected := listDerivesDuplicateSelectedHigh
    marker before
    (gap ++
      AlphaOccurrencePairing.renderMarkerGaps markers gaps ++ after)
    (by
      simpa [AlphaOccurrencePairing.renderMarkerGaps,
        List.append_assoc] using high)
  simpa [AlphaOccurrencePairing.renderMarkerGaps,
    List.append_assoc] using selected

/-- Remove one empty slot between two equal displayed high markers.  The high
hypothesis is measured in the contracted rendering, exactly as required by
`listDerivesContractSelectedHigh`. -/
theorem listDerivesContractHighMarkerGapHead
    (before after gap : List Nat) (marker : Nat)
    (markers : List Nat) (gaps : List (List Nat))
    (high :
      3 <=
        (before ++
          AlphaOccurrencePairing.renderMarkerGaps
            (marker :: markers) (gap :: gaps) ++
          after).count marker) :
    ListDerives
      (before ++
        AlphaOccurrencePairing.renderMarkerGaps
          (marker :: marker :: markers) ([] :: gap :: gaps) ++ after)
      (before ++
        AlphaOccurrencePairing.renderMarkerGaps
          (marker :: markers) (gap :: gaps) ++ after) := by
  have selected := listDerivesContractSelectedHigh
    marker before
    (gap ++
      AlphaOccurrencePairing.renderMarkerGaps markers gaps ++ after)
    (by
      simpa [AlphaOccurrencePairing.renderMarkerGaps,
        List.append_assoc] using high)
  simpa [AlphaOccurrencePairing.renderMarkerGaps,
    List.append_assoc] using selected

/-- Insert any requested number of empty slots immediately before one selected
high-marker slot.  The selected occurrence remains available to the recursive
call, while the retained copy is moved into the processed prefix. -/
theorem listDerivesExpandHighMarkerGapHead
    (before after gap : List Nat) (marker : Nat)
    (markers : List Nat) (gaps : List (List Nat))
    (high :
      3 <=
        (before ++
          AlphaOccurrencePairing.renderMarkerGaps
            (marker :: markers) (gap :: gaps) ++
          after).count marker) :
    forall extra : Nat,
      ListDerives
        (before ++
          AlphaOccurrencePairing.renderMarkerGaps
            (marker :: markers) (gap :: gaps) ++ after)
        (before ++
          AlphaOccurrencePairing.renderMarkerGaps
            (List.replicate (extra + 1) marker ++ markers)
            (List.replicate extra [] ++ gap :: gaps) ++ after)
  | 0 => by
      simpa [AlphaOccurrencePairing.renderMarkerGaps] using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++
            AlphaOccurrencePairing.renderMarkerGaps
              (marker :: markers) (gap :: gaps) ++ after))
  | extra + 1 => by
      have first := listDerivesDuplicateHighMarkerGapHead
        before after gap marker markers gaps high
      have nextHigh :
          3 <=
            ((before ++ [marker]) ++
              AlphaOccurrencePairing.renderMarkerGaps
                (marker :: markers) (gap :: gaps) ++
              after).count marker := by
        simp [AlphaOccurrencePairing.renderMarkerGaps,
          List.count_append] at high |-
        omega
      have rest := listDerivesExpandHighMarkerGapHead
        (before ++ [marker]) after gap marker markers gaps
        nextHigh extra
      have rest' :
          ListDerives
            (before ++
              AlphaOccurrencePairing.renderMarkerGaps
                (marker :: marker :: markers) ([] :: gap :: gaps) ++ after)
            ((before ++ [marker]) ++
              AlphaOccurrencePairing.renderMarkerGaps
                (List.replicate (extra + 1) marker ++ markers)
                (List.replicate extra [] ++ gap :: gaps) ++ after) := by
        simpa [AlphaOccurrencePairing.renderMarkerGaps,
          List.append_assoc] using rest
      simpa [List.replicate_succ,
        AlphaOccurrencePairing.renderMarkerGaps,
        List.append_assoc] using first.trans rest'
termination_by extra => extra

/-- Remove any finite block of empty slots inserted before one selected high
marker.  This is the exact symmetry of
`listDerivesExpandHighMarkerGapHead`. -/
theorem listDerivesContractHighMarkerGapHeadN
    (before after gap : List Nat) (marker : Nat)
    (markers : List Nat) (gaps : List (List Nat))
    (high :
      3 <=
        (before ++
          AlphaOccurrencePairing.renderMarkerGaps
            (marker :: markers) (gap :: gaps) ++
          after).count marker)
    (extra : Nat) :
    ListDerives
      (before ++
        AlphaOccurrencePairing.renderMarkerGaps
          (List.replicate (extra + 1) marker ++ markers)
          (List.replicate extra [] ++ gap :: gaps) ++ after)
      (before ++
        AlphaOccurrencePairing.renderMarkerGaps
          (marker :: markers) (gap :: gaps) ++ after) :=
  (listDerivesExpandHighMarkerGapHead
    before after gap marker markers gaps high extra).symm

/-! ### Common high-marker expansion -/

private theorem renderMarkerGaps_append
    (leftMarkers rightMarkers : List Nat)
    (leftGaps rightGaps : List (List Nat))
    (balanced : leftGaps.length = leftMarkers.length) :
    AlphaOccurrencePairing.renderMarkerGaps
        (leftMarkers ++ rightMarkers) (leftGaps ++ rightGaps) =
      AlphaOccurrencePairing.renderMarkerGaps leftMarkers leftGaps ++
        AlphaOccurrencePairing.renderMarkerGaps rightMarkers rightGaps := by
  induction leftMarkers generalizing leftGaps with
  | nil =>
      have leftGapsEmpty : leftGaps = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using balanced
      subst leftGaps
      rfl
  | cons marker markers induction =>
      cases leftGaps with
      | nil => simp at balanced
      | cons gap gaps =>
          have tailBalanced : gaps.length = markers.length := by
            simpa using balanced
          simp [AlphaOccurrencePairing.renderMarkerGaps,
            induction gaps tailBalanced, List.append_assoc]

private theorem count_nil_add_filter_ne_nil_length
    (gaps : List (List Nat)) :
    gaps.count [] + (gaps.filter (fun gap => gap != [])).length =
      gaps.length := by
  induction gaps with
  | nil => simp
  | cons gap gaps induction =>
      by_cases empty : gap = []
      · subst gap
        simp
        omega
      · simp [empty]
        omega

private theorem replicate_nil_add (left right : Nat) :
    List.replicate (left + right) ([] : List Nat) =
      List.replicate left [] ++ List.replicate right [] := by
  induction left with
  | zero => simp
  | succ left induction =>
      have arithmetic : left + 1 + right = (left + right) + 1 := by
        omega
      simp only [arithmetic, List.replicate_succ, List.cons_append]
      exact congrArg (List.cons ([] : List Nat)) induction

private def highMarkerPart (markers : List Nat) : List Nat :=
  markers.filter fun marker => decide (3 <= markers.count marker)

private theorem count_highMarkerPart
    (markers : List Nat) (tested : Nat) :
    (highMarkerPart markers).count tested =
      if 3 <= markers.count tested then markers.count tested else 0 := by
  by_cases high : 3 <= markers.count tested
  · rw [if_pos high]
    unfold highMarkerPart
    exact List.count_filter (p :=
      fun marker => decide (3 <= markers.count marker)) (by simp [high])
  · rw [if_neg high, List.count_eq_zero]
    intro member
    simp [highMarkerPart, high] at member

private theorem listDerivesPermuteMarkerGaps_of_counts
    (before after : List Nat) (gaps : List (List Nat))
    {source target : List Nat}
    (balanced : gaps.length = source.length)
    (multiple :
      forall marker, marker ∈ source -> 2 <= source.count marker)
    (permutation : source.Perm target) :
    ListDerives
      (before ++
        AlphaOccurrencePairing.renderMarkerGaps source gaps ++ after)
      (before ++
        AlphaOccurrencePairing.renderMarkerGaps target gaps ++ after) := by
  apply listDerivesPermuteNonsimpleMarkerGaps
    before after gaps balanced
  · intro marker markerIn
    have markerBound := multiple marker markerIn
    have renderBound :=
      AlphaOccurrencePairing.marker_count_le_renderMarkerGaps
        source gaps balanced marker
    simp only [List.count_append]
    omega
  · exact permutation

/-- Insert one empty positional gap before an arbitrary selected gap.  Marker
labels are freely permuted to expose the selected high marker, duplicated by
(15.1a), and then restored to the explicit inventory `marker :: markers`. -/
private theorem listDerivesInsertEmptyHighSlotAt
    (before after : List Nat) (marker : Nat)
    (markers : List Nat)
    (prefixGaps : List (List Nat)) (gap : List Nat)
    (suffixGaps : List (List Nat))
    (balanced :
      (prefixGaps ++ gap :: suffixGaps).length = markers.length)
    (multiple :
      forall tested, tested ∈ markers -> 2 <= markers.count tested)
    (markerMember : marker ∈ markers)
    (high : 3 <= markers.count marker) :
    ListDerives
      (before ++
        AlphaOccurrencePairing.renderMarkerGaps markers
          (prefixGaps ++ gap :: suffixGaps) ++ after)
      (before ++
        AlphaOccurrencePairing.renderMarkerGaps (marker :: markers)
          (prefixGaps ++ [] :: gap :: suffixGaps) ++ after) := by
  let remaining := markers.erase marker
  let leftMarkers := remaining.take prefixGaps.length
  let rightMarkers := remaining.drop prefixGaps.length
  have remainingSplit : leftMarkers ++ rightMarkers = remaining := by
    exact List.take_append_drop prefixGaps.length remaining
  have expose : markers.Perm (marker :: remaining) :=
    List.perm_cons_erase markerMember
  have shifted :
      (marker :: remaining).Perm
        (leftMarkers ++ marker :: rightMarkers) := by
    rw [List.perm_iff_count]
    intro tested
    rw [← remainingSplit]
    simp only [List.count_cons, List.count_append]
    omega
  have arranged :
      markers.Perm (leftMarkers ++ marker :: rightMarkers) :=
    expose.trans shifted
  have remainingLength : remaining.length + 1 = markers.length := by
    have erased := List.length_erase_of_mem markerMember
    have positive := List.length_pos_of_mem markerMember
    simp only [remaining] at erased ⊢
    omega
  have prefixLe : prefixGaps.length <= remaining.length := by
    simp only [List.length_append, List.length_cons] at balanced
    omega
  have leftBalanced : prefixGaps.length = leftMarkers.length := by
    simp [leftMarkers, List.length_take, Nat.min_eq_left prefixLe]
  have rightBalanced : suffixGaps.length = rightMarkers.length := by
    simp [rightMarkers, List.length_drop]
    simp only [List.length_append, List.length_cons] at balanced
    omega
  have arrangedBalanced :
      (prefixGaps ++ gap :: suffixGaps).length =
        (leftMarkers ++ marker :: rightMarkers).length :=
    balanced.trans arranged.length_eq
  have permuted := listDerivesPermuteMarkerGaps_of_counts
    before after (prefixGaps ++ gap :: suffixGaps)
    balanced multiple arranged
  have arrangedHigh :
      3 <= (leftMarkers ++ marker :: rightMarkers).count marker := by
    rw [← List.perm_iff_count.mp arranged marker]
    exact high
  have renderedHigh :
      3 <=
        (before ++
          AlphaOccurrencePairing.renderMarkerGaps
            (leftMarkers ++ marker :: rightMarkers)
            (prefixGaps ++ gap :: suffixGaps) ++ after).count marker := by
    have renderBound :=
      AlphaOccurrencePairing.marker_count_le_renderMarkerGaps
        (leftMarkers ++ marker :: rightMarkers)
        (prefixGaps ++ gap :: suffixGaps)
        arrangedBalanced marker
    simp only [List.count_append]
    omega
  have duplicated := listDerivesDuplicateSelectedHigh marker
    (before ++
      AlphaOccurrencePairing.renderMarkerGaps leftMarkers prefixGaps)
    (gap ++
      AlphaOccurrencePairing.renderMarkerGaps rightMarkers suffixGaps ++
      after)
    (by
      rw [renderMarkerGaps_append leftMarkers (marker :: rightMarkers)
        prefixGaps (gap :: suffixGaps) leftBalanced] at renderedHigh
      simpa [AlphaOccurrencePairing.renderMarkerGaps,
        List.append_assoc] using renderedHigh)
  have inserted :
      ListDerives
        (before ++
          AlphaOccurrencePairing.renderMarkerGaps
            (leftMarkers ++ marker :: rightMarkers)
            (prefixGaps ++ gap :: suffixGaps) ++ after)
        (before ++
          AlphaOccurrencePairing.renderMarkerGaps
            (leftMarkers ++ marker :: marker :: rightMarkers)
            (prefixGaps ++ [] :: gap :: suffixGaps) ++ after) := by
    simpa [renderMarkerGaps_append, leftBalanced,
      AlphaOccurrencePairing.renderMarkerGaps,
      List.append_assoc] using duplicated
  have expandedPermutation :
      (leftMarkers ++ marker :: marker :: rightMarkers).Perm
        (marker :: markers) := by
    rw [List.perm_iff_count]
    intro tested
    have arrangedCount := List.perm_iff_count.mp arranged tested
    simp only [List.count_append, List.count_cons] at arrangedCount ⊢
    omega
  have expandedBalanced :
      (prefixGaps ++ [] :: gap :: suffixGaps).length =
        (leftMarkers ++ marker :: marker :: rightMarkers).length := by
    simp only [List.length_append, List.length_cons]
    simp only [List.length_append, List.length_cons] at arrangedBalanced
    omega
  have targetMultiple :
      forall tested, tested ∈ marker :: markers ->
        2 <= (marker :: markers).count tested := by
    intro tested testedIn
    rcases List.mem_cons.mp testedIn with equal | testedIn
    · subst tested
      simp only [List.count_cons_self]
      omega
    · have testedBound := multiple tested testedIn
      simp only [List.count_cons]
      omega
  have expandedMultiple :
      forall tested,
        tested ∈ leftMarkers ++ marker :: marker :: rightMarkers ->
          2 <=
            (leftMarkers ++ marker :: marker :: rightMarkers).count tested := by
    intro tested testedIn
    have targetIn : tested ∈ marker :: markers :=
      expandedPermutation.mem_iff.mp testedIn
    have targetBound := targetMultiple tested targetIn
    rw [List.perm_iff_count.mp expandedPermutation tested]
    exact targetBound
  have restored := listDerivesPermuteMarkerGaps_of_counts
    before after (prefixGaps ++ [] :: gap :: suffixGaps)
    expandedBalanced expandedMultiple expandedPermutation
  exact permuted.trans (inserted.trans restored)

/-- Prepend any finite list of high-marker slots, with an empty gap after each
new occurrence. -/
private theorem listDerivesPrependHighSlots
    (before after : List Nat) (markers : List Nat)
    (gaps : List (List Nat))
    (balanced : gaps.length = markers.length)
    (multiple :
      forall marker, marker ∈ markers -> 2 <= markers.count marker) :
    forall additions : List Nat,
      (forall marker, marker ∈ additions -> 3 <= markers.count marker) ->
      ListDerives
        (before ++
          AlphaOccurrencePairing.renderMarkerGaps markers gaps ++ after)
        (before ++
          AlphaOccurrencePairing.renderMarkerGaps (additions ++ markers)
            (List.replicate additions.length [] ++ gaps) ++ after) := by
  intro additions additionsHigh
  induction additions with
  | nil =>
      simpa using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++
            AlphaOccurrencePairing.renderMarkerGaps markers gaps ++ after))
  | cons marker additions induction =>
      have tailHigh :
          forall tested, tested ∈ additions ->
            3 <= markers.count tested := by
        intro tested testedIn
        exact additionsHigh tested (List.Mem.tail marker testedIn)
      have tailStep := induction tailHigh
      let currentMarkers := additions ++ markers
      let currentGaps := List.replicate additions.length [] ++ gaps
      have currentBalanced :
          currentGaps.length = currentMarkers.length := by
        simp [currentGaps, currentMarkers, balanced]
      have currentMultiple :
          forall tested, tested ∈ currentMarkers ->
            2 <= currentMarkers.count tested := by
        intro tested testedIn
        rcases List.mem_append.mp testedIn with added | original
        · have testedHigh := tailHigh tested added
          simp only [currentMarkers, List.count_append]
          omega
        · have testedBound := multiple tested original
          simp only [currentMarkers, List.count_append]
          omega
      have markerHigh : 3 <= currentMarkers.count marker := by
        have originalHigh := additionsHigh marker (by simp)
        simp only [currentMarkers, List.count_append]
        omega
      have markerMember : marker ∈ currentMarkers :=
        List.count_pos_iff.mp (by omega)
      have currentGapsNonempty : currentGaps ≠ [] := by
        intro empty
        have currentMarkersEmpty : currentMarkers = [] := by
          apply List.eq_nil_of_length_eq_zero
          rw [← currentBalanced, empty]
          rfl
        rw [currentMarkersEmpty] at markerHigh
        simp at markerHigh
      obtain ⟨firstGap, suffixGaps, currentGapsShape⟩ :=
        List.exists_cons_of_ne_nil currentGapsNonempty
      have headStep := listDerivesInsertEmptyHighSlotAt
        before after marker currentMarkers [] firstGap suffixGaps
        (by simpa [currentGapsShape] using currentBalanced)
        currentMultiple markerMember markerHigh
      rw [← currentGapsShape] at headStep
      simpa [currentMarkers, currentGaps, List.replicate_succ,
        List.append_assoc] using tailStep.trans headStep

/-- Exchange one gap with a following internal empty gap.  Both directions
expand to the same one-slot common refinement, so no high occurrence is lost. -/
private theorem listDerivesSwapGapWithFollowingEmpty
    (before after : List Nat) (marker : Nat)
    (markers : List Nat)
    (prefixGaps : List (List Nat)) (gap nextGap : List Nat)
    (suffixGaps : List (List Nat))
    (balanced :
      (prefixGaps ++ gap :: [] :: nextGap :: suffixGaps).length =
        markers.length)
    (multiple :
      forall tested, tested ∈ markers -> 2 <= markers.count tested)
    (markerMember : marker ∈ markers)
    (high : 3 <= markers.count marker) :
    ListDerives
      (before ++
        AlphaOccurrencePairing.renderMarkerGaps markers
          (prefixGaps ++ gap :: [] :: nextGap :: suffixGaps) ++ after)
      (before ++
        AlphaOccurrencePairing.renderMarkerGaps markers
          (prefixGaps ++ [] :: gap :: nextGap :: suffixGaps) ++ after) := by
  have sourceExpansion := listDerivesInsertEmptyHighSlotAt
    before after marker markers prefixGaps gap
      ([] :: nextGap :: suffixGaps) balanced multiple markerMember high
  have targetBalanced :
      (prefixGaps ++ [] :: gap :: nextGap :: suffixGaps).length =
        markers.length := by
    simp only [List.length_append, List.length_cons]
    simp only [List.length_append, List.length_cons] at balanced
    omega
  have targetExpansion := listDerivesInsertEmptyHighSlotAt
    before after marker markers (prefixGaps ++ [[], gap]) nextGap
      suffixGaps (by simpa [List.append_assoc] using targetBalanced)
      multiple markerMember high
  have targetContraction :
      ListDerives
        (before ++
          AlphaOccurrencePairing.renderMarkerGaps (marker :: markers)
            (prefixGaps ++ [] :: gap :: [] :: nextGap :: suffixGaps) ++ after)
        (before ++
          AlphaOccurrencePairing.renderMarkerGaps markers
            (prefixGaps ++ [] :: gap :: nextGap :: suffixGaps) ++ after) := by
    simpa [List.append_assoc] using targetExpansion.symm
  exact sourceExpansion.trans targetContraction

private theorem listDerivesMoveGapAcrossEmptySlots
    (before after : List Nat) (marker : Nat)
    (markers : List Nat)
    (prefixGaps : List (List Nat)) (gap : List Nat)
    (suffixGaps : List (List Nat))
    (suffixNonempty : suffixGaps ≠ [])
    (multiple :
      forall tested, tested ∈ markers -> 2 <= markers.count tested)
    (markerMember : marker ∈ markers)
    (high : 3 <= markers.count marker) :
    forall emptyCount : Nat,
      (prefixGaps ++ gap :: List.replicate emptyCount [] ++ suffixGaps).length =
        markers.length ->
      ListDerives
        (before ++
          AlphaOccurrencePairing.renderMarkerGaps markers
            (prefixGaps ++ gap :: List.replicate emptyCount [] ++
              suffixGaps) ++ after)
        (before ++
          AlphaOccurrencePairing.renderMarkerGaps markers
            (prefixGaps ++ List.replicate emptyCount [] ++ gap ::
              suffixGaps) ++ after) := by
  intro emptyCount
  induction emptyCount generalizing prefixGaps with
  | zero =>
      intro balanced
      simpa using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++
            AlphaOccurrencePairing.renderMarkerGaps markers
              (prefixGaps ++ gap :: suffixGaps) ++ after))
  | succ emptyCount induction =>
      intro balanced
      have remainingNonempty :
          List.replicate emptyCount [] ++ suffixGaps ≠ [] := by
        exact List.append_ne_nil_of_right_ne_nil _ suffixNonempty
      obtain ⟨nextGap, remainingGaps, remainingShape⟩ :=
        List.exists_cons_of_ne_nil remainingNonempty
      have firstStep := listDerivesSwapGapWithFollowingEmpty
        before after marker markers prefixGaps gap nextGap remainingGaps
        (by
          simpa [List.replicate_succ, remainingShape,
            List.append_assoc] using balanced)
        multiple markerMember high
      have recursiveBalanced :
          ((prefixGaps ++ [[]]) ++ gap ::
              List.replicate emptyCount [] ++ suffixGaps).length =
            markers.length := by
        simpa [List.replicate_succ, List.append_assoc] using balanced
      have recursiveStep := induction (prefixGaps ++ [[]]) recursiveBalanced
      have recursiveStep' :
          ListDerives
            (before ++
              AlphaOccurrencePairing.renderMarkerGaps markers
                (prefixGaps ++ [] :: gap :: nextGap :: remainingGaps) ++ after)
            (before ++
              AlphaOccurrencePairing.renderMarkerGaps markers
                (prefixGaps ++ [] :: List.replicate emptyCount [] ++
                  gap :: suffixGaps) ++ after) := by
        simpa [remainingShape, List.append_assoc] using recursiveStep
      simpa [List.replicate_succ, remainingShape,
        List.append_assoc] using firstStep.trans recursiveStep'

/-- Stable-partition the internal gaps, moving every empty one to the front
while retaining the final gap literally. -/
private theorem listDerivesMoveInternalEmptiesFront
    (before after : List Nat) (marker : Nat)
    (markers : List Nat)
    (prefixGaps internalGaps : List (List Nat)) (finalGap : List Nat)
    (balanced :
      (prefixGaps ++ internalGaps ++ [finalGap]).length = markers.length)
    (multiple :
      forall tested, tested ∈ markers -> 2 <= markers.count tested)
    (markerMember : marker ∈ markers)
    (high : 3 <= markers.count marker) :
    ListDerives
      (before ++
        AlphaOccurrencePairing.renderMarkerGaps markers
          (prefixGaps ++ internalGaps ++ [finalGap]) ++ after)
      (before ++
        AlphaOccurrencePairing.renderMarkerGaps markers
          (prefixGaps ++ List.replicate (internalGaps.count []) [] ++
            internalGaps.filter (fun gap => gap != []) ++ [finalGap]) ++
        after) := by
  induction internalGaps generalizing prefixGaps with
  | nil =>
      simpa using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++
            AlphaOccurrencePairing.renderMarkerGaps markers
              (prefixGaps ++ [finalGap]) ++ after))
  | cons gap internalGaps induction =>
      have tailBalanced :
          ((prefixGaps ++ [gap]) ++ internalGaps ++ [finalGap]).length =
            markers.length := by
        simpa [List.append_assoc] using balanced
      have tailStep := induction (prefixGaps ++ [gap]) tailBalanced
      by_cases empty : gap = []
      · subst gap
        simpa [List.append_assoc] using tailStep
      · have partitionLength :=
          count_nil_add_filter_ne_nil_length internalGaps
        have moveBalanced :
            (prefixGaps ++ gap ::
                List.replicate (internalGaps.count []) [] ++
                  internalGaps.filter (fun candidate => candidate != []) ++
                    [finalGap]).length = markers.length := by
          simp only [List.length_append, List.length_cons,
            List.length_replicate]
          simp only [List.length_append, List.length_cons] at balanced
          omega
        have moveStep := listDerivesMoveGapAcrossEmptySlots
          before after marker markers prefixGaps gap
          (internalGaps.filter (fun candidate => candidate != []) ++
            [finalGap])
          (by simp) multiple markerMember high
          (internalGaps.count []) (by
            simpa [List.append_assoc] using moveBalanced)
        have moveStep' :
            ListDerives
              (before ++
                AlphaOccurrencePairing.renderMarkerGaps markers
                  ((prefixGaps ++ [gap]) ++
                    List.replicate (internalGaps.count []) [] ++
                    internalGaps.filter
                      (fun candidate => candidate != []) ++ [finalGap]) ++
                after)
              (before ++
                AlphaOccurrencePairing.renderMarkerGaps markers
                  (prefixGaps ++ List.replicate (internalGaps.count []) [] ++
                    gap :: internalGaps.filter
                      (fun candidate => candidate != []) ++ [finalGap]) ++
                after) := by
          simpa [List.append_assoc] using moveStep
        simpa [empty, List.append_assoc] using tailStep.trans moveStep'

/-! ### Exact marker-gap presentation of the beta scaffold -/

private def scaffoldMarkerLabels (letters : List Nat) : List Nat :=
  let anchor := BetaScaffoldData.highBlock letters
  CanonicalData.renderSquares (BetaScaffoldData.doubledLabels letters) ++
    (BetaScaffoldData.interiorUnits letters).flatMap (fun _ => anchor) ++
      anchor

private def anchorGaps (anchor : List Nat) (gap : List Nat) :
    List (List Nat) :=
  List.replicate (anchor.length - 1) [] ++ [gap]

private def scaffoldUnitGaps (letters : List Nat) : List (List Nat) :=
  let anchor := BetaScaffoldData.highBlock letters
  (BetaScaffoldData.interiorUnits letters).flatMap (anchorGaps anchor)

private def scaffoldInternalGaps (letters : List Nat) : List (List Nat) :=
  let squares :=
    CanonicalData.renderSquares (BetaScaffoldData.doubledLabels letters)
  let anchor := BetaScaffoldData.highBlock letters
  List.replicate squares.length [] ++ scaffoldUnitGaps letters ++
    List.replicate (anchor.length - 1) []

private def scaffoldMarkerGaps (letters : List Nat) : List (List Nat) :=
  scaffoldInternalGaps letters ++ [S5_107.finalSimpleBlock letters]

private theorem anchorGaps_length
    (anchor gap : List Nat) (anchorNonempty : anchor ≠ []) :
    (anchorGaps anchor gap).length = anchor.length := by
  have anchorPositive : 0 < anchor.length :=
    List.length_pos_iff.mpr anchorNonempty
  simp [anchorGaps]
  omega

private theorem renderMarkerGaps_anchorGaps
    (anchor gap : List Nat) (anchorNonempty : anchor ≠ []) :
    AlphaOccurrencePairing.renderMarkerGaps anchor
      (anchorGaps anchor gap) = anchor ++ gap := by
  induction anchor with
  | nil => exact False.elim (anchorNonempty rfl)
  | cons head tail induction =>
      cases tail with
      | nil =>
          simp [anchorGaps,
            AlphaOccurrencePairing.renderMarkerGaps]
      | cons next rest =>
          have tailNonempty : next :: rest ≠ [] := by simp
          have tailStep := induction tailNonempty
          simpa [anchorGaps, List.replicate_succ,
            AlphaOccurrencePairing.renderMarkerGaps,
            List.append_assoc] using tailStep

private theorem renderMarkerGaps_emptyGaps (markers : List Nat) :
    AlphaOccurrencePairing.renderMarkerGaps markers
      (List.replicate markers.length []) = markers := by
  induction markers with
  | nil => rfl
  | cons marker markers induction =>
      rw [show (marker :: markers).length = Nat.succ markers.length by rfl,
        List.replicate_succ,
        AlphaOccurrencePairing.renderMarkerGaps, induction]
      simp

private theorem scaffoldUnitGaps_length
    (letters : List Nat)
    (anchorNonempty : BetaScaffoldData.highBlock letters ≠ []) :
    (scaffoldUnitGaps letters).length =
      (BetaScaffoldData.interiorUnits letters).length *
        (BetaScaffoldData.highBlock letters).length := by
  have generic : forall units : List (List Nat),
      (units.flatMap
          (anchorGaps (BetaScaffoldData.highBlock letters))).length =
        units.length * (BetaScaffoldData.highBlock letters).length := by
    intro units
    induction units with
    | nil => simp
    | cons unit units induction =>
        have chunkLength := anchorGaps_length
          (BetaScaffoldData.highBlock letters) unit anchorNonempty
        simp [chunkLength, induction, Nat.succ_mul,
          Nat.add_comm]
  simpa [scaffoldUnitGaps] using
    generic (BetaScaffoldData.interiorUnits letters)

private theorem scaffoldUnitGaps_filter
    (letters : List Nat) :
    (scaffoldUnitGaps letters).filter (fun gap => gap != []) =
      BetaScaffoldData.interiorUnits letters := by
  have generic : forall units : List (List Nat),
      (forall unit, unit ∈ units -> unit ≠ []) ->
      (units.flatMap
          (anchorGaps (BetaScaffoldData.highBlock letters))).filter
          (fun gap => gap != []) = units := by
    intro units unitsNonempty
    induction units with
    | nil => simp
    | cons unit units induction =>
        have unitNonempty := unitsNonempty unit (by simp)
        have tailNonempty : forall candidate,
            candidate ∈ units -> candidate ≠ [] := by
          intro candidate member
          exact unitsNonempty candidate (by simp [member])
        simp [anchorGaps, unitNonempty, induction tailNonempty]
  apply generic
  intro unit member
  exact BetaScaffoldData.interiorUnits_nonempty letters unit member

private theorem length_flatMap_constant
    (blocks : List (List Nat)) (anchor : List Nat) :
    (blocks.flatMap (fun _ => anchor)).length =
      blocks.length * anchor.length := by
  induction blocks with
  | nil => simp
  | cons block blocks induction =>
      simp [induction, Nat.succ_mul, Nat.add_comm]

private theorem renderMarkerGaps_anchoredUnits
    (anchor : List Nat) (anchorNonempty : anchor ≠ []) :
    forall (units : List (List Nat)) (finalGap : List Nat),
      AlphaOccurrencePairing.renderMarkerGaps
          (units.flatMap (fun _ => anchor) ++ anchor)
          (units.flatMap (anchorGaps anchor) ++
            anchorGaps anchor finalGap) =
        anchor ++ renderBetaUnitBlocks anchor units ++ finalGap := by
  intro units
  induction units with
  | nil =>
      intro finalGap
      simpa using renderMarkerGaps_anchorGaps
        anchor finalGap anchorNonempty
  | cons unit units induction =>
      intro finalGap
      have firstBalanced := anchorGaps_length
        anchor unit anchorNonempty
      have split := renderMarkerGaps_append anchor
        (units.flatMap (fun _ => anchor) ++ anchor)
        (anchorGaps anchor unit)
        (units.flatMap (anchorGaps anchor) ++
          anchorGaps anchor finalGap)
        firstBalanced
      have split' :
          AlphaOccurrencePairing.renderMarkerGaps
              (anchor ++ units.flatMap (fun _ => anchor) ++ anchor)
              (anchorGaps anchor unit ++
                units.flatMap (anchorGaps anchor) ++
                  anchorGaps anchor finalGap) =
            AlphaOccurrencePairing.renderMarkerGaps anchor
                (anchorGaps anchor unit) ++
              AlphaOccurrencePairing.renderMarkerGaps
                (units.flatMap (fun _ => anchor) ++ anchor)
                (units.flatMap (anchorGaps anchor) ++
                  anchorGaps anchor finalGap) := by
        simpa [List.append_assoc] using split
      rw [List.flatMap_cons, List.flatMap_cons, split']
      rw [renderMarkerGaps_anchorGaps anchor unit anchorNonempty,
        induction finalGap]
      simp [renderBetaUnitBlocks, List.append_assoc]

private theorem scaffoldMarkerGaps_balanced
    (letters : List Nat)
    (branch : CanonicalData.canonicalBranch letters = .beta) :
    (scaffoldMarkerGaps letters).length =
      (scaffoldMarkerLabels letters).length := by
  have anchorNonempty :=
    BetaScaffoldData.highBlock_ne_nil_of_branch_beta branch
  have unitGapsLength :=
    scaffoldUnitGaps_length letters anchorNonempty
  have anchorPositive :
      0 < (BetaScaffoldData.highBlock letters).length :=
    List.length_pos_iff.mpr anchorNonempty
  simp only [scaffoldMarkerGaps, scaffoldInternalGaps,
    scaffoldMarkerLabels, List.length_append, List.length_replicate,
    List.length_singleton]
  rw [unitGapsLength, length_flatMap_constant]
  omega

private theorem scaffoldInternalGaps_filter
    (letters : List Nat)
    (branch : CanonicalData.canonicalBranch letters = .beta) :
    (scaffoldInternalGaps letters).filter (fun gap => gap != []) =
      BetaScaffoldData.interiorUnits letters := by
  have anchorNonempty :=
    BetaScaffoldData.highBlock_ne_nil_of_branch_beta branch
  have anchorPositive :
      0 < (BetaScaffoldData.highBlock letters).length :=
    List.length_pos_iff.mpr anchorNonempty
  simp [scaffoldInternalGaps, scaffoldUnitGaps_filter letters]

private theorem scaffoldList_eq_markerGapRender
    (letters : List Nat)
    (branch : CanonicalData.canonicalBranch letters = .beta) :
    BetaScaffoldData.scaffoldList letters =
      S5_107.initialSimpleBlock letters ++
        AlphaOccurrencePairing.renderMarkerGaps
          (scaffoldMarkerLabels letters) (scaffoldMarkerGaps letters) := by
  have anchorNonempty :=
    BetaScaffoldData.highBlock_ne_nil_of_branch_beta branch
  let squares :=
    CanonicalData.renderSquares (BetaScaffoldData.doubledLabels letters)
  let anchor := BetaScaffoldData.highBlock letters
  let units := BetaScaffoldData.interiorUnits letters
  have rendered :
      AlphaOccurrencePairing.renderMarkerGaps
          (scaffoldMarkerLabels letters) (scaffoldMarkerGaps letters) =
        squares ++ anchor ++ renderBetaUnitBlocks anchor units ++
          S5_107.finalSimpleBlock letters := by
    have squareStep := renderMarkerGaps_emptyGaps squares
    have anchorStep := renderMarkerGaps_anchoredUnits
      anchor (by simpa [anchor] using anchorNonempty) units
        (S5_107.finalSimpleBlock letters)
    have combined :
        AlphaOccurrencePairing.renderMarkerGaps
            (squares ++ (units.flatMap (fun _ => anchor) ++ anchor))
            (List.replicate squares.length [] ++
              (units.flatMap (anchorGaps anchor) ++
                anchorGaps anchor (S5_107.finalSimpleBlock letters))) =
          squares ++ anchor ++ renderBetaUnitBlocks anchor units ++
            S5_107.finalSimpleBlock letters := by
      rw [renderMarkerGaps_append squares
        (units.flatMap (fun _ => anchor) ++ anchor)
        (List.replicate squares.length [])
        (units.flatMap (anchorGaps anchor) ++
          anchorGaps anchor (S5_107.finalSimpleBlock letters)) (by simp)]
      rw [squareStep, anchorStep]
      simp [List.append_assoc]
    simpa [scaffoldMarkerLabels, scaffoldMarkerGaps,
      scaffoldInternalGaps, scaffoldUnitGaps, anchorGaps,
      squares, anchor, units, List.append_assoc] using combined
  cases finalShape : S5_107.finalSimpleBlock letters with
  | nil =>
      rw [scaffoldList_eq_anchor_context_of_final_nil
        letters finalShape, rendered]
      simp [scaffoldPrefix, squares, anchor, units,
        finalShape, List.append_assoc]
  | cons first rest =>
      rw [scaffoldList_eq_anchor_context_of_final_cons
        letters first rest finalShape, rendered]
      simp [scaffoldPrefix, squares, anchor, units,
        finalShape, List.append_assoc]

/-! ### Source and scaffold marker inventories -/

private theorem count_renderCopies
    (exponent : Nat) (labels : List Nat) (tested : Nat) :
    (CanonicalData.renderCopies exponent labels).count tested =
      exponent * labels.count tested := by
  change (labels.flatMap
      (fun letter => List.replicate exponent letter)).count tested = _
  induction labels with
  | nil => simp
  | cons label labels induction =>
      by_cases equal : label = tested
      · subst label
        simp [induction, Nat.mul_add, Nat.add_comm]
      · have repeatedZero :
            (List.replicate exponent label).count tested = 0 := by
          rw [List.count_eq_zero]
          simp [Ne.symm equal]
        simp [induction, equal, repeatedZero]

private theorem count_flatMap_constant
    (blocks : List (List Nat)) (anchor : List Nat) (tested : Nat) :
    (blocks.flatMap (fun _ => anchor)).count tested =
      blocks.length * anchor.count tested := by
  induction blocks with
  | nil => simp
  | cons block blocks induction =>
      simp [induction, List.count_append, Nat.succ_mul,
        Nat.add_comm]

private theorem parsedMarkerLabels_count_eq_of_multiple
    (letters : List Nat) (marker : Nat)
    (multiple : 2 <= letters.count marker) :
    (AlphaParsedBridge.markerLabels letters).count marker =
      letters.count marker := by
  simpa [AlphaParsedBridge.markerLabels, ParsedWords.factors] using
    S5_107.count_terminatedFactorMarkers_of_multiple
      marker letters multiple

private theorem parsedMarkerLabels_count_eq_zero_of_small
    (letters : List Nat) (marker : Nat)
    (small : letters.count marker <= 1) :
    (AlphaParsedBridge.markerLabels letters).count marker = 0 := by
  rw [List.count_eq_zero]
  intro member
  have multiple := parsedMarker_nonsimple letters marker member
  omega

private theorem scaffoldMarkerLabels_count_eq_two
    (letters : List Nat) (marker : Nat)
    (doubled : letters.count marker = 2) :
    (scaffoldMarkerLabels letters).count marker = 2 := by
  have doubledMember :
      marker ∈ BetaScaffoldData.doubledLabels letters := by
    simpa [BetaScaffoldData.doubledLabels] using
      (CanonicalData.sortedDoubledLetters_mem_iff marker letters).2 doubled
  have highAbsent :
      marker ∉ BetaScaffoldData.highLabels letters := by
    intro member
    have high :=
      (CanonicalData.sortedHighCountLetters_mem_iff marker letters).1 (by
        simpa [BetaScaffoldData.highLabels] using member)
    omega
  have doubledCount :
      (BetaScaffoldData.doubledLabels letters).count marker = 1 := by
    have nodup :
        (BetaScaffoldData.doubledLabels letters).Nodup := by
      simpa [BetaScaffoldData.doubledLabels] using
        CanonicalData.sortedDoubledLetters_nodup letters
    rw [nodup.count]
    simp [doubledMember]
  have highCount :
      (BetaScaffoldData.highLabels letters).count marker = 0 := by
    rw [List.count_eq_zero]
    exact highAbsent
  have squareCount :
      (CanonicalData.renderSquares
        (BetaScaffoldData.doubledLabels letters)).count marker = 2 := by
    rw [CanonicalData.renderSquares, count_renderCopies, doubledCount]
  have anchorCount :
      (BetaScaffoldData.highBlock letters).count marker = 0 := by
    rw [BetaScaffoldData.highBlock, CanonicalData.renderCubes,
      count_renderCopies, highCount]
  change (CanonicalData.renderSquares
        (BetaScaffoldData.doubledLabels letters) ++
      (BetaScaffoldData.interiorUnits letters).flatMap
        (fun _ => BetaScaffoldData.highBlock letters) ++
      BetaScaffoldData.highBlock letters).count marker = 2
  simp only [List.count_append, squareCount, anchorCount,
    count_flatMap_constant]
  omega

private theorem scaffoldMarkerLabels_count_eq_zero_of_small
    (letters : List Nat) (marker : Nat)
    (small : letters.count marker <= 1) :
    (scaffoldMarkerLabels letters).count marker = 0 := by
  have doubledAbsent :
      marker ∉ BetaScaffoldData.doubledLabels letters := by
    intro member
    have doubled :=
      (CanonicalData.sortedDoubledLetters_mem_iff marker letters).1 (by
        simpa [BetaScaffoldData.doubledLabels] using member)
    omega
  have highAbsent :
      marker ∉ BetaScaffoldData.highLabels letters := by
    intro member
    have high :=
      (CanonicalData.sortedHighCountLetters_mem_iff marker letters).1 (by
        simpa [BetaScaffoldData.highLabels] using member)
    omega
  have doubledCount :
      (BetaScaffoldData.doubledLabels letters).count marker = 0 :=
    List.count_eq_zero.mpr doubledAbsent
  have highCount :
      (BetaScaffoldData.highLabels letters).count marker = 0 :=
    List.count_eq_zero.mpr highAbsent
  have squareCount :
      (CanonicalData.renderSquares
        (BetaScaffoldData.doubledLabels letters)).count marker = 0 := by
    rw [CanonicalData.renderSquares, count_renderCopies, doubledCount]
  have anchorCount :
      (BetaScaffoldData.highBlock letters).count marker = 0 := by
    rw [BetaScaffoldData.highBlock, CanonicalData.renderCubes,
      count_renderCopies, highCount]
  change (CanonicalData.renderSquares
        (BetaScaffoldData.doubledLabels letters) ++
      (BetaScaffoldData.interiorUnits letters).flatMap
        (fun _ => BetaScaffoldData.highBlock letters) ++
      BetaScaffoldData.highBlock letters).count marker = 0
  simp only [List.count_append, squareCount, anchorCount,
    count_flatMap_constant]
  omega

private theorem scaffoldMarkerLabels_count_ge_three
    (letters : List Nat) (marker : Nat)
    (high : 3 <= letters.count marker) :
    3 <= (scaffoldMarkerLabels letters).count marker := by
  have highMember :
      marker ∈ BetaScaffoldData.highLabels letters := by
    simpa [BetaScaffoldData.highLabels] using
      (CanonicalData.sortedHighCountLetters_mem_iff marker letters).2 high
  have highCount :
      (BetaScaffoldData.highLabels letters).count marker = 1 := by
    have nodup : (BetaScaffoldData.highLabels letters).Nodup := by
      simpa [BetaScaffoldData.highLabels] using
        CanonicalData.sortedHighCountLetters_nodup letters
    rw [nodup.count]
    simp [highMember]
  have anchorCount :
      (BetaScaffoldData.highBlock letters).count marker = 3 := by
    rw [BetaScaffoldData.highBlock, CanonicalData.renderCubes,
      count_renderCopies, highCount]
  change 3 <= (CanonicalData.renderSquares
        (BetaScaffoldData.doubledLabels letters) ++
      (BetaScaffoldData.interiorUnits letters).flatMap
        (fun _ => BetaScaffoldData.highBlock letters) ++
      BetaScaffoldData.highBlock letters).count marker
  simp only [List.count_append, anchorCount]
  omega

private theorem parsedMarkerLabels_high_iff
    (letters : List Nat) (marker : Nat) :
    3 <= (AlphaParsedBridge.markerLabels letters).count marker <->
      3 <= letters.count marker := by
  constructor
  · intro markerHigh
    have markerMember :
        marker ∈ AlphaParsedBridge.markerLabels letters :=
      List.count_pos_iff.mp (by omega)
    have multiple := parsedMarker_nonsimple letters marker markerMember
    rw [parsedMarkerLabels_count_eq_of_multiple
      letters marker multiple] at markerHigh
    exact markerHigh
  · intro markerHigh
    rw [parsedMarkerLabels_count_eq_of_multiple
      letters marker (by omega)]
    exact markerHigh

private theorem scaffoldMarkerLabels_high_iff
    (letters : List Nat) (marker : Nat) :
    3 <= (scaffoldMarkerLabels letters).count marker <->
      3 <= letters.count marker := by
  constructor
  · intro markerHigh
    by_cases sourceHigh : 3 <= letters.count marker
    · exact sourceHigh
    · by_cases doubled : letters.count marker = 2
      · rw [scaffoldMarkerLabels_count_eq_two
          letters marker doubled] at markerHigh
        omega
      · have small : letters.count marker <= 1 := by omega
        rw [scaffoldMarkerLabels_count_eq_zero_of_small
          letters marker small] at markerHigh
        omega
  · exact scaffoldMarkerLabels_count_ge_three letters marker

private theorem parsedMarkerLabels_multiple
    (letters : List Nat) :
    forall marker, marker ∈ AlphaParsedBridge.markerLabels letters ->
      2 <= (AlphaParsedBridge.markerLabels letters).count marker := by
  intro marker member
  have multiple := parsedMarker_nonsimple letters marker member
  rw [parsedMarkerLabels_count_eq_of_multiple letters marker multiple]
  exact multiple

private theorem scaffoldMarkerLabels_multiple
    (letters : List Nat) :
    forall marker, marker ∈ scaffoldMarkerLabels letters ->
      2 <= (scaffoldMarkerLabels letters).count marker := by
  intro marker member
  by_cases high : 3 <= letters.count marker
  · exact Nat.le_trans (by omega)
      (scaffoldMarkerLabels_count_ge_three letters marker high)
  · by_cases doubled : letters.count marker = 2
    · rw [scaffoldMarkerLabels_count_eq_two letters marker doubled]
      omega
    · have small : letters.count marker <= 1 := by omega
      have zero := scaffoldMarkerLabels_count_eq_zero_of_small
        letters marker small
      have positive : 0 < (scaffoldMarkerLabels letters).count marker :=
        List.count_pos_iff.mpr member
      omega

private theorem commonExpandedMarkerLabels_perm
    (letters : List Nat) :
    (highMarkerPart (scaffoldMarkerLabels letters) ++
        AlphaParsedBridge.markerLabels letters).Perm
      (highMarkerPart (AlphaParsedBridge.markerLabels letters) ++
        scaffoldMarkerLabels letters) := by
  rw [List.perm_iff_count]
  intro marker
  have highIff :
      3 <= (AlphaParsedBridge.markerLabels letters).count marker <->
        3 <= (scaffoldMarkerLabels letters).count marker := by
    rw [parsedMarkerLabels_high_iff, scaffoldMarkerLabels_high_iff]
  by_cases sourceHigh :
      3 <= (AlphaParsedBridge.markerLabels letters).count marker
  · have targetHigh := highIff.mp sourceHigh
    rw [List.count_append, List.count_append,
      count_highMarkerPart, count_highMarkerPart,
      if_pos targetHigh, if_pos sourceHigh]
    omega
  · have targetNotHigh :
        ¬(3 <= (scaffoldMarkerLabels letters).count marker) := by
      exact fun targetHigh => sourceHigh (highIff.mpr targetHigh)
    have sourceCountEqTarget :
        (AlphaParsedBridge.markerLabels letters).count marker =
          (scaffoldMarkerLabels letters).count marker := by
      have sourceNotHighLetters : ¬(3 <= letters.count marker) := by
        intro sourceLettersHigh
        exact sourceHigh <|
          (parsedMarkerLabels_high_iff letters marker).2 sourceLettersHigh
      by_cases doubled : letters.count marker = 2
      · rw [parsedMarkerLabels_count_eq_of_multiple
            letters marker (by omega),
          scaffoldMarkerLabels_count_eq_two letters marker doubled,
          doubled]
      · have small : letters.count marker <= 1 := by omega
        rw [parsedMarkerLabels_count_eq_zero_of_small
            letters marker small,
          scaffoldMarkerLabels_count_eq_zero_of_small
            letters marker small]
    rw [List.count_append, List.count_append,
      count_highMarkerPart, count_highMarkerPart,
      if_neg targetNotHigh, if_neg sourceHigh,
      sourceCountEqTarget]

private theorem filter_terminatedFactorBlocks_ne_nil
    (factors : List ParsedWords.Factor) :
    (S5_107.terminatedFactorBlocks factors).filter
        (fun gap => gap != []) =
      S5_107.nonemptyTerminatedBlocks factors := by
  change (factors.map (fun factor => factor.1)).filter
      (fun gap => gap != []) = S5_107.nonemptyTerminatedBlocks factors
  induction factors with
  | nil => rfl
  | cons factor factors induction =>
      rcases factor with ⟨block, marker⟩
      by_cases empty : block = []
      · subst block
        simp [S5_107.nonemptyTerminatedBlocks, induction]
      · simp [S5_107.nonemptyTerminatedBlocks, empty, induction]

private theorem appendHighMarkers_multiple
    (markers additions : List Nat)
    (multiple :
      forall marker, marker ∈ markers -> 2 <= markers.count marker)
    (additionsHigh :
      forall marker, marker ∈ additions -> 3 <= markers.count marker) :
    forall marker, marker ∈ additions ++ markers ->
      2 <= (additions ++ markers).count marker := by
  intro marker member
  rcases List.mem_append.mp member with added | original
  · have high := additionsHigh marker added
    simp only [List.count_append]
    omega
  · have bound := multiple marker original
    simp only [List.count_append]
    omega

/-! ### Terminal beta source-to-scaffold derivation -/

/-- Every beta-branch word derives to the exact raw scaffold used by the
repeated-anchor unit normalizer. -/
theorem listDerivesToScaffold_of_branch_beta
    (letters : List Nat)
    (branch : CanonicalData.canonicalBranch letters = .beta) :
    ListDerives letters (BetaScaffoldData.scaffoldList letters) := by
  obtain ⟨firstFactor, restFactors, factorsShape⟩ :=
    List.exists_cons_of_ne_nil (factors_ne_nil_of_branch_beta branch)
  have sourceGapsShape :
      AlphaParsedBridge.postMarkerGaps letters =
        S5_107.terminatedFactorBlocks restFactors ++
          [S5_107.finalSimpleBlock letters] := by
    simp [AlphaParsedBridge.postMarkerGaps, factorsShape,
      ParsedWords.finalBlock_eq_finalSimpleBlock]
  have sourcePayload :
      (S5_107.terminatedFactorBlocks restFactors).filter
          (fun gap => gap != []) =
        BetaScaffoldData.interiorUnits letters := by
    rw [filter_terminatedFactorBlocks_ne_nil]
    simpa [BetaScaffoldData.interiorUnits] using
      ParsedWords.nonemptyRestBlocks_eq_interiorSimpleBlocks
        letters firstFactor restFactors factorsShape
  have targetPayload := scaffoldInternalGaps_filter letters branch
  have sourceBalanced :
      (S5_107.terminatedFactorBlocks restFactors ++
          [S5_107.finalSimpleBlock letters]).length =
        (AlphaParsedBridge.markerLabels letters).length := by
    rw [← sourceGapsShape]
    exact AlphaParsedBridge.postMarkerGaps_length_eq_markerLabels_length
      letters
  have targetBalanced :
      (scaffoldInternalGaps letters ++
          [S5_107.finalSimpleBlock letters]).length =
        (scaffoldMarkerLabels letters).length := by
    simpa [scaffoldMarkerGaps] using
      scaffoldMarkerGaps_balanced letters branch
  obtain ⟨selected, selectedHighInLetters⟩ :=
    CanonicalData.exists_count_ge_three_of_branch_beta branch
  have selectedHighInSource :
      3 <= (AlphaParsedBridge.markerLabels letters).count selected := by
    exact (parsedMarkerLabels_high_iff letters selected).2
      selectedHighInLetters
  have selectedInSource :
      selected ∈ AlphaParsedBridge.markerLabels letters :=
    List.count_pos_iff.mp (by omega)
  have selectedHighInTarget :
      3 <= (scaffoldMarkerLabels letters).count selected :=
    (scaffoldMarkerLabels_high_iff letters selected).2
      selectedHighInLetters
  have selectedInTarget : selected ∈ scaffoldMarkerLabels letters :=
    List.count_pos_iff.mp (by omega)
  have sourceMultiple := parsedMarkerLabels_multiple letters
  have targetMultiple := scaffoldMarkerLabels_multiple letters
  have sourceCanonicalBalanced :
      (List.replicate
            ((S5_107.terminatedFactorBlocks restFactors).count []) [] ++
          (S5_107.terminatedFactorBlocks restFactors).filter
            (fun gap => gap != []) ++
          [S5_107.finalSimpleBlock letters]).length =
        (AlphaParsedBridge.markerLabels letters).length := by
    have partitionLength := count_nil_add_filter_ne_nil_length
      (S5_107.terminatedFactorBlocks restFactors)
    simp only [List.length_append, List.length_replicate,
      List.length_singleton]
    simp only [List.length_append, List.length_singleton] at sourceBalanced
    omega
  have targetCanonicalBalanced :
      (List.replicate ((scaffoldInternalGaps letters).count []) [] ++
          (scaffoldInternalGaps letters).filter (fun gap => gap != []) ++
          [S5_107.finalSimpleBlock letters]).length =
        (scaffoldMarkerLabels letters).length := by
    have partitionLength := count_nil_add_filter_ne_nil_length
      (scaffoldInternalGaps letters)
    simp only [List.length_append, List.length_replicate,
      List.length_singleton]
    simp only [List.length_append, List.length_singleton] at targetBalanced
    omega
  have sourceNormalizedRaw := listDerivesMoveInternalEmptiesFront
    (S5_107.initialSimpleBlock letters) [] selected
    (AlphaParsedBridge.markerLabels letters) []
    (S5_107.terminatedFactorBlocks restFactors)
    (S5_107.finalSimpleBlock letters)
    (by simpa using sourceBalanced) sourceMultiple selectedInSource
    selectedHighInSource
  have sourceReconstruction :=
    reconstruct_with_initialSimpleBlock_of_branch_beta letters branch
  rw [sourceGapsShape] at sourceReconstruction
  have sourceNormalized :
      ListDerives letters
        (S5_107.initialSimpleBlock letters ++
          AlphaOccurrencePairing.renderMarkerGaps
            (AlphaParsedBridge.markerLabels letters)
            (List.replicate
                ((S5_107.terminatedFactorBlocks restFactors).count []) [] ++
              (S5_107.terminatedFactorBlocks restFactors).filter
                (fun gap => gap != []) ++
              [S5_107.finalSimpleBlock letters])) := by
    simpa only [List.nil_append, List.append_nil, sourceReconstruction] using
      sourceNormalizedRaw
  have targetNormalizedRaw := listDerivesMoveInternalEmptiesFront
    (S5_107.initialSimpleBlock letters) [] selected
    (scaffoldMarkerLabels letters) [] (scaffoldInternalGaps letters)
    (S5_107.finalSimpleBlock letters)
    (by simpa using targetBalanced) targetMultiple selectedInTarget
    selectedHighInTarget
  have targetNormalized :
      ListDerives (BetaScaffoldData.scaffoldList letters)
        (S5_107.initialSimpleBlock letters ++
          AlphaOccurrencePairing.renderMarkerGaps
            (scaffoldMarkerLabels letters)
            (List.replicate ((scaffoldInternalGaps letters).count []) [] ++
              (scaffoldInternalGaps letters).filter
                (fun gap => gap != []) ++
              [S5_107.finalSimpleBlock letters])) := by
    rw [scaffoldList_eq_markerGapRender letters branch]
    simpa [scaffoldMarkerGaps, List.append_assoc] using
      targetNormalizedRaw
  have sourceAdditionsHigh :
      forall marker,
        marker ∈ highMarkerPart (scaffoldMarkerLabels letters) ->
          3 <= (AlphaParsedBridge.markerLabels letters).count marker := by
    intro marker member
    have targetHigh : 3 <= (scaffoldMarkerLabels letters).count marker := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp member).2
    have sourceHighInLetters :=
      (scaffoldMarkerLabels_high_iff letters marker).1 targetHigh
    exact (parsedMarkerLabels_high_iff letters marker).2
      sourceHighInLetters
  have targetAdditionsHigh :
      forall marker,
        marker ∈ highMarkerPart
          (AlphaParsedBridge.markerLabels letters) ->
          3 <= (scaffoldMarkerLabels letters).count marker := by
    intro marker member
    have sourceHigh :
        3 <= (AlphaParsedBridge.markerLabels letters).count marker := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp member).2
    have sourceHighInLetters :=
      (parsedMarkerLabels_high_iff letters marker).1 sourceHigh
    exact (scaffoldMarkerLabels_high_iff letters marker).2
      sourceHighInLetters
  have sourceExpanded := listDerivesPrependHighSlots
    (S5_107.initialSimpleBlock letters) []
    (AlphaParsedBridge.markerLabels letters)
    (List.replicate
        ((S5_107.terminatedFactorBlocks restFactors).count []) [] ++
      (S5_107.terminatedFactorBlocks restFactors).filter
        (fun gap => gap != []) ++
      [S5_107.finalSimpleBlock letters])
    sourceCanonicalBalanced sourceMultiple
    (highMarkerPart (scaffoldMarkerLabels letters)) sourceAdditionsHigh
  have targetExpanded := listDerivesPrependHighSlots
    (S5_107.initialSimpleBlock letters) []
    (scaffoldMarkerLabels letters)
    (List.replicate ((scaffoldInternalGaps letters).count []) [] ++
      (scaffoldInternalGaps letters).filter (fun gap => gap != []) ++
      [S5_107.finalSimpleBlock letters])
    targetCanonicalBalanced targetMultiple
    (highMarkerPart (AlphaParsedBridge.markerLabels letters))
    targetAdditionsHigh
  have commonPermutation := commonExpandedMarkerLabels_perm letters
  have sourcePartitionLength := count_nil_add_filter_ne_nil_length
    (S5_107.terminatedFactorBlocks restFactors)
  have targetPartitionLength := count_nil_add_filter_ne_nil_length
    (scaffoldInternalGaps letters)
  have payloadLength :
      ((S5_107.terminatedFactorBlocks restFactors).filter
          (fun gap => gap != [])).length =
        ((scaffoldInternalGaps letters).filter
          (fun gap => gap != [])).length := by
    rw [sourcePayload, targetPayload]
  have commonLength := commonPermutation.length_eq
  have frontCountEq :
      (highMarkerPart (scaffoldMarkerLabels letters)).length +
          (S5_107.terminatedFactorBlocks restFactors).count [] =
        (highMarkerPart
            (AlphaParsedBridge.markerLabels letters)).length +
          (scaffoldInternalGaps letters).count [] := by
    simp only [List.length_append] at commonLength
    simp only [List.length_append, List.length_singleton] at sourceBalanced targetBalanced
    omega
  have expandedGapsEq :
      List.replicate
            (highMarkerPart (scaffoldMarkerLabels letters)).length [] ++
          List.replicate
            ((S5_107.terminatedFactorBlocks restFactors).count []) [] ++
          (S5_107.terminatedFactorBlocks restFactors).filter
            (fun gap => gap != []) ++
          [S5_107.finalSimpleBlock letters] =
        List.replicate
            (highMarkerPart
              (AlphaParsedBridge.markerLabels letters)).length [] ++
          List.replicate ((scaffoldInternalGaps letters).count []) [] ++
          (scaffoldInternalGaps letters).filter (fun gap => gap != []) ++
          [S5_107.finalSimpleBlock letters] := by
    rw [← replicate_nil_add, ← replicate_nil_add, frontCountEq,
      sourcePayload, targetPayload]
  have sourceExpandedBalanced :
      (List.replicate
            (highMarkerPart (scaffoldMarkerLabels letters)).length [] ++
          List.replicate
            ((S5_107.terminatedFactorBlocks restFactors).count []) [] ++
          (S5_107.terminatedFactorBlocks restFactors).filter
            (fun gap => gap != []) ++
          [S5_107.finalSimpleBlock letters]).length =
        (highMarkerPart (scaffoldMarkerLabels letters) ++
          AlphaParsedBridge.markerLabels letters).length := by
    have canonicalLength := sourceCanonicalBalanced
    simp only [List.length_append, List.length_replicate] at canonicalLength ⊢
    omega
  have sourceExpandedMultiple := appendHighMarkers_multiple
    (AlphaParsedBridge.markerLabels letters)
    (highMarkerPart (scaffoldMarkerLabels letters))
    sourceMultiple sourceAdditionsHigh
  have markerPermutation := listDerivesPermuteMarkerGaps_of_counts
    (S5_107.initialSimpleBlock letters) []
    (List.replicate
        (highMarkerPart (scaffoldMarkerLabels letters)).length [] ++
      List.replicate
        ((S5_107.terminatedFactorBlocks restFactors).count []) [] ++
      (S5_107.terminatedFactorBlocks restFactors).filter
        (fun gap => gap != []) ++
      [S5_107.finalSimpleBlock letters])
    sourceExpandedBalanced sourceExpandedMultiple commonPermutation
  simp only [List.append_assoc, List.append_nil] at sourceNormalized sourceExpanded markerPermutation
  simp only [List.append_assoc] at expandedGapsEq targetNormalized
  simp only [List.append_assoc, List.append_nil] at targetExpanded
  rw [← expandedGapsEq] at targetExpanded
  exact sourceNormalized.trans
    (sourceExpanded.trans
      (markerPermutation.trans
        (targetExpanded.symm.trans targetNormalized.symm)))

end BetaScaffoldMoves

end SemigroupBasis.CoRoots.Order6SporadicSection15
