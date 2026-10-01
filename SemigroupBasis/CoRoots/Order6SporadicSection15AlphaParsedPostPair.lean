import SemigroupBasis.CoRoots.Order6SporadicSection15AlphaParsedBridge
import SemigroupBasis.CoRoots.Order6SporadicSection15AlphaPostPair

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

namespace AlphaParsedPostPair

/-- Pair and sort the parsed markers of an alpha word, then compact all
internal post-marker gaps while retaining the parser's final block. -/
theorem listDerivesPairSortAndCompact_of_branch_alpha
    (letters : List Nat)
    (branch : CanonicalData.canonicalBranch letters = .alpha) :
    ∃ internal compacted : List (List Nat),
      AlphaParsedBridge.postMarkerGaps letters =
          internal ++ [ParsedWords.finalBlock letters] ∧
      ListDerives letters
        (S5_107.initialSimpleBlock letters ++
          AlphaSlotMoves.renderPairedGapSlots
            (AlphaPostPair.sortedPairedLabels
              (AlphaPostPair.pairedLabels
                (AlphaOccurrencePairing.pairMarkerOccurrences
                  (AlphaParsedBridge.markerLabels letters))))
            compacted ++
          ParsedWords.finalBlock letters) ∧
      AlphaSlotMoves.emptyBeforeNonemptyInversions compacted = 0 ∧
      internal.Perm compacted := by
  obtain ⟨internal, gapShape⟩ :=
    AlphaParsedBridge.exists_internal_postMarkerGaps_of_branch_alpha branch
  have balanced :
      (AlphaParsedBridge.postMarkerGaps letters).length =
        (AlphaParsedBridge.markerLabels letters).length :=
    AlphaParsedBridge.postMarkerGaps_length_eq_markerLabels_length letters
  have twice :
      AlphaOccurrencePairing.TwiceOccurringMarkers
        (AlphaParsedBridge.markerLabels letters) :=
    AlphaParsedBridge.twiceOccurringMarkers_of_branch_alpha branch
  have markerFree :
      AlphaOccurrencePairing.MarkerFreeGaps
        (AlphaParsedBridge.markerLabels letters)
        (AlphaParsedBridge.postMarkerGaps letters) :=
    AlphaParsedBridge.markerFreeGaps letters
  obtain ⟨compacted, derivation, compactedZero, permutation⟩ :=
    AlphaPostPair.listDerivesPairSortAndCompactAlphaSlots
      (S5_107.initialSimpleBlock letters) []
      (AlphaParsedBridge.markerLabels letters)
      (AlphaParsedBridge.postMarkerGaps letters)
      internal (ParsedWords.finalBlock letters)
      balanced gapShape twice markerFree
  have derivationWithoutAfter :
      ListDerives
        (S5_107.initialSimpleBlock letters ++
          AlphaOccurrencePairing.renderMarkerGaps
            (AlphaParsedBridge.markerLabels letters)
            (AlphaParsedBridge.postMarkerGaps letters))
        (S5_107.initialSimpleBlock letters ++
          AlphaSlotMoves.renderPairedGapSlots
            (AlphaPostPair.sortedPairedLabels
              (AlphaPostPair.pairedLabels
                (AlphaOccurrencePairing.pairMarkerOccurrences
                  (AlphaParsedBridge.markerLabels letters))))
            compacted ++
          ParsedWords.finalBlock letters) := by
    simpa only [List.append_nil] using derivation
  have reconstructed :=
    AlphaParsedBridge.reconstruct_with_initialSimpleBlock_of_branch_alpha
      letters branch
  rw [reconstructed] at derivationWithoutAfter
  exact
    ⟨internal, compacted, gapShape,
      derivationWithoutAfter,
      compactedZero, permutation⟩

end AlphaParsedPostPair

end SemigroupBasis.CoRoots.Order6SporadicSection15
