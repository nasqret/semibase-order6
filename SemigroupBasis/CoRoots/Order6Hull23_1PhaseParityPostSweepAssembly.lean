import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityPostSweepFold

/-!
# Hull 23.1 explicit post-sweep assembly

This module composes the exact post-sweep interfaces without importing the
word-level normalization module.  Its source and target lists are stated
literally so that `Order6Hull23_1PhaseParityNormalization` can import this
module without creating an import cycle.

The active debt carrier is always
`gapDebt lastBlock ++ sweptPriorDebt beforeBlocks`.  The old-letter debt of
the selected final gap is part of that carrier and is not discarded.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull23_1PhaseParityPowerNormalization

open SemigroupBasis.CoRoots.S5_831
open SemigroupBasis.CoRoots.S5_870
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityInvariant
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockFacts
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityDebtMoves
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityGapMoves
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityPowerMoves

/-! ## Exact selected-gap regrouping -/

/-- Regroup the selected swept gap into one exact terminal power followed by
the corrected active carrier.  In particular, the marker copies contained in
`sweptGapDebt lastBlock` join the terminal power, while its `gapDebt` summand
remains in front of the debt emitted by the prior-block sweep. -/
theorem postSweepActiveList_eq_regrouped
    (beforeBlocks : List GapBlock) (lastBlock : GapBlock)
    (suffix : List Nat) :
    renderSweptPriorBlocks beforeBlocks ++
        sweptGapMarkerPower lastBlock ++
        [lastBlock.marker, lastBlock.marker] ++
        sweptGapDebt lastBlock ++
        sweptPriorDebt beforeBlocks ++ suffix =
      renderSweptPriorBlocks beforeBlocks ++
        List.replicate
          (selectedTerminalExponent lastBlock) lastBlock.marker ++
        (gapDebt lastBlock ++ sweptPriorDebt beforeBlocks) ++ suffix := by
  have powerShape :
      List.replicate
            (lastBlock.seconds.length + 1) lastBlock.marker ++
          [lastBlock.marker, lastBlock.marker] ++
          List.replicate
            (gapDebt lastBlock).length lastBlock.marker =
        List.replicate
          (selectedTerminalExponent lastBlock) lastBlock.marker := by
    calc
      List.replicate
              (lastBlock.seconds.length + 1) lastBlock.marker ++
            [lastBlock.marker, lastBlock.marker] ++
            List.replicate
              (gapDebt lastBlock).length lastBlock.marker =
          (List.replicate
                (lastBlock.seconds.length + 1) lastBlock.marker ++
              List.replicate 2 lastBlock.marker) ++
            List.replicate
              (gapDebt lastBlock).length lastBlock.marker := by
        simp [List.append_assoc]
      _ = List.replicate
              ((lastBlock.seconds.length + 1) + 2) lastBlock.marker ++
            List.replicate
              (gapDebt lastBlock).length lastBlock.marker := by
        exact congrArg
          (fun terminalPrefix =>
            terminalPrefix ++
              List.replicate
                (gapDebt lastBlock).length lastBlock.marker)
          (replicate_add_power
            (lastBlock.seconds.length + 1) 2 lastBlock.marker).symm
      _ = List.replicate
            (((lastBlock.seconds.length + 1) + 2) +
              (gapDebt lastBlock).length) lastBlock.marker :=
        (replicate_add_power
          ((lastBlock.seconds.length + 1) + 2)
          (gapDebt lastBlock).length lastBlock.marker).symm
      _ = List.replicate
            (selectedTerminalExponent lastBlock) lastBlock.marker := by
        rfl
  calc
    renderSweptPriorBlocks beforeBlocks ++
          sweptGapMarkerPower lastBlock ++
          [lastBlock.marker, lastBlock.marker] ++
          sweptGapDebt lastBlock ++
          sweptPriorDebt beforeBlocks ++ suffix =
        renderSweptPriorBlocks beforeBlocks ++
          (List.replicate
                (lastBlock.seconds.length + 1) lastBlock.marker ++
              [lastBlock.marker, lastBlock.marker] ++
              List.replicate
                (gapDebt lastBlock).length lastBlock.marker) ++
          (gapDebt lastBlock ++ sweptPriorDebt beforeBlocks) ++ suffix := by
      rw [sweptGapMarkerPower_eq_replicate]
      simp [sweptGapDebt, List.append_assoc]
    _ = renderSweptPriorBlocks beforeBlocks ++
          List.replicate
            (selectedTerminalExponent lastBlock) lastBlock.marker ++
          (gapDebt lastBlock ++ sweptPriorDebt beforeBlocks) ++ suffix := by
      rw [powerShape]

/-! ## Complete explicit active-skeleton endpoint -/

/-- Close the literal post-sweep active skeleton to the literal last-doubled
canonical split.  The hypotheses are exactly the parser and entry-alignment
facts exposed by `ActivePhaseParitySkeletonCompletion`, but neither that
contract nor the normalization module is referenced here. -/
theorem hullListDerivesPostSweepCanonical
    (word : Word Nat)
    (beforeBlocks : List GapBlock) (lastBlock : GapBlock)
    (afterBlocks : List GapBlock)
    (beforeEntries : List PhaseParityEntry)
    (lastEntry : PhaseParityEntry)
    (afterEntries : List PhaseParityEntry)
    (anchor : Nat) (remaining : List Nat)
    (sourceSplit :
      gapBlocksList word.toList =
        beforeBlocks ++ lastBlock :: afterBlocks)
    (lastShape : lastBlock.seconds = anchor :: remaining)
    (lastNonempty : lastBlock.seconds ≠ [])
    (afterEmpty :
      forall block, block ∈ afterBlocks -> block.seconds = [])
    (entrySplit :
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        beforeEntries ++ lastEntry :: afterEntries)
    (beforeAligned :
      beforeEntries.map (fun entry => entry.phase) =
        beforeBlocks.map phaseOfGapBlock)
    (lastAligned : lastEntry.phase = phaseOfGapBlock lastBlock)
    (afterAligned :
      afterEntries.map (fun entry => entry.phase) =
        afterBlocks.map phaseOfGapBlock)
    (lastDoubled : lastEntry.phase.doubled = true)
    (afterUndoubled :
      forall entry, entry ∈ afterEntries ->
        entry.phase.doubled = false) :
    HullListDerives
      (renderSweptPriorBlocks beforeBlocks ++ [lastBlock.marker] ++
        remaining ++ [anchor, lastBlock.marker, lastBlock.marker] ++
        sweptPriorDebt beforeBlocks ++ gapBlockMarkers afterBlocks)
      (renderGapBlocks (canonicalPriorGapBlocks beforeEntries) ++
        renderGapBlocks
          [lastDoubledGapBlock (collectParityDebt beforeEntries) lastEntry] ++
        renderGapBlocks (markerOnlyGapBlocks afterEntries)) := by
  have formed :
      GapBlocksWellFormed []
        (beforeBlocks ++ lastBlock :: afterBlocks) := by
    rw [← sourceSplit]
    exact gapBlocksList_wellFormed word.toList
  have beforeFormed : GapBlocksWellFormed [] beforeBlocks :=
    (gapBlocksWellFormed_append formed).1
  have regroupedShape :=
    postSweepActiveList_eq_regrouped
      beforeBlocks lastBlock (gapBlockMarkers afterBlocks)
  have sweptRaw :=
    hullListDerivesSweepSelectedLastGapAcrossExposedSquare
      (gapBlockMarkers afterBlocks) formed lastShape
  have swept :
      HullListDerives
        (renderSweptPriorBlocks beforeBlocks ++ [lastBlock.marker] ++
          remaining ++ [anchor, lastBlock.marker, lastBlock.marker] ++
          sweptPriorDebt beforeBlocks ++ gapBlockMarkers afterBlocks)
        (renderSweptPriorBlocks beforeBlocks ++
          List.replicate
            (selectedTerminalExponent lastBlock) lastBlock.marker ++
          (gapDebt lastBlock ++ sweptPriorDebt beforeBlocks) ++
          gapBlockMarkers afterBlocks) := by
    rw [regroupedShape] at sweptRaw
    exact sweptRaw
  obtain ⟨data, dataEntries, _dataExponents, dataRender⟩ :=
    exists_priorPowerData_of_phase_alignment
      beforeBlocks beforeEntries beforeAligned
  have dataLabelsShape :
      data.map (fun datum => datum.entry.phase.label) =
        gapBlockMarkers beforeBlocks :=
    priorPowerData_labels_eq_gapBlockMarkers
      beforeBlocks beforeEntries data dataEntries beforeAligned
  have dataLabelsNodup :
      (data.map (fun datum => datum.entry.phase.label)).Nodup := by
    rw [dataLabelsShape]
    exact beforeFormed.markersNodup
  have oddLabelsNodup : (priorDebtLabels data).Nodup :=
    priorDebtLabels_nodup data dataLabelsNodup
  have residueExact :=
    activePriorDebt_count_mod_two_eq_priorDebtLabels
      word sourceSplit afterEmpty entrySplit beforeAligned
      dataEntries dataRender
  have residueModTwo :
      forall letter,
        (gapDebt lastBlock ++ sweptPriorDebt beforeBlocks).count
              letter % 2 =
          (priorDebtLabels data).count letter % 2 := by
    intro letter
    have oddAtMostOne : (priorDebtLabels data).count letter ≤ 1 :=
      List.nodup_iff_count.mp oddLabelsNodup letter
    calc
      (gapDebt lastBlock ++ sweptPriorDebt beforeBlocks).count
              letter % 2 =
          (priorDebtLabels data).count letter :=
        residueExact letter
      _ = (priorDebtLabels data).count letter % 2 := by
        omega
  obtain ⟨pairMarkers, countSplit, pairSeenRaw⟩ :=
    exists_activePriorDebt_pairMarkers
      formed dataRender dataLabelsNodup residueModTwo
  have activeCarrierSeen :
      forall letter,
        letter ∈ gapDebt lastBlock ++ sweptPriorDebt beforeBlocks ->
          letter ∈ renderPriorPowerData data :=
    activePriorDebt_seen_in_renderPriorPowerData formed dataRender
  have activeCarrierSeenWithTerminal :
      forall letter,
        letter ∈ gapDebt lastBlock ++ sweptPriorDebt beforeBlocks ->
          letter ∈
            renderPriorPowerData data ++
              List.replicate
                (selectedTerminalExponent lastBlock) lastBlock.marker := by
    intro letter member
    exact List.mem_append.mpr <| Or.inl <|
      activeCarrierSeen letter member
  have decomposedRaw :=
    hullListDerivesDecomposeWitnessedDebt
      (renderPriorPowerData data ++
        List.replicate
          (selectedTerminalExponent lastBlock) lastBlock.marker)
      (gapBlockMarkers afterBlocks)
      (gapDebt lastBlock ++ sweptPriorDebt beforeBlocks)
      pairMarkers (priorDebtLabels data)
      activeCarrierSeenWithTerminal countSplit
  have decomposed :
      HullListDerives
        (renderSweptPriorBlocks beforeBlocks ++
          List.replicate
            (selectedTerminalExponent lastBlock) lastBlock.marker ++
          (gapDebt lastBlock ++ sweptPriorDebt beforeBlocks) ++
          gapBlockMarkers afterBlocks)
        (renderPriorPowerData data ++
          List.replicate
            (selectedTerminalExponent lastBlock) lastBlock.marker ++
          displayedMarkerPairs pairMarkers ++
          priorDebtLabels data ++ gapBlockMarkers afterBlocks) := by
    simpa [dataRender, List.append_assoc] using decomposedRaw
  have selectedTerminalPositive :
      0 < selectedTerminalExponent lastBlock := by
    simp only [selectedTerminalExponent]
    omega
  have foldedRaw :=
    hullListDerivesNormalizePriorPowerData
      data pairMarkers (gapBlockMarkers afterBlocks)
      lastBlock.marker (selectedTerminalExponent lastBlock)
      selectedTerminalPositive pairSeenRaw
  have folded :
      HullListDerives
        (renderPriorPowerData data ++
          List.replicate
            (selectedTerminalExponent lastBlock) lastBlock.marker ++
          displayedMarkerPairs pairMarkers ++
          priorDebtLabels data ++ gapBlockMarkers afterBlocks)
        (renderGapBlocks (canonicalPriorGapBlocks beforeEntries) ++
          List.replicate
            (terminalExponentAfterPrior lastBlock data) lastBlock.marker ++
          displayedMarkerPairs pairMarkers ++
          retainedPriorDebt data ++ gapBlockMarkers afterBlocks) := by
    simpa [dataEntries, terminalExponentAfterPrior,
      List.append_assoc] using foldedRaw
  have lastLabelAligned :
      lastEntry.phase.label = lastBlock.marker := by
    simpa [phaseOfGapBlock] using congrArg Phase.label lastAligned
  have terminalLowerBound :
      4 <= terminalExponentAfterPrior lastBlock data :=
    terminalExponentAfterPrior_ge_four
      lastBlock data lastNonempty
  let terminalDatum : TerminalPowerDatum := {
    entry := lastEntry
    exponent := terminalExponentAfterPrior lastBlock data
    debt := retainedPriorDebt data
    exponent_pos := by omega
    parity_eq :=
      terminalExponentAfterPrior_parity
        word data sourceSplit afterEmpty entrySplit lastAligned
    singleton_has_debt := by
      intro exponentOne
      omega
  }
  have terminalAtLeastThree : 3 <= terminalDatum.exponent := by
    dsimp [terminalDatum]
    omega
  have labelSeenCanonical :
      forall letter,
        letter ∈ data.map (fun datum => datum.entry.phase.label) ->
          letter ∈
            renderGapBlocks (canonicalPriorGapBlocks beforeEntries) := by
    intro letter member
    obtain ⟨datum, datumMember, labelEqual⟩ :=
      List.mem_map.mp member
    rw [
      SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.mem_render_canonicalPriorGapBlocks_iff]
    refine ⟨datum.entry, ?_, labelEqual.symm⟩
    rw [← dataEntries]
    exact List.mem_map.mpr ⟨datum, datumMember, rfl⟩
  have pairSeenCanonical :
      forall marker, marker ∈ pairMarkers ->
        marker ∈
          renderGapBlocks (canonicalPriorGapBlocks beforeEntries) := by
    intro marker member
    exact labelSeenCanonical marker <|
      renderPriorPowerData_label_support
        (pairSeenRaw marker member)
  have terminalDebtSeen :
      forall letter, letter ∈ terminalDatum.debt ->
        letter ∈
          renderGapBlocks (canonicalPriorGapBlocks beforeEntries) := by
    intro letter member
    apply labelSeenCanonical letter
    apply retainedPriorDebt_support data letter
    simpa [terminalDatum] using member
  have terminalRaw :=
    hullListDerivesTransferPairsAndNormalizeTerminal
      (renderGapBlocks (canonicalPriorGapBlocks beforeEntries))
      (gapBlockMarkers afterBlocks) pairMarkers terminalDatum
      terminalAtLeastThree pairSeenCanonical terminalDebtSeen
  have retainedShape :
      retainedPriorDebt data = collectParityDebt beforeEntries :=
    retainedPriorDebt_eq_collectParityDebt
      data beforeEntries dataEntries
  have afterLabelsShape :
      SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.entryLabels
          afterEntries =
        gapBlockMarkers afterBlocks := by
    have labelsEqual :=
      congrArg (List.map Phase.label) afterAligned
    simpa [
      SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.entryLabels,
      gapBlockMarkers, phaseOfGapBlock,
      List.map_map, Function.comp_def] using labelsEqual
  have afterSuffixShape :
      gapBlockMarkers afterBlocks =
        renderGapBlocks (markerOnlyGapBlocks afterEntries) := by
    rw [
      SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.render_markerOnlyGapBlocks_eq_entryLabels]
    exact afterLabelsShape.symm
  have terminal :
      HullListDerives
        (renderGapBlocks (canonicalPriorGapBlocks beforeEntries) ++
          List.replicate
            (terminalExponentAfterPrior lastBlock data) lastBlock.marker ++
          displayedMarkerPairs pairMarkers ++
          retainedPriorDebt data ++ gapBlockMarkers afterBlocks)
        (renderGapBlocks (canonicalPriorGapBlocks beforeEntries) ++
          renderGapBlocks
            [lastDoubledGapBlock
              (collectParityDebt beforeEntries) lastEntry] ++
          renderGapBlocks (markerOnlyGapBlocks afterEntries)) := by
    simpa [terminalDatum, lastLabelAligned, retainedShape,
      afterSuffixShape, List.append_assoc] using terminalRaw
  exact swept.trans <| decomposed.trans <| folded.trans terminal

end Order6Hull23_1PhaseParityPowerNormalization
end CoRoots
end SemigroupBasis
