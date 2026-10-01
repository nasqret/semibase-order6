import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityPowerNormalization

/-!
# Hull 23.1 post-sweep endpoint foundations

This module isolates the bookkeeping and terminal endpoint operations needed
after the corrected active-debt carrier has been decomposed.  It deliberately
does not contain the recursive prior-power fold or the final last-doubled
skeleton theorem.

The active carrier remains
`gapDebt lastBlock ++ sweptPriorDebt beforeBlocks`; in particular, none of the
definitions below reintroduces the falsified swept-prior-only carrier.
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

/-! ## Prior exceptional count and retained debt -/

/-- Number of doubled prior data whose selected debt copy is absorbed by the
Condition-IV exceptional repair.  Each such repair contributes two copies to
the final terminal exponent. -/
def exceptionalDebtCount : List PriorPowerDatum -> Nat
  | [] => 0
  | datum :: rest =>
      (if datum.entry.phase.doubled && datum.debtBit then 1 else 0) +
        exceptionalDebtCount rest

/-- A prior singleton is retained precisely for an undoubled datum whose
stored correction bit is set. -/
def retainedPriorDebtContribution
    (datum : PriorPowerDatum) : List Nat :=
  if datum.entry.phase.doubled then
    []
  else if datum.debtBit then
    [datum.entry.phase.label]
  else
    []

/-- Retained undoubled singleton debt, in original datum order. -/
def retainedPriorDebt : List PriorPowerDatum -> List Nat
  | [] => []
  | datum :: rest =>
      retainedPriorDebtContribution datum ++ retainedPriorDebt rest

theorem exceptionalDebtCount_append
    (left right : List PriorPowerDatum) :
    exceptionalDebtCount (left ++ right) =
      exceptionalDebtCount left + exceptionalDebtCount right := by
  induction left with
  | nil =>
      simp [exceptionalDebtCount]
  | cons datum rest induction =>
      simp only [List.cons_append, exceptionalDebtCount]
      rw [induction]
      omega

theorem retainedPriorDebt_append
    (left right : List PriorPowerDatum) :
    retainedPriorDebt (left ++ right) =
      retainedPriorDebt left ++ retainedPriorDebt right := by
  induction left with
  | nil =>
      rfl
  | cons datum rest induction =>
      simp only [List.cons_append, retainedPriorDebt]
      rw [induction, List.append_assoc]

/-- The retained bit selected from one datum is exactly the published parity
debt contribution of its entry. -/
theorem retainedPriorDebtContribution_eq_parityDebtContribution
    (datum : PriorPowerDatum) :
    retainedPriorDebtContribution datum =
      parityDebtContribution datum.entry := by
  cases doubled : datum.entry.phase.doubled with
  | true =>
      simp [retainedPriorDebtContribution,
        parityDebtContribution, doubled]
  | false =>
      have exponentOne := datum.undoubled_eq_one doubled
      have parityEquation := datum.parity_eq
      cases debtBit : datum.debtBit with
      | false =>
          have odd : datum.entry.parity % 2 = 1 := by
            simpa [debtBit, exponentOne] using parityEquation.symm
          simp [retainedPriorDebtContribution,
            parityDebtContribution, doubled, debtBit, odd]
      | true =>
          have even : datum.entry.parity % 2 = 0 := by
            simpa [debtBit, exponentOne] using parityEquation.symm
          simp [retainedPriorDebtContribution,
            parityDebtContribution, doubled, debtBit, even]

theorem retainedPriorDebt_eq_collectParityDebt_map :
    forall data : List PriorPowerDatum,
      retainedPriorDebt data =
        collectParityDebt (data.map (fun datum => datum.entry))
  | [] => rfl
  | datum :: rest => by
      simp only [retainedPriorDebt, List.map_cons, collectParityDebt]
      rw [retainedPriorDebtContribution_eq_parityDebtContribution,
        retainedPriorDebt_eq_collectParityDebt_map rest]

/-- Retained debt is the literal published parity debt after replacing data
by its aligned entry list. -/
theorem retainedPriorDebt_eq_collectParityDebt
    (data : List PriorPowerDatum) (entries : List PhaseParityEntry)
    (dataEntries : data.map (fun datum => datum.entry) = entries) :
    retainedPriorDebt data = collectParityDebt entries := by
  rw [← dataEntries]
  exact retainedPriorDebt_eq_collectParityDebt_map data

/-! ## Support needed by the prior fold -/

theorem mem_displayedMarkerPairs_iff
    (letter : Nat) :
    forall markers : List Nat,
      letter ∈ displayedMarkerPairs markers ↔ letter ∈ markers
  | [] => by
      simp [displayedMarkerPairs]
  | marker :: rest => by
      simp [displayedMarkerPairs,
        mem_displayedMarkerPairs_iff letter rest]

/-- Every retained singleton is labelled by one of its source data. -/
theorem retainedPriorDebt_support
    (data : List PriorPowerDatum) :
    forall letter, letter ∈ retainedPriorDebt data ->
      letter ∈ data.map (fun datum => datum.entry.phase.label) := by
  induction data with
  | nil =>
      simp [retainedPriorDebt]
  | cons datum rest induction =>
      intro letter member
      cases doubled : datum.entry.phase.doubled with
      | true =>
          have inRest : letter ∈ retainedPriorDebt rest := by
            simpa [retainedPriorDebt,
              retainedPriorDebtContribution, doubled] using member
          exact List.Mem.tail _ <| induction letter inRest
      | false =>
          cases debtBit : datum.debtBit with
          | false =>
              have inRest : letter ∈ retainedPriorDebt rest := by
                simpa [retainedPriorDebt,
                  retainedPriorDebtContribution, doubled,
                  debtBit] using member
              exact List.Mem.tail _ <| induction letter inRest
          | true =>
              have selected :
                  letter = datum.entry.phase.label ∨
                    letter ∈ retainedPriorDebt rest := by
                simpa [retainedPriorDebt,
                  retainedPriorDebtContribution, doubled,
                  debtBit] using member
              rcases selected with atHead | inRest
              · subst letter
                simp
              · exact List.Mem.tail _ <| induction letter inRest

/-- Every datum marker has a literal occurrence in the gathered raw-power
rendering. -/
private theorem postSweep_mem_replicate_self_of_pos
    (letter copies : Nat) (positive : 0 < copies) :
    letter ∈ List.replicate copies letter := by
  cases copies with
  | zero =>
      simp at positive
  | succ rest =>
      simp [List.replicate_succ]

theorem priorPowerData_labels_seen
    (data : List PriorPowerDatum) :
    forall datum, datum ∈ data ->
      datum.entry.phase.label ∈ renderPriorPowerData data := by
  induction data with
  | nil =>
      simp
  | cons head rest induction =>
      intro datum member
      rcases List.mem_cons.mp member with atHead | inRest
      · subst datum
        have inPower :
            head.entry.phase.label ∈ renderPriorPowerDatum head := by
          rw [renderPriorPowerDatum]
          exact postSweep_mem_replicate_self_of_pos
            head.entry.phase.label head.exponent head.exponent_pos
        simpa only [renderPriorPowerData] using
          (List.mem_append.mpr <| Or.inl inPower)
      · simpa only [renderPriorPowerData] using
          (List.mem_append.mpr <| Or.inr <|
            induction datum inRest)

/-- At every left-to-right fold cut, each datum label is witnessed either in
the already canonicalized prefix or in the still-raw power suffix. -/
theorem datumLabels_seen_in_foldPrefix
    (done rest : List PriorPowerDatum) :
    forall datum, datum ∈ done ++ rest ->
      datum.entry.phase.label ∈
        renderGapBlocks
            (canonicalPriorGapBlocks
              (done.map (fun selected => selected.entry))) ++
          renderPriorPowerData rest := by
  intro datum member
  rcases List.mem_append.mp member with inDone | inRest
  · apply List.mem_append.mpr
    apply Or.inl
    rw [
      SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.mem_render_canonicalPriorGapBlocks_iff]
    exact
      ⟨datum.entry,
        List.mem_map.mpr ⟨datum, inDone, rfl⟩, rfl⟩
  · exact List.mem_append.mpr <| Or.inr <|
      priorPowerData_labels_seen rest datum inRest

/-! ## Canonical exceptional endpoint -/

/-- The parity-selected square or cube returned by Condition IV is literally
the canonical prior block of the repaired doubled datum. -/
theorem renderConditionIVActivePower_eq_canonicalPrior
    (datum : PriorPowerDatum) (result : ConditionIVActiveResult)
    (doubled : datum.entry.phase.doubled = true)
    (resultParity :
      (renderConditionIVActivePower
          result datum.entry.phase.label).count
            datum.entry.phase.label % 2 =
        datum.entry.parity % 2) :
    renderConditionIVActivePower result datum.entry.phase.label =
      renderGapBlocks [canonicalPriorGapBlock datum.entry] := by
  cases result with
  | square =>
      have even : datum.entry.parity % 2 = 0 := by
        simpa [renderConditionIVActivePower] using resultParity.symm
      simp [renderConditionIVActivePower, canonicalPriorGapBlock,
        priorDoubledGapBlock, renderGapBlocks, doubled, even]
  | cube =>
      have odd : datum.entry.parity % 2 = 1 := by
        simpa [renderConditionIVActivePower] using resultParity.symm
      simp [renderConditionIVActivePower, canonicalPriorGapBlock,
        priorDoubledGapBlock, renderGapBlocks, doubled, odd]

/-! ## Exact final-marker exponent -/

/-- Final-marker exponent after the selected gap itself has been swept and
its exposed terminal square retained. -/
def selectedTerminalExponent (lastBlock : GapBlock) : Nat :=
  (lastBlock.seconds.length + 1) + 2 + (gapDebt lastBlock).length

/-- Final-marker exponent after all exceptional prior singleton absorptions. -/
def terminalExponentAfterPrior
    (lastBlock : GapBlock) (data : List PriorPowerDatum) : Nat :=
  selectedTerminalExponent lastBlock + 2 * exceptionalDebtCount data

/-- The exact terminal exponent has the source parity stored by the selected
last entry. -/
theorem terminalExponentAfterPrior_parity
    (word : Word Nat)
    {beforeBlocks afterBlocks : List GapBlock} {lastBlock : GapBlock}
    {beforeEntries afterEntries : List PhaseParityEntry}
    {lastEntry : PhaseParityEntry}
    (data : List PriorPowerDatum)
    (sourceSplit :
      gapBlocksList word.toList =
        beforeBlocks ++ lastBlock :: afterBlocks)
    (afterEmpty :
      forall block, block ∈ afterBlocks -> block.seconds = [])
    (entrySplit :
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        beforeEntries ++ lastEntry :: afterEntries)
    (lastAligned : lastEntry.phase = phaseOfGapBlock lastBlock) :
    terminalExponentAfterPrior lastBlock data % 2 =
      lastEntry.parity % 2 := by
  have formed :
      GapBlocksWellFormed []
        (beforeBlocks ++ lastBlock :: afterBlocks) := by
    rw [← sourceSplit]
    exact gapBlocksList_wellFormed word.toList
  have beforeFormed : GapBlocksWellFormed [] beforeBlocks :=
    (gapBlocksWellFormed_append formed).1
  have markerSplitNodup :
      (gapBlockMarkers beforeBlocks ++
        lastBlock.marker :: gapBlockMarkers afterBlocks).Nodup := by
    simpa [gapBlockMarkers] using formed.markersNodup
  have markerSplit := List.nodup_append.mp markerSplitNodup
  have lastNotBefore : lastBlock.marker ∉ gapBlockMarkers beforeBlocks := by
    intro member
    exact markerSplit.2.2
      lastBlock.marker member lastBlock.marker
      (List.Mem.head (gapBlockMarkers afterBlocks)) rfl
  have tailNodup :
      (lastBlock.marker :: gapBlockMarkers afterBlocks).Nodup :=
    markerSplit.2.1
  have lastNotAfter : lastBlock.marker ∉ gapBlockMarkers afterBlocks :=
    (List.nodup_cons.mp tailNodup).1
  have beforeRenderedAbsent :
      lastBlock.marker ∉ renderGapBlocks beforeBlocks :=
    not_mem_renderGapBlocks_of_not_mem_markers
      beforeFormed lastNotBefore
  have beforeRenderedCountZero :
      (renderGapBlocks beforeBlocks).count lastBlock.marker = 0 :=
    List.count_eq_zero.mpr beforeRenderedAbsent
  have afterRenderedCountZero :
      (renderGapBlocks afterBlocks).count lastBlock.marker = 0 := by
    rw [
      SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.renderGapBlocks_eq_markers_of_seconds_empty
        afterBlocks afterEmpty]
    exact List.count_eq_zero.mpr lastNotAfter
  have sourceRender :
      word.toList =
        renderGapBlocks beforeBlocks ++ [lastBlock.marker] ++
          lastBlock.seconds ++ renderGapBlocks afterBlocks := by
    calc
      word.toList = renderGapBlocks (gapBlocksList word.toList) :=
        (render_gapBlocksList word.toList).symm
      _ = renderGapBlocks
          (beforeBlocks ++ lastBlock :: afterBlocks) := by
        rw [sourceSplit]
      _ = renderGapBlocks beforeBlocks ++ [lastBlock.marker] ++
          lastBlock.seconds ++ renderGapBlocks afterBlocks := by
        rw [
          SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.renderGapBlocks_append]
        simp [renderGapBlocks, List.append_assoc]
  have sourceCount :
      word.toList.count lastBlock.marker =
        lastBlock.seconds.count lastBlock.marker + 1 := by
    rw [sourceRender]
    simp only [List.count_append]
    rw [beforeRenderedCountZero, afterRenderedCountZero]
    simp
    omega
  have lastEntryMember :
      lastEntry ∈
        phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) := by
    rw [entrySplit]
    exact List.mem_append.mpr <| Or.inr <|
      List.Mem.head afterEntries
  have labelAligned : lastEntry.phase.label = lastBlock.marker := by
    simpa [phaseOfGapBlock] using congrArg Phase.label lastAligned
  have storedParity :=
    phaseParityEntry_parity_eq_source_count word lastEntryMember
  rw [labelAligned, sourceCount] at storedParity
  have gapAccounting := gapMarkerCount_add_debtLength lastBlock
  simp only [terminalExponentAfterPrior, selectedTerminalExponent]
  omega

theorem terminalExponentAfterPrior_ge_four
    (lastBlock : GapBlock) (data : List PriorPowerDatum)
    (lastNonempty : lastBlock.seconds ≠ []) :
    4 <= terminalExponentAfterPrior lastBlock data := by
  have positive : 0 < lastBlock.seconds.length :=
    List.length_pos_iff.mpr lastNonempty
  simp only [terminalExponentAfterPrior, selectedTerminalExponent]
  omega

/-! ## Pair placement and terminal normalization -/

theorem replicate_eq_pred_three
    (terminal exponent : Nat) (atLeastThree : 3 <= exponent) :
    List.replicate exponent terminal =
      List.replicate (exponent - 3) terminal ++
        [terminal, terminal, terminal] := by
  have exponentShape : exponent = (exponent - 3) + 3 := by
    omega
  calc
    List.replicate exponent terminal =
        List.replicate ((exponent - 3) + 3) terminal := by
      exact congrArg (fun copies =>
        List.replicate copies terminal) exponentShape
    _ = List.replicate (exponent - 3) terminal ++
          List.replicate 3 terminal :=
      replicate_add_power (exponent - 3) 3 terminal
    _ = List.replicate (exponent - 3) terminal ++
          [terminal, terminal, terminal] := by
      rfl

/-- Move all displayed prior-debt pairs across a terminal power of exponent
at least three.  The terminal cube is preserved, so the operation removes
the pairs without changing the displayed exponent. -/
theorem hullListDerivesTransferPairsAcrossTerminalPower
    (pre suffix pairMarkers debt : List Nat)
    (terminal exponent : Nat) (atLeastThree : 3 <= exponent)
    (markersSeen :
      forall marker, marker ∈ pairMarkers -> marker ∈ pre) :
    HullListDerives
      (pre ++ List.replicate exponent terminal ++
        displayedMarkerPairs pairMarkers ++ debt ++ suffix)
      (pre ++ List.replicate exponent terminal ++ debt ++ suffix) := by
  let stem := pre ++ List.replicate (exponent - 3) terminal
  let witnesses := stem ++ [terminal]
  have sourceSeen :
      forall letter,
        letter ∈ [terminal, terminal] ++
            displayedMarkerPairs pairMarkers ->
          letter ∈ witnesses := by
    intro letter member
    rcases List.mem_append.mp member with atTerminal | inPairs
    · have equal : letter = terminal := by
        simpa using atTerminal
      subst letter
      simp [witnesses]
    · have markerMember : letter ∈ pairMarkers :=
        (mem_displayedMarkerPairs_iff letter pairMarkers).mp inPairs
      have inPre := markersSeen letter markerMember
      simp [witnesses, stem, inPre]
  have placedRaw :=
    SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityDebtMoves.hullListDerivesWitnessedTailPermutation
      witnesses (debt ++ suffix) sourceSeen
      (List.perm_append_comm
        (l₁ := [terminal, terminal])
        (l₂ := displayedMarkerPairs pairMarkers))
  have powerShape :=
    replicate_eq_pred_three terminal exponent atLeastThree
  have placed :
      HullListDerives
        (pre ++ List.replicate exponent terminal ++
          displayedMarkerPairs pairMarkers ++ debt ++ suffix)
        (stem ++ [terminal] ++ displayedMarkerPairs pairMarkers ++
          [terminal, terminal] ++ debt ++ suffix) := by
    rw [powerShape]
    simpa [stem, witnesses, List.append_assoc] using placedRaw
  have stemMarkersSeen :
      forall marker, marker ∈ pairMarkers -> marker ∈ stem := by
    intro marker member
    exact List.mem_append.mpr <| Or.inl <|
      markersSeen marker member
  have transferred :=
    hullListDerivesTransferDebtPairsToTerminalCube
      stem suffix pairMarkers debt terminal stemMarkersSeen
  have transferredAligned :
      HullListDerives
        (stem ++ [terminal] ++ displayedMarkerPairs pairMarkers ++
          [terminal, terminal] ++ debt ++ suffix)
        (pre ++ List.replicate exponent terminal ++ debt ++ suffix) := by
    rw [powerShape]
    simpa [stem, List.append_assoc] using transferred
  exact placed.trans transferredAligned

/-- Transfer all prior-debt pairs into the terminal power, then apply the
existing exact terminal-power normalizer. -/
theorem hullListDerivesTransferPairsAndNormalizeTerminal
    (pre suffix pairMarkers : List Nat) (datum : TerminalPowerDatum)
    (atLeastThree : 3 <= datum.exponent)
    (markersSeen :
      forall marker, marker ∈ pairMarkers -> marker ∈ pre)
    (debtSeen :
      forall letter, letter ∈ datum.debt -> letter ∈ pre) :
    HullListDerives
      (pre ++ List.replicate datum.exponent
          datum.entry.phase.label ++
        displayedMarkerPairs pairMarkers ++ datum.debt ++ suffix)
      (pre ++
        renderGapBlocks
          [lastDoubledGapBlock datum.debt datum.entry] ++ suffix) := by
  have pairsRemoved :=
    hullListDerivesTransferPairsAcrossTerminalPower
      pre suffix pairMarkers datum.debt datum.entry.phase.label
      datum.exponent atLeastThree markersSeen
  have normalized :=
    hullListDerivesNormalizeTerminalPower
      pre suffix datum debtSeen
  exact pairsRemoved.trans <| by
    simpa [renderTerminalPowerDatum, List.append_assoc] using normalized

end Order6Hull23_1PhaseParityPowerNormalization
end CoRoots
end SemigroupBasis
