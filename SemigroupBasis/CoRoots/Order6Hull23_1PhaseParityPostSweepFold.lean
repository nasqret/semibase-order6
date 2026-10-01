import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityPostSweep

/-!
# Hull 23.1 post-sweep prior-power fold

This module contains only the recursive normalization of the gathered prior
powers.  Its source invariant deliberately retains the complete unprocessed
`priorDebtLabels rest`, while already processed undoubled debt is accumulated
in `retainedPriorDebt done`.  A doubled datum with a selected debt copy is the
only branch that consumes that copy and adds two copies to the terminal power.

The pair bank supplied to this fold must come from the corrected active
carrier decomposition, whose carrier is
`gapDebt lastBlock ++ sweptPriorDebt beforeBlocks`.  No swept-prior-only
carrier is asserted here.
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

/-! ## Pure shape helpers -/

private theorem renderCanonicalPriorData_append_singleton
    (done : List PriorPowerDatum) (datum : PriorPowerDatum) :
    renderGapBlocks
        (canonicalPriorGapBlocks
          (done.map (fun selected => selected.entry) ++
            [datum.entry])) =
      renderGapBlocks
          (canonicalPriorGapBlocks
            (done.map (fun selected => selected.entry))) ++
        renderGapBlocks [canonicalPriorGapBlock datum.entry] := by
  have blocksShape :
      canonicalPriorGapBlocks
          (done.map (fun selected => selected.entry) ++
            [datum.entry]) =
        canonicalPriorGapBlocks
            (done.map (fun selected => selected.entry)) ++
          [canonicalPriorGapBlock datum.entry] := by
    simp [canonicalPriorGapBlocks]
  rw [blocksShape]
  exact
    SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.renderGapBlocks_append
      _ _

private theorem replicate_eq_pred_one
    (terminal exponent : Nat) (positive : 0 < exponent) :
    List.replicate exponent terminal =
      List.replicate (exponent - 1) terminal ++ [terminal] := by
  have exponentShape : exponent = (exponent - 1) + 1 := by
    omega
  calc
    List.replicate exponent terminal =
        List.replicate ((exponent - 1) + 1) terminal := by
      exact congrArg (fun copies =>
        List.replicate copies terminal) exponentShape
    _ = List.replicate (exponent - 1) terminal ++
          List.replicate 1 terminal :=
      replicate_add_power (exponent - 1) 1 terminal
    _ = List.replicate (exponent - 1) terminal ++ [terminal] := by
      rfl

private theorem replicate_pred_one_append_three
    (terminal exponent : Nat) (positive : 0 < exponent) :
    List.replicate (exponent - 1) terminal ++
        [terminal, terminal, terminal] =
      List.replicate (exponent + 2) terminal := by
  have exponentShape : exponent + 2 = (exponent - 1) + 3 := by
    omega
  calc
    List.replicate (exponent - 1) terminal ++
          [terminal, terminal, terminal] =
        List.replicate (exponent - 1) terminal ++
          List.replicate 3 terminal := by
      rfl
    _ = List.replicate ((exponent - 1) + 3) terminal :=
      (replicate_add_power (exponent - 1) 3 terminal).symm
    _ = List.replicate (exponent + 2) terminal := by
      exact congrArg (fun copies =>
        List.replicate copies terminal) exponentShape.symm

private theorem replicate_pred_one_append_three_append
    (terminal exponent : Nat) (positive : 0 < exponent)
    (post : List Nat) :
    List.replicate (exponent - 1) terminal ++
        [terminal, terminal, terminal] ++ post =
      List.replicate (exponent + 2) terminal ++ post := by
  rw [replicate_pred_one_append_three terminal exponent positive]

/-! ## Recursive prior-power normalization -/

/-- Normalize the unprocessed prior powers from a left-to-right fold cut.

The current terminal exponent is explicit.  Every exceptional doubled datum
consumes its selected correction copy and increments this exponent by two;
undoubled selected copies instead move into the retained-debt accumulator.
The displayed pair bank is never reconstructed here and therefore remains
tied to the corrected active-carrier decomposition supplied by the caller. -/
theorem hullListDerivesNormalizePriorPowerDataFrom
    (done rest : List PriorPowerDatum)
    (pairMarkers suffix : List Nat)
    (terminal terminalExponent : Nat)
    (terminalPositive : 0 < terminalExponent)
    (pairSupport :
      forall marker, marker ∈ pairMarkers ->
        marker ∈
          (done ++ rest).map
            (fun datum => datum.entry.phase.label)) :
    HullListDerives
      (renderGapBlocks
          (canonicalPriorGapBlocks
            (done.map (fun datum => datum.entry))) ++
        renderPriorPowerData rest ++
        List.replicate terminalExponent terminal ++
        displayedMarkerPairs pairMarkers ++
        retainedPriorDebt done ++ priorDebtLabels rest ++ suffix)
      (renderGapBlocks
          (canonicalPriorGapBlocks
            ((done ++ rest).map (fun datum => datum.entry))) ++
        List.replicate
          (terminalExponent + 2 * exceptionalDebtCount rest) terminal ++
        displayedMarkerPairs pairMarkers ++
        retainedPriorDebt (done ++ rest) ++ suffix) := by
  induction rest generalizing done terminalExponent with
  | nil =>
      simpa [renderPriorPowerData, priorDebtLabels] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (renderGapBlocks
              (canonicalPriorGapBlocks
                (done.map (fun datum => datum.entry))) ++
            List.replicate terminalExponent terminal ++
            displayedMarkerPairs pairMarkers ++
            retainedPriorDebt done ++ suffix))
  | cons datum tail induction =>
      have nextPairSupport :
          forall marker, marker ∈ pairMarkers ->
            marker ∈
              ((done ++ [datum]) ++ tail).map
                (fun selected => selected.entry.phase.label) := by
        intro marker member
        simpa [List.append_assoc] using pairSupport marker member
      cases doubled : datum.entry.phase.doubled with
      | false =>
          cases debtBit : datum.debtBit with
          | false =>
              have headRaw :=
                hullListDerivesNormalizeUndoubledPriorPower
                  (renderGapBlocks
                    (canonicalPriorGapBlocks
                      (done.map (fun selected => selected.entry))))
                  (renderPriorPowerData tail ++
                    List.replicate terminalExponent terminal ++
                    displayedMarkerPairs pairMarkers ++
                    retainedPriorDebt done ++
                    priorDebtLabels (datum :: tail) ++ suffix)
                  datum doubled
              have headNormalized :
                  HullListDerives
                    (renderGapBlocks
                        (canonicalPriorGapBlocks
                          (done.map
                            (fun selected => selected.entry))) ++
                      renderPriorPowerData (datum :: tail) ++
                      List.replicate terminalExponent terminal ++
                      displayedMarkerPairs pairMarkers ++
                      retainedPriorDebt done ++
                      priorDebtLabels (datum :: tail) ++ suffix)
                    (renderGapBlocks
                        (canonicalPriorGapBlocks
                          (((done ++ [datum])).map
                            (fun selected => selected.entry))) ++
                      renderPriorPowerData tail ++
                      List.replicate terminalExponent terminal ++
                      displayedMarkerPairs pairMarkers ++
                      retainedPriorDebt (done ++ [datum]) ++
                      priorDebtLabels tail ++ suffix) := by
                simpa [renderPriorPowerData, priorDebtLabels,
                  retainedPriorDebt_append, retainedPriorDebt,
                  retainedPriorDebtContribution, doubled, debtBit,
                  renderCanonicalPriorData_append_singleton,
                  List.append_assoc] using headRaw
              have tailNormalized :=
                induction
                  (done := done ++ [datum])
                  (terminalExponent := terminalExponent)
                  terminalPositive nextPairSupport
              exact headNormalized.trans <| by
                simpa [exceptionalDebtCount, doubled, debtBit,
                  List.append_assoc] using tailNormalized
          | true =>
              have headRaw :=
                hullListDerivesNormalizeUndoubledPriorPower
                  (renderGapBlocks
                    (canonicalPriorGapBlocks
                      (done.map (fun selected => selected.entry))))
                  (renderPriorPowerData tail ++
                    List.replicate terminalExponent terminal ++
                    displayedMarkerPairs pairMarkers ++
                    retainedPriorDebt done ++
                    priorDebtLabels (datum :: tail) ++ suffix)
                  datum doubled
              have headNormalized :
                  HullListDerives
                    (renderGapBlocks
                        (canonicalPriorGapBlocks
                          (done.map
                            (fun selected => selected.entry))) ++
                      renderPriorPowerData (datum :: tail) ++
                      List.replicate terminalExponent terminal ++
                      displayedMarkerPairs pairMarkers ++
                      retainedPriorDebt done ++
                      priorDebtLabels (datum :: tail) ++ suffix)
                    (renderGapBlocks
                        (canonicalPriorGapBlocks
                          ((done ++ [datum]).map
                            (fun selected => selected.entry))) ++
                      renderPriorPowerData tail ++
                      List.replicate terminalExponent terminal ++
                      displayedMarkerPairs pairMarkers ++
                      retainedPriorDebt (done ++ [datum]) ++
                      priorDebtLabels tail ++ suffix) := by
                simpa [renderPriorPowerData, priorDebtLabels,
                  retainedPriorDebt_append, retainedPriorDebt,
                  retainedPriorDebtContribution, doubled, debtBit,
                  renderCanonicalPriorData_append_singleton,
                  List.append_assoc] using headRaw
              have tailNormalized :=
                induction
                  (done := done ++ [datum])
                  (terminalExponent := terminalExponent)
                  terminalPositive nextPairSupport
              exact headNormalized.trans <| by
                simpa [exceptionalDebtCount, doubled, debtBit,
                  List.append_assoc] using tailNormalized
      | true =>
          cases debtBit : datum.debtBit with
          | false =>
              have headRaw :=
                hullListDerivesNormalizeDoubledPriorPowerNoDebt
                  (renderGapBlocks
                    (canonicalPriorGapBlocks
                      (done.map (fun selected => selected.entry))))
                  (renderPriorPowerData tail ++
                    List.replicate terminalExponent terminal ++
                    displayedMarkerPairs pairMarkers ++
                    retainedPriorDebt done ++
                    priorDebtLabels (datum :: tail) ++ suffix)
                  datum doubled debtBit
              have headNormalized :
                  HullListDerives
                    (renderGapBlocks
                        (canonicalPriorGapBlocks
                          (done.map
                            (fun selected => selected.entry))) ++
                      renderPriorPowerData (datum :: tail) ++
                      List.replicate terminalExponent terminal ++
                      displayedMarkerPairs pairMarkers ++
                      retainedPriorDebt done ++
                      priorDebtLabels (datum :: tail) ++ suffix)
                    (renderGapBlocks
                        (canonicalPriorGapBlocks
                          ((done ++ [datum]).map
                            (fun selected => selected.entry))) ++
                      renderPriorPowerData tail ++
                      List.replicate terminalExponent terminal ++
                      displayedMarkerPairs pairMarkers ++
                      retainedPriorDebt (done ++ [datum]) ++
                      priorDebtLabels tail ++ suffix) := by
                simpa [renderPriorPowerData, priorDebtLabels,
                  retainedPriorDebt_append, retainedPriorDebt,
                  retainedPriorDebtContribution, doubled, debtBit,
                  renderCanonicalPriorData_append_singleton,
                  List.append_assoc] using headRaw
              have tailNormalized :=
                induction
                  (done := done ++ [datum])
                  (terminalExponent := terminalExponent)
                  terminalPositive nextPairSupport
              exact headNormalized.trans <| by
                simpa [exceptionalDebtCount, doubled, debtBit,
                  List.append_assoc] using tailNormalized
          | true =>
              let stable :=
                renderGapBlocks
                  (canonicalPriorGapBlocks
                    (done.map (fun selected => selected.entry)))
              let tailStem :=
                renderPriorPowerData tail ++
                  List.replicate (terminalExponent - 1) terminal
              let frontDebt :=
                displayedMarkerPairs pairMarkers ++
                  retainedPriorDebt done
              have labelSeen :
                  forall letter,
                    letter ∈
                        (done ++ datum :: tail).map
                          (fun selected =>
                            selected.entry.phase.label) ->
                      letter ∈
                        stable ++ renderPriorPowerData (datum :: tail) := by
                intro letter support
                obtain ⟨selected, selectedMember, labelEqual⟩ :=
                  List.mem_map.mp support
                have seen :=
                  datumLabels_seen_in_foldPrefix
                    done (datum :: tail) selected selectedMember
                simpa [stable, labelEqual] using seen
              have frontDebtSeen :
                  forall letter, letter ∈ frontDebt ->
                    letter ∈
                      stable ++ renderPriorPowerDatum datum ++
                        (tailStem ++ [terminal]) := by
                intro letter member
                have seenAtCut :
                    letter ∈
                      stable ++ renderPriorPowerData (datum :: tail) := by
                  change letter ∈
                    displayedMarkerPairs pairMarkers ++
                      retainedPriorDebt done at member
                  rcases List.mem_append.mp member with
                    inPairs | inRetained
                  · have markerMember : letter ∈ pairMarkers :=
                      (mem_displayedMarkerPairs_iff
                        letter pairMarkers).mp inPairs
                    exact labelSeen letter <|
                      pairSupport letter markerMember
                  · have retainedSupport :=
                      retainedPriorDebt_support
                        done letter inRetained
                    have totalSupport :
                        letter ∈
                          (done ++ datum :: tail).map
                            (fun selected =>
                              selected.entry.phase.label) := by
                      rw [List.map_append]
                      exact List.mem_append.mpr <|
                        Or.inl retainedSupport
                    exact labelSeen letter totalSupport
                have withStem :
                    letter ∈
                      (stable ++ renderPriorPowerData (datum :: tail)) ++
                        List.replicate
                          (terminalExponent - 1) terminal :=
                  List.mem_append.mpr <| Or.inl seenAtCut
                have withTerminal :
                    letter ∈
                      ((stable ++ renderPriorPowerData
                          (datum :: tail)) ++
                        List.replicate
                          (terminalExponent - 1) terminal) ++
                        [terminal] :=
                  List.mem_append.mpr <| Or.inl withStem
                simpa [stable, tailStem, renderPriorPowerData,
                  List.append_assoc] using withTerminal
              obtain ⟨result, resultParity, exceptionalRaw⟩ :=
                hullListDerivesExceptionalPriorPowerWithTail
                  stable (priorDebtLabels tail ++ suffix)
                  frontDebt tailStem datum terminal
                  doubled debtBit frontDebtSeen
              have resultShape :=
                renderConditionIVActivePower_eq_canonicalPrior
                  datum result doubled resultParity
              have terminalSplit :=
                replicate_eq_pred_one
                  terminal terminalExponent terminalPositive
              have terminalGrowthContext :=
                replicate_pred_one_append_three_append
                  terminal terminalExponent terminalPositive
                  (frontDebt ++ priorDebtLabels tail ++ suffix)
              have exceptionalTargetGrowth :
                  stable ++
                      renderConditionIVActivePower
                        result datum.entry.phase.label ++
                      tailStem ++ [terminal, terminal, terminal] ++
                      frontDebt ++ (priorDebtLabels tail ++ suffix) =
                    stable ++
                      renderConditionIVActivePower
                        result datum.entry.phase.label ++
                      renderPriorPowerData tail ++
                      List.replicate
                        (terminalExponent + 2) terminal ++
                      frontDebt ++ (priorDebtLabels tail ++ suffix) := by
                have lifted :=
                  congrArg
                    (fun terminalTail =>
                      stable ++
                        renderConditionIVActivePower
                          result datum.entry.phase.label ++
                        renderPriorPowerData tail ++ terminalTail)
                    terminalGrowthContext
                simpa [tailStem, List.append_assoc] using lifted
              rw [exceptionalTargetGrowth] at exceptionalRaw
              have headNormalized :
                  HullListDerives
                    (renderGapBlocks
                        (canonicalPriorGapBlocks
                          (done.map
                            (fun selected => selected.entry))) ++
                      renderPriorPowerData (datum :: tail) ++
                      List.replicate terminalExponent terminal ++
                      displayedMarkerPairs pairMarkers ++
                      retainedPriorDebt done ++
                      priorDebtLabels (datum :: tail) ++ suffix)
                    (renderGapBlocks
                        (canonicalPriorGapBlocks
                          ((done ++ [datum]).map
                            (fun selected => selected.entry))) ++
                      renderPriorPowerData tail ++
                      List.replicate
                        (terminalExponent + 2) terminal ++
                      displayedMarkerPairs pairMarkers ++
                      retainedPriorDebt (done ++ [datum]) ++
                      priorDebtLabels tail ++ suffix) := by
                simpa [stable, tailStem, frontDebt,
                  renderPriorPowerData, priorDebtLabels,
                  retainedPriorDebt_append, retainedPriorDebt,
                  retainedPriorDebtContribution, doubled, debtBit,
                  renderCanonicalPriorData_append_singleton,
                  resultShape, terminalSplit,
                  List.append_assoc] using exceptionalRaw
              have tailNormalized :=
                induction
                  (done := done ++ [datum])
                  (terminalExponent := terminalExponent + 2)
                  (by omega) nextPairSupport
              have exponentShape :
                  (terminalExponent + 2) +
                      2 * exceptionalDebtCount tail =
                    terminalExponent +
                      2 * exceptionalDebtCount (datum :: tail) := by
                simp [exceptionalDebtCount, doubled, debtBit] <;> omega
              exact headNormalized.trans <| by
                simpa [exponentShape, List.append_assoc] using
                  tailNormalized

/-! ## Initial-cut specialization -/

/-- Normalize all gathered prior powers from the empty processed prefix.
The support premise is stated in the raw rendering form returned by the exact
active-carrier pair builder. -/
theorem hullListDerivesNormalizePriorPowerData
    (data : List PriorPowerDatum)
    (pairMarkers suffix : List Nat)
    (terminal terminalExponent : Nat)
    (terminalPositive : 0 < terminalExponent)
    (pairSupport :
      forall marker, marker ∈ pairMarkers ->
        marker ∈ renderPriorPowerData data) :
    HullListDerives
      (renderPriorPowerData data ++
        List.replicate terminalExponent terminal ++
        displayedMarkerPairs pairMarkers ++
        priorDebtLabels data ++ suffix)
      (renderGapBlocks
          (canonicalPriorGapBlocks
            (data.map (fun datum => datum.entry))) ++
        List.replicate
          (terminalExponent + 2 * exceptionalDebtCount data) terminal ++
        displayedMarkerPairs pairMarkers ++
        retainedPriorDebt data ++ suffix) := by
  have pairLabelSupport :
      forall marker, marker ∈ pairMarkers ->
        marker ∈
          ([] ++ data).map
            (fun datum : PriorPowerDatum =>
              datum.entry.phase.label) := by
    intro marker member
    simpa using
      renderPriorPowerData_label_support
        (pairSupport marker member)
  simpa [renderPriorPowerData, priorDebtLabels] using
    hullListDerivesNormalizePriorPowerDataFrom
      [] data pairMarkers suffix terminal terminalExponent
      terminalPositive pairLabelSupport

end Order6Hull23_1PhaseParityPowerNormalization
end CoRoots
end SemigroupBasis
