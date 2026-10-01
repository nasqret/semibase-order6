import SemigroupBasis.CoRoots.Order6SporadicSection14CanonicalBlocks

namespace SemigroupBasis.CoRoots.Order6SporadicSection14

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_870
open SemigroupBasis.Examples

private theorem gapBlock_eq
    (left right : FirstOccurrenceGapBlock)
    (marker : left.marker = right.marker)
    (seconds : left.seconds = right.seconds) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem choice_members
    {allowed seconds : List Nat}
    (choice : ChoiceIn allowed seconds) :
    forall letter, letter ∈ seconds -> letter ∈ allowed := by
  intro letter member
  rcases choice with empty | ⟨selected, selectedAllowed, shape⟩
  · simp [empty] at member
  · rw [shape] at member
    have letterEq : letter = selected := by
      simpa only [List.mem_singleton] using member
    subst letter
    exact selectedAllowed

private theorem final_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).final = final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

private theorem final_eq_of_toList_eq
    (word : Word Nat) (stem : List Nat) (final : Nat)
    (shape : word.toList = stem ++ [final]) :
    word.final = final := by
  have wordEq : word = wordOfPrefixFinal stem final := by
    apply Word.toList_injective
    simpa [toList_wordOfPrefixFinal] using shape
  rw [wordEq]
  exact final_wordOfPrefixFinal stem final

private theorem selected_gap_contradiction
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    (left right : Word Nat)
    (before : List Nat) (current selected nextMarker : Nat)
    (leftSuffix rightGap rightSuffix : List Nat)
    (leftShape :
      left.toList =
        before ++ [current, selected, nextMarker] ++ leftSuffix)
    (rightShape :
      right.toList =
        before ++ [current] ++ rightGap ++
          (nextMarker :: rightSuffix))
    (selectedNeNext : selected ≠ nextMarker)
    (currentNeSelected : current ≠ selected)
    (currentNeNext : current ≠ nextMarker)
    (beforeNoNext :
      forall letter, letter ∈ before -> letter ≠ nextMarker)
    (rightGapOrdinary : forall letter, letter ∈ rightGap ->
      letter ≠ selected ∧ letter ≠ nextMarker)
    (valid : (Identity.mk left right).SatisfiedBy candidate) : False := by
  have evaluated :=
    valid (separator.valuation selected nextMarker)
  rw [separator.eval_selected_gap left before current selected
      nextMarker leftSuffix leftShape selectedNeNext currentNeSelected
      currentNeNext beforeNoNext,
    separator.eval_ordinary_gap right before rightGap current selected
      nextMarker rightSuffix rightShape selectedNeNext currentNeSelected
      currentNeNext beforeNoNext rightGapOrdinary] at evaluated
  exact separator.hit_ne_miss evaluated

private theorem CleanBlocks.headFresh
    {seen : List Nat} {block : FirstOccurrenceGapBlock}
    {rest : List FirstOccurrenceGapBlock}
    (normal : CleanBlocks seen (block :: rest)) :
    block.marker ∉ seen := by
  cases normal with
  | cons _ _ _ fresh _ _ => exact fresh

private theorem AlphaBlocks.headFresh
    {seen : List Nat} {block : FirstOccurrenceGapBlock}
    {rest : List FirstOccurrenceGapBlock}
    (normal : AlphaBlocks seen (block :: rest)) :
    block.marker ∉ seen := by
  cases normal with
  | last _ _ fresh _ => exact fresh
  | cons _ _ _ _ fresh _ _ => exact fresh

private theorem extend_before_seen
    {seen before seconds : List Nat} {marker : Nat}
    (beforeSeen : forall letter, letter ∈ before -> letter ∈ seen)
    (secondsSeen : forall letter, letter ∈ seconds -> letter ∈ seen) :
    forall letter,
      letter ∈ before ++ [marker] ++ seconds ->
        letter ∈ marker :: seen := by
  intro letter member
  rcases List.mem_append.mp member with inBeforeMarker | inSeconds
  · rcases List.mem_append.mp inBeforeMarker with inBefore | atMarker
    · exact List.Mem.tail marker (beforeSeen letter inBefore)
    · have letterEq : letter = marker := by
        simpa only [List.mem_singleton] using atMarker
      subst letter
      exact List.Mem.head seen
  · exact List.Mem.tail marker (secondsSeen letter inSeconds)

set_option maxHeartbeats 2000000 in
private theorem cleanBlocks_eq_of_valid
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    (leftWord rightWord : Word Nat)
    {seen before : List Nat}
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (leftNormal : CleanBlocks seen leftBlocks)
    (rightNormal : CleanBlocks seen rightBlocks)
    (markers :
      gapBlockMarkers leftBlocks = gapBlockMarkers rightBlocks)
    (leftList :
      leftWord.toList = before ++ renderGapBlocks leftBlocks)
    (rightList :
      rightWord.toList = before ++ renderGapBlocks rightBlocks)
    (beforeSeen : forall letter, letter ∈ before -> letter ∈ seen)
    (valid :
      (Identity.mk leftWord rightWord).SatisfiedBy candidate)
    (finalEq : leftWord.final = rightWord.final) :
    leftBlocks = rightBlocks := by
  cases leftNormal with
  | nil seen =>
      cases rightNormal with
      | nil => rfl
      | cons _ block rest fresh choice tail =>
          simp [gapBlockMarkers] at markers
  | cons seen leftBlock leftRest leftFresh leftChoice leftTail =>
      cases rightNormal with
      | nil =>
          simp [gapBlockMarkers] at markers
      | cons _ rightBlock rightRest rightFresh rightChoice rightTail =>
          simp only [gapBlockMarkers, List.map_cons,
            FirstOccurrenceGapBlock.marker] at markers
          have markerEq : leftBlock.marker = rightBlock.marker := by
            exact (List.cons.inj markers).1
          have tailMarkers :
              gapBlockMarkers leftRest = gapBlockMarkers rightRest := by
            exact (List.cons.inj markers).2
          have secondsEq : leftBlock.seconds = rightBlock.seconds := by
            rcases leftChoice with leftEmpty |
              ⟨leftSelected, leftSelectedSeen, leftSeconds⟩
            · rcases rightChoice with rightEmpty |
                ⟨rightSelected, rightSelectedSeen, rightSeconds⟩
              · exact leftEmpty.trans rightEmpty.symm
              · cases leftRest with
                | nil =>
                    cases rightRest with
                    | nil =>
                        have leftFinal :
                            leftWord.final = leftBlock.marker := by
                          apply final_eq_of_toList_eq leftWord before
                            leftBlock.marker
                          simpa [renderGapBlocks, leftEmpty,
                            List.append_assoc] using leftList
                        have rightFinal :
                            rightWord.final = rightSelected := by
                          apply final_eq_of_toList_eq rightWord
                            (before ++ [rightBlock.marker]) rightSelected
                          simpa [renderGapBlocks, rightSeconds,
                            List.append_assoc] using rightList
                        have selectedEq :
                            rightSelected = leftBlock.marker :=
                          rightFinal.symm.trans
                            (finalEq.symm.trans leftFinal)
                        have rightSelectedNe :
                            rightSelected ≠ rightBlock.marker := by
                          intro equal
                          exact rightFresh <| by
                            rw [← equal]
                            exact rightSelectedSeen
                        exact False.elim <|
                          rightSelectedNe (selectedEq.trans markerEq)
                    | cons rightNext rightRemaining =>
                        simp [gapBlockMarkers] at tailMarkers
                | cons leftNext leftRemaining =>
                    cases rightRest with
                    | nil =>
                        simp [gapBlockMarkers] at tailMarkers
                    | cons rightNext rightRemaining =>
                        have nextMarkerEq :
                            leftNext.marker = rightNext.marker := by
                          simpa [gapBlockMarkers] using
                            congrArg List.head? tailMarkers
                        have nextFresh := leftTail.headFresh
                        have rightSelectedNeNext :
                            rightSelected ≠ leftNext.marker := by
                          intro equal
                          exact nextFresh <| by
                            rw [← equal]
                            exact List.Mem.tail leftBlock.marker
                              rightSelectedSeen
                        have currentNeSelected :
                            leftBlock.marker ≠ rightSelected := by
                          intro equal
                          exact rightFresh <| by
                            rw [← markerEq, equal]
                            exact rightSelectedSeen
                        have currentNeNext :
                            leftBlock.marker ≠ leftNext.marker := by
                          intro equal
                          exact nextFresh <| by simp [← equal]
                        have beforeNoNext :
                            forall letter, letter ∈ before ->
                              letter ≠ leftNext.marker := by
                          intro letter member equal
                          exact nextFresh <| by
                            rw [← equal]
                            exact List.Mem.tail leftBlock.marker
                              (beforeSeen letter member)
                        have rightAsLeft :
                            rightWord.toList =
                              before ++
                                [leftBlock.marker, rightSelected,
                                  leftNext.marker] ++
                                (rightNext.seconds ++
                                  renderGapBlocks rightRemaining) := by
                          simpa [renderGapBlocks, rightSeconds,
                            markerEq, nextMarkerEq,
                            List.append_assoc] using rightList
                        have leftOrdinary :
                            forall letter, letter ∈ ([] : List Nat) ->
                              letter ≠ rightSelected ∧
                                letter ≠ leftNext.marker := by simp
                        have leftAsOrdinary :
                            leftWord.toList =
                              before ++ [leftBlock.marker] ++ [] ++
                                (leftNext.marker ::
                                  (leftNext.seconds ++
                                    renderGapBlocks leftRemaining)) := by
                          simpa [renderGapBlocks, leftEmpty,
                            List.append_assoc] using leftList
                        have reverseValid :
                            (Identity.mk rightWord leftWord).SatisfiedBy
                              candidate := fun valuation =>
                                (valid valuation).symm
                        exact False.elim <|
                          selected_gap_contradiction separator
                            rightWord leftWord before leftBlock.marker
                            rightSelected leftNext.marker
                            (rightNext.seconds ++
                              renderGapBlocks rightRemaining)
                            []
                            (leftNext.seconds ++
                              renderGapBlocks leftRemaining)
                            rightAsLeft leftAsOrdinary
                            rightSelectedNeNext currentNeSelected
                            currentNeNext beforeNoNext leftOrdinary
                            reverseValid
            · rcases rightChoice with rightEmpty |
                ⟨rightSelected, rightSelectedSeen, rightSeconds⟩
              · cases leftRest with
                | nil =>
                    cases rightRest with
                    | nil =>
                        have leftFinal :
                            leftWord.final = leftSelected := by
                          apply final_eq_of_toList_eq leftWord
                            (before ++ [leftBlock.marker]) leftSelected
                          simpa [renderGapBlocks, leftSeconds,
                            List.append_assoc] using leftList
                        have rightFinal :
                            rightWord.final = rightBlock.marker := by
                          apply final_eq_of_toList_eq rightWord before
                            rightBlock.marker
                          simpa [renderGapBlocks, rightEmpty,
                            List.append_assoc] using rightList
                        have selectedEq :
                            leftSelected = rightBlock.marker :=
                          leftFinal.symm.trans (finalEq.trans rightFinal)
                        have leftSelectedNe :
                            leftSelected ≠ leftBlock.marker := by
                          intro equal
                          exact leftFresh <| by
                            rw [← equal]
                            exact leftSelectedSeen
                        exact False.elim <|
                          leftSelectedNe (selectedEq.trans markerEq.symm)
                    | cons rightNext rightRemaining =>
                        simp [gapBlockMarkers] at tailMarkers
                | cons leftNext leftRemaining =>
                    cases rightRest with
                    | nil =>
                        simp [gapBlockMarkers] at tailMarkers
                    | cons rightNext rightRemaining =>
                        have nextMarkerEq :
                            leftNext.marker = rightNext.marker := by
                          simpa [gapBlockMarkers] using
                            congrArg List.head? tailMarkers
                        have nextFresh := leftTail.headFresh
                        have selectedNeNext :
                            leftSelected ≠ leftNext.marker := by
                          intro equal
                          exact nextFresh <| by
                            rw [← equal]
                            exact List.Mem.tail leftBlock.marker
                              leftSelectedSeen
                        have currentNeSelected :
                            leftBlock.marker ≠ leftSelected := by
                          intro equal
                          exact leftFresh <| by
                            rw [equal]
                            exact leftSelectedSeen
                        have currentNeNext :
                            leftBlock.marker ≠ leftNext.marker := by
                          intro equal
                          exact nextFresh <| by simp [← equal]
                        have beforeNoNext :
                            forall letter, letter ∈ before ->
                              letter ≠ leftNext.marker := by
                          intro letter member equal
                          exact nextFresh <| by
                            rw [← equal]
                            exact List.Mem.tail leftBlock.marker
                              (beforeSeen letter member)
                        have leftAsSelected :
                            leftWord.toList =
                              before ++
                                [leftBlock.marker, leftSelected,
                                  leftNext.marker] ++
                                (leftNext.seconds ++
                                  renderGapBlocks leftRemaining) := by
                          simpa [renderGapBlocks, leftSeconds,
                            List.append_assoc] using leftList
                        have rightOrdinary :
                            forall letter, letter ∈ ([] : List Nat) ->
                              letter ≠ leftSelected ∧
                                letter ≠ leftNext.marker := by simp
                        have rightAsOrdinary :
                            rightWord.toList =
                              before ++ [leftBlock.marker] ++ [] ++
                                (leftNext.marker ::
                                  (rightNext.seconds ++
                                    renderGapBlocks rightRemaining)) := by
                          simpa [renderGapBlocks, rightEmpty,
                            markerEq, nextMarkerEq,
                            List.append_assoc] using rightList
                        exact False.elim <|
                          selected_gap_contradiction separator
                            leftWord rightWord before leftBlock.marker
                            leftSelected leftNext.marker
                            (leftNext.seconds ++
                              renderGapBlocks leftRemaining)
                            []
                            (rightNext.seconds ++
                              renderGapBlocks rightRemaining)
                            leftAsSelected rightAsOrdinary
                            selectedNeNext currentNeSelected currentNeNext
                            beforeNoNext rightOrdinary valid
              · by_cases sameSelected : leftSelected = rightSelected
                · simpa [leftSeconds, rightSeconds, sameSelected]
                · cases leftRest with
                  | nil =>
                      cases rightRest with
                      | nil =>
                          have leftFinal :
                              leftWord.final = leftSelected := by
                            apply final_eq_of_toList_eq leftWord
                              (before ++ [leftBlock.marker]) leftSelected
                            simpa [renderGapBlocks, leftSeconds,
                              List.append_assoc] using leftList
                          have rightFinal :
                              rightWord.final = rightSelected := by
                            apply final_eq_of_toList_eq rightWord
                              (before ++ [rightBlock.marker]) rightSelected
                            simpa [renderGapBlocks, rightSeconds,
                              List.append_assoc] using rightList
                          exact False.elim <| sameSelected <|
                            leftFinal.symm.trans (finalEq.trans rightFinal)
                      | cons rightNext rightRemaining =>
                          simp [gapBlockMarkers] at tailMarkers
                  | cons leftNext leftRemaining =>
                      cases rightRest with
                      | nil =>
                          simp [gapBlockMarkers] at tailMarkers
                      | cons rightNext rightRemaining =>
                          have nextMarkerEq :
                              leftNext.marker = rightNext.marker := by
                            simpa [gapBlockMarkers] using
                              congrArg List.head? tailMarkers
                          have nextFresh := leftTail.headFresh
                          have selectedNeNext :
                              leftSelected ≠ leftNext.marker := by
                            intro equal
                            exact nextFresh <| by
                              rw [← equal]
                              exact List.Mem.tail leftBlock.marker
                                leftSelectedSeen
                          have currentNeSelected :
                              leftBlock.marker ≠ leftSelected := by
                            intro equal
                            exact leftFresh <| by
                              rw [equal]
                              exact leftSelectedSeen
                          have currentNeNext :
                              leftBlock.marker ≠ leftNext.marker := by
                            intro equal
                            exact nextFresh <| by simp [← equal]
                          have rightSelectedNeNext :
                              rightSelected ≠ leftNext.marker := by
                            intro equal
                            exact nextFresh <| by
                              rw [← equal]
                              exact List.Mem.tail leftBlock.marker
                                rightSelectedSeen
                          have beforeNoNext :
                              forall letter, letter ∈ before ->
                                letter ≠ leftNext.marker := by
                            intro letter member equal
                            exact nextFresh <| by
                              rw [← equal]
                              exact List.Mem.tail leftBlock.marker
                                (beforeSeen letter member)
                          have leftAsSelected :
                              leftWord.toList =
                                before ++
                                  [leftBlock.marker, leftSelected,
                                    leftNext.marker] ++
                                  (leftNext.seconds ++
                                    renderGapBlocks leftRemaining) := by
                            simpa [renderGapBlocks, leftSeconds,
                              List.append_assoc] using leftList
                          have rightAsOrdinary :
                              rightWord.toList =
                                before ++ [leftBlock.marker] ++
                                  [rightSelected] ++
                                  (leftNext.marker ::
                                    (rightNext.seconds ++
                                      renderGapBlocks rightRemaining)) := by
                            simpa [renderGapBlocks, rightSeconds,
                              markerEq, nextMarkerEq,
                              List.append_assoc] using rightList
                          have rightOrdinary :
                              forall letter, letter ∈ [rightSelected] ->
                                letter ≠ leftSelected ∧
                                  letter ≠ leftNext.marker := by
                            intro letter member
                            simp only [List.mem_singleton] at member
                            subst letter
                            exact ⟨Ne.symm sameSelected,
                              rightSelectedNeNext⟩
                          exact False.elim <|
                            selected_gap_contradiction separator
                              leftWord rightWord before leftBlock.marker
                              leftSelected leftNext.marker
                              (leftNext.seconds ++
                                renderGapBlocks leftRemaining)
                              [rightSelected]
                              (rightNext.seconds ++
                                renderGapBlocks rightRemaining)
                              leftAsSelected rightAsOrdinary
                              selectedNeNext currentNeSelected
                              currentNeNext beforeNoNext rightOrdinary valid
          have blockEq :=
            gapBlock_eq leftBlock rightBlock markerEq secondsEq
          subst rightBlock
          have nextBeforeSeen :=
            extend_before_seen beforeSeen
              (choice_members leftChoice)
              (marker := leftBlock.marker)
          have leftTailList :
              leftWord.toList =
                (before ++ [leftBlock.marker] ++ leftBlock.seconds) ++
                  renderGapBlocks leftRest := by
            simpa [renderGapBlocks, List.append_assoc] using leftList
          have rightTailList :
              rightWord.toList =
                (before ++ [leftBlock.marker] ++ leftBlock.seconds) ++
                  renderGapBlocks rightRest := by
            simpa [renderGapBlocks, List.append_assoc] using rightList
          have tailEq :=
            cleanBlocks_eq_of_valid separator leftWord rightWord
              leftTail rightTail tailMarkers leftTailList rightTailList
              nextBeforeSeen valid finalEq
          rw [tailEq]
termination_by leftBlocks.length
decreasing_by
  simp_all only [List.length_cons, Nat.lt_succ_iff, Nat.le_refl]

private theorem nonterminal_seconds_eq_of_valid
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    (leftWord rightWord : Word Nat)
    (seen before : List Nat) (current nextMarker : Nat)
    (leftSeconds rightSeconds leftSuffix rightSuffix : List Nat)
    (leftChoice : ChoiceIn seen leftSeconds)
    (rightChoice : ChoiceIn seen rightSeconds)
    (currentFresh : current ∉ seen)
    (nextFresh : nextMarker ∉ current :: seen)
    (beforeSeen : forall letter, letter ∈ before -> letter ∈ seen)
    (leftList :
      leftWord.toList =
        before ++ [current] ++ leftSeconds ++
          (nextMarker :: leftSuffix))
    (rightList :
      rightWord.toList =
        before ++ [current] ++ rightSeconds ++
          (nextMarker :: rightSuffix))
    (valid :
      (Identity.mk leftWord rightWord).SatisfiedBy candidate) :
    leftSeconds = rightSeconds := by
  have currentNeNext : current ≠ nextMarker := by
    intro equal
    exact nextFresh (by simp [← equal])
  have beforeNoNext :
      forall letter, letter ∈ before -> letter ≠ nextMarker := by
    intro letter member equal
    exact nextFresh <| by
      rw [← equal]
      exact List.Mem.tail current (beforeSeen letter member)
  rcases leftChoice with leftEmpty |
    ⟨leftSelected, leftSelectedSeen, leftShape⟩
  · rcases rightChoice with rightEmpty |
      ⟨rightSelected, rightSelectedSeen, rightShape⟩
    · exact leftEmpty.trans rightEmpty.symm
    · have selectedNeNext : rightSelected ≠ nextMarker := by
        intro equal
        exact nextFresh <| by
          rw [← equal]
          exact List.Mem.tail current rightSelectedSeen
      have currentNeSelected : current ≠ rightSelected := by
        intro equal
        exact currentFresh <| by
          rw [equal]
          exact rightSelectedSeen
      have leftOrdinary :
          forall letter, letter ∈ ([] : List Nat) ->
            letter ≠ rightSelected ∧ letter ≠ nextMarker := by simp
      have reverseValid :
          (Identity.mk rightWord leftWord).SatisfiedBy candidate :=
        fun valuation => (valid valuation).symm
      exact False.elim <|
        selected_gap_contradiction separator rightWord leftWord before
          current rightSelected nextMarker rightSuffix [] leftSuffix
          (by simpa [rightShape, List.append_assoc] using rightList)
          (by simpa [leftEmpty, List.append_assoc] using leftList)
          selectedNeNext currentNeSelected currentNeNext beforeNoNext
          leftOrdinary reverseValid
  · rcases rightChoice with rightEmpty |
      ⟨rightSelected, rightSelectedSeen, rightShape⟩
    · have selectedNeNext : leftSelected ≠ nextMarker := by
        intro equal
        exact nextFresh <| by
          rw [← equal]
          exact List.Mem.tail current leftSelectedSeen
      have currentNeSelected : current ≠ leftSelected := by
        intro equal
        exact currentFresh <| by
          rw [equal]
          exact leftSelectedSeen
      have rightOrdinary :
          forall letter, letter ∈ ([] : List Nat) ->
            letter ≠ leftSelected ∧ letter ≠ nextMarker := by simp
      exact False.elim <|
        selected_gap_contradiction separator leftWord rightWord before
          current leftSelected nextMarker leftSuffix [] rightSuffix
          (by simpa [leftShape, List.append_assoc] using leftList)
          (by simpa [rightEmpty, List.append_assoc] using rightList)
          selectedNeNext currentNeSelected currentNeNext beforeNoNext
          rightOrdinary valid
    · by_cases sameSelected : leftSelected = rightSelected
      · simpa [leftShape, rightShape, sameSelected]
      · have selectedNeNext : leftSelected ≠ nextMarker := by
          intro equal
          exact nextFresh <| by
            rw [← equal]
            exact List.Mem.tail current leftSelectedSeen
        have rightSelectedNeNext : rightSelected ≠ nextMarker := by
          intro equal
          exact nextFresh <| by
            rw [← equal]
            exact List.Mem.tail current rightSelectedSeen
        have currentNeSelected : current ≠ leftSelected := by
          intro equal
          exact currentFresh <| by
            rw [equal]
            exact leftSelectedSeen
        have rightOrdinary :
            forall letter, letter ∈ [rightSelected] ->
              letter ≠ leftSelected ∧ letter ≠ nextMarker := by
          intro letter member
          simp only [List.mem_singleton] at member
          subst letter
          exact ⟨Ne.symm sameSelected, rightSelectedNeNext⟩
        exact False.elim <|
          selected_gap_contradiction separator leftWord rightWord before
            current leftSelected nextMarker leftSuffix [rightSelected]
            rightSuffix
            (by simpa [leftShape, List.append_assoc] using leftList)
            (by simpa [rightShape, List.append_assoc] using rightList)
            selectedNeNext currentNeSelected currentNeNext beforeNoNext
            rightOrdinary valid

private theorem simpleFinal_single_double_ne
    (single double : Word Nat) (before : List Nat) (marker : Nat)
    (markerAbsent : marker ∉ before)
    (singleList : single.toList = before ++ [marker])
    (doubleList : double.toList = before ++ [marker, marker]) :
    S5_345.simpleFinalVariable single ≠
      S5_345.simpleFinalVariable double := by
  have singleCount : single.toList.count marker = 1 := by
    rw [singleList, List.count_append]
    simp [List.count_eq_zero.mpr markerAbsent]
  have singleFinal : single.final = marker :=
    final_eq_of_toList_eq single before marker singleList
  have singleSome :
      S5_345.simpleFinalVariable single = some marker :=
    (S5_345.simpleFinalVariable_eq_some_iff single marker).2
      ⟨singleCount, singleFinal⟩
  intro equal
  have doubleSome :
      S5_345.simpleFinalVariable double = some marker :=
    equal.symm.trans singleSome
  have doubleSimple :=
    (S5_345.simpleFinalVariable_eq_some_iff double marker).1
      doubleSome
  have doubleCount := doubleSimple.1
  unfold S5_107.SimpleIn at doubleCount
  rw [doubleList, List.count_append] at doubleCount
  simp [List.count_eq_zero.mpr markerAbsent] at doubleCount

private theorem alpha_terminal_seconds_eq
    (leftWord rightWord : Word Nat)
    (seen before : List Nat) (marker : Nat)
    (leftSeconds rightSeconds : List Nat)
    (leftChoice : ChoiceIn (marker :: seen) leftSeconds)
    (rightChoice : ChoiceIn (marker :: seen) rightSeconds)
    (markerFresh : marker ∉ seen)
    (beforeSeen : forall letter, letter ∈ before -> letter ∈ seen)
    (leftList : leftWord.toList = before ++ marker :: leftSeconds)
    (rightList : rightWord.toList = before ++ marker :: rightSeconds)
    (finalEq : leftWord.final = rightWord.final)
    (simpleEq :
      S5_345.simpleFinalVariable leftWord =
        S5_345.simpleFinalVariable rightWord) :
    leftSeconds = rightSeconds := by
  have markerAbsent : marker ∉ before := by
    intro member
    exact markerFresh (beforeSeen marker member)
  rcases leftChoice with leftEmpty |
    ⟨leftSelected, leftSelectedKnown, leftShape⟩
  · rcases rightChoice with rightEmpty |
      ⟨rightSelected, rightSelectedKnown, rightShape⟩
    · exact leftEmpty.trans rightEmpty.symm
    · by_cases selectedMarker : rightSelected = marker
      · subst rightSelected
        have mismatch := simpleFinal_single_double_ne
          leftWord rightWord before marker markerAbsent
          (by simpa [leftEmpty] using leftList)
          (by simpa [rightShape, List.append_assoc] using rightList)
        exact False.elim (mismatch simpleEq)
      · have selectedSeen : rightSelected ∈ seen :=
          (List.mem_cons.mp rightSelectedKnown).resolve_left selectedMarker
        have leftFinal : leftWord.final = marker := by
          apply final_eq_of_toList_eq leftWord before marker
          simpa [leftEmpty] using leftList
        have rightFinal : rightWord.final = rightSelected := by
          apply final_eq_of_toList_eq rightWord
            (before ++ [marker]) rightSelected
          simpa [rightShape, List.append_assoc] using rightList
        have selectedEq : rightSelected = marker :=
          rightFinal.symm.trans (finalEq.symm.trans leftFinal)
        exact False.elim (selectedMarker selectedEq)
  · rcases rightChoice with rightEmpty |
      ⟨rightSelected, rightSelectedKnown, rightShape⟩
    · by_cases selectedMarker : leftSelected = marker
      · subst leftSelected
        have mismatch := simpleFinal_single_double_ne
          rightWord leftWord before marker markerAbsent
          (by simpa [rightEmpty] using rightList)
          (by simpa [leftShape, List.append_assoc] using leftList)
        exact False.elim (mismatch simpleEq.symm)
      · have selectedSeen : leftSelected ∈ seen :=
          (List.mem_cons.mp leftSelectedKnown).resolve_left selectedMarker
        have leftFinal : leftWord.final = leftSelected := by
          apply final_eq_of_toList_eq leftWord
            (before ++ [marker]) leftSelected
          simpa [leftShape, List.append_assoc] using leftList
        have rightFinal : rightWord.final = marker := by
          apply final_eq_of_toList_eq rightWord before marker
          simpa [rightEmpty] using rightList
        have selectedEq : leftSelected = marker :=
          leftFinal.symm.trans (finalEq.trans rightFinal)
        exact False.elim (selectedMarker selectedEq)
    · have leftFinal : leftWord.final = leftSelected := by
        apply final_eq_of_toList_eq leftWord
          (before ++ [marker]) leftSelected
        simpa [leftShape, List.append_assoc] using leftList
      have rightFinal : rightWord.final = rightSelected := by
        apply final_eq_of_toList_eq rightWord
          (before ++ [marker]) rightSelected
        simpa [rightShape, List.append_assoc] using rightList
      have selectedEq : leftSelected = rightSelected :=
        leftFinal.symm.trans (finalEq.trans rightFinal)
      simpa [leftShape, rightShape, selectedEq]

set_option maxHeartbeats 2000000 in
private theorem alphaBlocks_eq_of_valid
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    (leftWord rightWord : Word Nat)
    {seen before : List Nat}
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (leftNormal : AlphaBlocks seen leftBlocks)
    (rightNormal : AlphaBlocks seen rightBlocks)
    (markers :
      gapBlockMarkers leftBlocks = gapBlockMarkers rightBlocks)
    (leftList :
      leftWord.toList = before ++ renderGapBlocks leftBlocks)
    (rightList :
      rightWord.toList = before ++ renderGapBlocks rightBlocks)
    (beforeSeen : forall letter, letter ∈ before -> letter ∈ seen)
    (valid :
      (Identity.mk leftWord rightWord).SatisfiedBy candidate)
    (finalEq : leftWord.final = rightWord.final)
    (simpleEq :
      S5_345.simpleFinalVariable leftWord =
        S5_345.simpleFinalVariable rightWord) :
    leftBlocks = rightBlocks := by
  cases leftNormal with
  | nil seen =>
      cases rightNormal with
      | nil => rfl
      | last _ block fresh choice =>
          simp [gapBlockMarkers] at markers
      | cons _ block next rest fresh choice tail =>
          simp [gapBlockMarkers] at markers
  | last seen leftBlock leftFresh leftChoice =>
      cases rightNormal with
      | nil => simp [gapBlockMarkers] at markers
      | last _ rightBlock rightFresh rightChoice =>
          simp only [gapBlockMarkers, List.map_singleton,
            FirstOccurrenceGapBlock.marker] at markers
          have markerEq : leftBlock.marker = rightBlock.marker :=
            (List.cons.inj markers).1
          have rightChoice' :
              ChoiceIn (leftBlock.marker :: seen) rightBlock.seconds := by
            simpa [markerEq] using rightChoice
          have rightList' :
              rightWord.toList =
                before ++ leftBlock.marker :: rightBlock.seconds := by
            simpa [renderGapBlocks, markerEq] using rightList
          have secondsEq :=
            alpha_terminal_seconds_eq leftWord rightWord seen before
              leftBlock.marker leftBlock.seconds rightBlock.seconds
              leftChoice rightChoice' leftFresh beforeSeen
              (by simpa [renderGapBlocks] using leftList)
              rightList' finalEq simpleEq
          exact congrArg List.singleton <|
            gapBlock_eq leftBlock rightBlock markerEq secondsEq
      | cons _ rightBlock rightNext rightRest rightFresh rightChoice
          rightTail =>
          simp [gapBlockMarkers] at markers
  | cons seen leftBlock leftNext leftRest leftFresh leftChoice leftTail =>
      cases rightNormal with
      | nil => simp [gapBlockMarkers] at markers
      | last _ rightBlock rightFresh rightChoice =>
          simp [gapBlockMarkers] at markers
      | cons _ rightBlock rightNext rightRest rightFresh rightChoice
          rightTail =>
          simp only [gapBlockMarkers, List.map_cons,
            FirstOccurrenceGapBlock.marker] at markers
          have markerEq : leftBlock.marker = rightBlock.marker :=
            (List.cons.inj markers).1
          have tailMarkers :
              gapBlockMarkers (leftNext :: leftRest) =
                gapBlockMarkers (rightNext :: rightRest) :=
            (List.cons.inj markers).2
          have nextMarkerEq : leftNext.marker = rightNext.marker := by
            simpa [gapBlockMarkers] using congrArg List.head? tailMarkers
          have nextFresh := leftTail.headFresh
          have rightChoice' : ChoiceIn seen rightBlock.seconds := by
            exact rightChoice
          have leftCommonList :
              leftWord.toList =
                before ++ [leftBlock.marker] ++ leftBlock.seconds ++
                  (leftNext.marker ::
                    (leftNext.seconds ++ renderGapBlocks leftRest)) := by
            simpa [renderGapBlocks, List.append_assoc] using leftList
          have rightCommonList :
              rightWord.toList =
                before ++ [leftBlock.marker] ++ rightBlock.seconds ++
                  (leftNext.marker ::
                    (rightNext.seconds ++ renderGapBlocks rightRest)) := by
            simpa [renderGapBlocks, markerEq, nextMarkerEq,
              List.append_assoc] using rightList
          have secondsEq :=
            nonterminal_seconds_eq_of_valid separator leftWord rightWord
              seen before leftBlock.marker leftNext.marker
              leftBlock.seconds rightBlock.seconds
              (leftNext.seconds ++ renderGapBlocks leftRest)
              (rightNext.seconds ++ renderGapBlocks rightRest)
              leftChoice rightChoice' leftFresh nextFresh beforeSeen
              leftCommonList rightCommonList valid
          have blockEq :=
            gapBlock_eq leftBlock rightBlock markerEq secondsEq
          subst rightBlock
          have nextBeforeSeen :=
            extend_before_seen beforeSeen
              (choice_members leftChoice)
              (marker := leftBlock.marker)
          have leftTailList :
              leftWord.toList =
                (before ++ [leftBlock.marker] ++ leftBlock.seconds) ++
                  renderGapBlocks (leftNext :: leftRest) := by
            simpa [renderGapBlocks, List.append_assoc] using leftList
          have rightTailList :
              rightWord.toList =
                (before ++ [leftBlock.marker] ++ leftBlock.seconds) ++
                  renderGapBlocks (rightNext :: rightRest) := by
            simpa [renderGapBlocks, List.append_assoc] using rightList
          have tailEq :=
            alphaBlocks_eq_of_valid separator leftWord rightWord
              leftTail rightTail tailMarkers leftTailList rightTailList
              nextBeforeSeen valid finalEq simpleEq
          rw [tailEq]
termination_by leftBlocks.length
decreasing_by
  simp_all only [List.length_cons, Nat.lt_succ_iff, Nat.le_refl]

/-- Alpha canonical representatives with the same first-occurrence order,
final letter, simple-final status, and A7 semantics are literally equal. -/
theorem alphaCanonicalWord_eq_of_invariants
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    (identity : Identity Nat)
    (firstOccurrences :
      firstOccurrenceSequence identity.lhs.toList =
        firstOccurrenceSequence identity.rhs.toList)
    (canonicalValid :
      (alphaCanonicalIdentity identity).SatisfiedBy candidate)
    (canonicalFinal :
      (alphaCanonicalWord identity.lhs).final =
        (alphaCanonicalWord identity.rhs).final)
    (canonicalSimpleFinal :
      S5_345.simpleFinalVariable (alphaCanonicalWord identity.lhs) =
        S5_345.simpleFinalVariable (alphaCanonicalWord identity.rhs)) :
    alphaCanonicalWord identity.lhs =
      alphaCanonicalWord identity.rhs := by
  let leftSource := gapBlocksList identity.lhs.toList
  let rightSource := gapBlocksList identity.rhs.toList
  let leftBlocks := alphaCanonicalBlocks leftSource
  let rightBlocks := alphaCanonicalBlocks rightSource
  have sourceMarkers :
      gapBlockMarkers leftSource = gapBlockMarkers rightSource := by
    simpa [leftSource, rightSource,
      gapBlockMarkers_gapBlocksList,
      firstOccurrenceSequenceList_eq_firstOccurrenceSequence] using
        firstOccurrences
  have markers :
      gapBlockMarkers leftBlocks = gapBlockMarkers rightBlocks := by
    simpa [leftBlocks, rightBlocks,
      markers_alphaCanonicalBlocks] using sourceMarkers
  have leftNormal : AlphaBlocks [] leftBlocks := by
    exact alphaCanonicalBlocks_normal
      (gapBlocksList_wellFormed identity.lhs.toList)
  have rightNormal : AlphaBlocks [] rightBlocks := by
    exact alphaCanonicalBlocks_normal
      (gapBlocksList_wellFormed identity.rhs.toList)
  have leftList :
      (alphaCanonicalWord identity.lhs).toList =
        renderGapBlocks leftBlocks := by
    exact alphaCanonicalWord_toList_blocks identity.lhs
  have rightList :
      (alphaCanonicalWord identity.rhs).toList =
        renderGapBlocks rightBlocks := by
    exact alphaCanonicalWord_toList_blocks identity.rhs
  have blockEq :=
    alphaBlocks_eq_of_valid separator
      (alphaCanonicalWord identity.lhs)
      (alphaCanonicalWord identity.rhs)
      (before := [])
      leftNormal rightNormal markers
      (by simpa using leftList)
      (by simpa using rightList)
      (by simp) canonicalValid canonicalFinal canonicalSimpleFinal
  apply Word.toList_injective
  rw [leftList, rightList, blockEq]

private theorem singleton_choice
    {marker : Nat} {seconds : List Nat}
    (choice : ChoiceIn [marker] seconds) :
    seconds = [] ∨ seconds = [marker] := by
  rcases choice with empty | ⟨selected, selectedMember, shape⟩
  · exact Or.inl empty
  · have selectedEq : selected = marker := by simpa using selectedMember
    exact Or.inr <| by simpa [selectedEq] using shape

private theorem unary_seconds_eq_of_valid
    {candidate : Semigroup (Fin 6)}
    (separator : UnarySeparator candidate)
    (left right : Word Nat) (marker : Nat)
    (leftSeconds rightSeconds : List Nat)
    (leftChoice : leftSeconds = [] ∨ leftSeconds = [marker])
    (rightChoice : rightSeconds = [] ∨ rightSeconds = [marker])
    (leftList : left.toList = marker :: leftSeconds)
    (rightList : right.toList = marker :: rightSeconds)
    (valid : (Identity.mk left right).SatisfiedBy candidate) :
    leftSeconds = rightSeconds := by
  rcases leftChoice with leftEmpty | leftDouble
  · rcases rightChoice with rightEmpty | rightDouble
    · exact leftEmpty.trans rightEmpty.symm
    · have leftWord : left = Word.singleton marker := by
        apply Word.toList_injective
        simpa [leftEmpty, Word.singleton, Word.toList] using leftList
      have rightWord : right = Word.mk marker [marker] := by
        apply Word.toList_injective
        simpa [rightDouble, Word.toList] using rightList
      have evaluated := valid (fun _ => separator.value)
      rw [leftWord, rightWord] at evaluated
      exact False.elim <| separator.value_ne_square <| by
        simpa [Semigroup.eval, Word.singleton] using evaluated
  · rcases rightChoice with rightEmpty | rightDouble
    · have leftWord : left = Word.mk marker [marker] := by
        apply Word.toList_injective
        simpa [leftDouble, Word.toList] using leftList
      have rightWord : right = Word.singleton marker := by
        apply Word.toList_injective
        simpa [rightEmpty, Word.singleton, Word.toList] using rightList
      have evaluated := valid (fun _ => separator.value)
      rw [leftWord, rightWord] at evaluated
      exact False.elim <| separator.value_ne_square <| by
        simpa [Semigroup.eval, Word.singleton] using evaluated.symm
    · exact leftDouble.trans rightDouble.symm

/-- Beta canonical representatives with equal first-occurrence order and
equal target semantics are literally equal. The many-marker branch is the
clean-block recursion; the one-marker branch is separated by a nonidempotent
table element. -/
theorem betaCanonicalWord_eq_of_invariants
    {candidate : Semigroup (Fin 6)}
    (gapSeparator : GapSeparator candidate)
    (unarySeparator : UnarySeparator candidate)
    (identity : Identity Nat)
    (firstOccurrences :
      firstOccurrenceSequence identity.lhs.toList =
        firstOccurrenceSequence identity.rhs.toList)
    (canonicalValid :
      (betaCanonicalIdentity identity).SatisfiedBy candidate)
    (canonicalFinal :
      (betaCanonicalWord identity.lhs).final =
        (betaCanonicalWord identity.rhs).final) :
    betaCanonicalWord identity.lhs =
      betaCanonicalWord identity.rhs := by
  let leftSource := gapBlocksList identity.lhs.toList
  let rightSource := gapBlocksList identity.rhs.toList
  let leftBlocks := betaCanonicalBlocks leftSource
  let rightBlocks := betaCanonicalBlocks rightSource
  have sourceMarkers :
      gapBlockMarkers leftSource = gapBlockMarkers rightSource := by
    simpa [leftSource, rightSource,
      gapBlockMarkers_gapBlocksList,
      firstOccurrenceSequenceList_eq_firstOccurrenceSequence] using
        firstOccurrences
  have markers :
      gapBlockMarkers leftBlocks = gapBlockMarkers rightBlocks := by
    simpa [leftBlocks, rightBlocks,
      markers_betaCanonicalBlocks] using sourceMarkers
  have leftNormal : BetaBlocks [] leftBlocks := by
    exact betaCanonicalBlocks_normal
      (gapBlocksList_wellFormed identity.lhs.toList)
  have rightNormal : BetaBlocks [] rightBlocks := by
    exact betaCanonicalBlocks_normal
      (gapBlocksList_wellFormed identity.rhs.toList)
  have leftList :
      (betaCanonicalWord identity.lhs).toList =
        renderGapBlocks leftBlocks := by
    exact betaCanonicalWord_toList_blocks identity.lhs
  have rightList :
      (betaCanonicalWord identity.rhs).toList =
        renderGapBlocks rightBlocks := by
    exact betaCanonicalWord_toList_blocks identity.rhs
  have blockEq : leftBlocks = rightBlocks := by
    generalize leftEq : leftBlocks = leftBlocks' at leftNormal markers leftList ⊢
    generalize rightEq : rightBlocks = rightBlocks' at rightNormal markers rightList ⊢
    cases leftNormal with
    | nil =>
        cases canonicalShape : betaCanonicalWord identity.lhs with
        | mk head tail =>
            simp [canonicalShape, Word.toList, renderGapBlocks] at leftList
    | single leftBlock leftFresh leftChoice =>
        cases rightNormal with
        | nil => simp [gapBlockMarkers] at markers
        | single rightBlock rightFresh rightChoice =>
            simp only [gapBlockMarkers, List.map_singleton,
              FirstOccurrenceGapBlock.marker] at markers
            have markerEq : leftBlock.marker = rightBlock.marker :=
              (List.cons.inj markers).1
            have rightChoice' :
                rightBlock.seconds = [] ∨
                  rightBlock.seconds = [leftBlock.marker] := by
              simpa [markerEq] using singleton_choice rightChoice
            have rightList' :
                (betaCanonicalWord identity.rhs).toList =
                  leftBlock.marker :: rightBlock.seconds := by
              simpa [renderGapBlocks, markerEq] using rightList
            have secondsEq :=
              unary_seconds_eq_of_valid unarySeparator
                (betaCanonicalWord identity.lhs)
                (betaCanonicalWord identity.rhs)
                leftBlock.marker leftBlock.seconds rightBlock.seconds
                (singleton_choice leftChoice)
                rightChoice'
                (by simpa [renderGapBlocks] using leftList)
                rightList'
                canonicalValid
            exact congrArg List.singleton <|
              gapBlock_eq leftBlock rightBlock markerEq secondsEq
        | many rightBlock rightNext rightRest rightClean =>
            simp [gapBlockMarkers] at markers
    | many leftBlock leftNext leftRest leftClean =>
        cases rightNormal with
        | nil => simp [gapBlockMarkers] at markers
        | single rightBlock rightFresh rightChoice =>
            simp [gapBlockMarkers] at markers
        | many rightBlock rightNext rightRest rightClean =>
            exact cleanBlocks_eq_of_valid gapSeparator
              (betaCanonicalWord identity.lhs)
              (betaCanonicalWord identity.rhs)
              (before := [])
              leftClean rightClean markers
              (by simpa using leftList)
              (by simpa using rightList)
              (by simp) canonicalValid canonicalFinal
  apply Word.toList_injective
  rw [leftList, rightList, blockEq]

end SemigroupBasis.CoRoots.Order6SporadicSection14
