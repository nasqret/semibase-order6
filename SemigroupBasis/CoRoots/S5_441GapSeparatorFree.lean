import SemigroupBasis.CoRoots.S5_441GapScannerComplete
import SemigroupBasis.CoRoots.S5_441GapCountLocalization
import SemigroupBasis.Examples.ConnectedComponentFourComponents

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis.Examples

private theorem exactCut_separator_not_right
    {letters left right : List Nat} {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        letters left separator right) :
    separator ∉ right := by
  intro member
  have positive : 0 < right.count separator :=
    List.count_pos_iff.mpr member
  have countOne := cut.2.1
  rw [cut.1, List.count_append, List.count_cons_self] at countOne
  omega

private theorem mem_exactCutSeparators_of_separator_eq
    {segments : List ExactCutSegment}
    {segment : ExactCutSegment} {separator : Nat}
    (segmentMember : segment ∈ segments)
    (separatorEq : segment.separator = some separator) :
    separator ∈ exactCutSeparators segments := by
  unfold exactCutSeparators
  rw [List.mem_filterMap]
  exact ⟨segment, segmentMember, separatorEq⟩

private theorem mem_exactCutSeparators_of_separator_toList
    {segments : List ExactCutSegment}
    {segment : ExactCutSegment} {letter : Nat}
    (segmentMember : segment ∈ segments)
    (letterMember : letter ∈ segment.separator.toList) :
    letter ∈ exactCutSeparators segments := by
  cases separatorEq : segment.separator with
  | none =>
      simp [separatorEq] at letterMember
  | some separator =>
      have letterEq : letter = separator := by
        simpa [separatorEq] using letterMember
      subst separator
      exact
        mem_exactCutSeparators_of_separator_eq
          segmentMember separatorEq

/-- Earlier and later rendered segments have disjoint supports, including
their optional separators. -/
private theorem exactCutDecomposition_ordered_renders_disjoint
    {letters : List Nat}
    {before between after : List ExactCutSegment}
    {left right : ExactCutSegment}
    (decompositionEq :
      exactCutDecomposition letters =
        before ++ left :: (between ++ right :: after)) :
    UniqueSeparatorFourSupportsDisjoint
      left.render right.render := by
  have suffixNonempty : between ++ right :: after ≠ [] := by
    simp
  obtain ⟨separator, separatorEq⟩ :=
    exactCutDecomposition_separator_some_of_after_ne_nil
      (letters := letters)
      (before := before)
      (segment := left)
      (after := between ++ right :: after)
      decompositionEq suffixNonempty
  have cut :=
    exactCutDecomposition_separator_exactCut
      (letters := letters)
      (before := before)
      (after := between ++ right :: after)
      (segment := left)
      decompositionEq separatorEq
  have separatorNotRight :=
    exactCut_separator_not_right cut
  intro letter leftMember rightMember
  have rightRendered :
      letter ∈
        renderExactCutSegments
          (between ++ right :: after) := by
    change
      letter ∈
        (between ++ right :: after).flatMap
          ExactCutSegment.render
    rw [List.mem_flatMap]
    exact ⟨right, by simp, rightMember⟩
  change
    letter ∈ left.gap ++ left.separator.toList
      at leftMember
  rw [List.mem_append] at leftMember
  rcases leftMember with leftGapMember | leftSeparatorMember
  · exact
      cut.2.2 letter
        (List.mem_append_right _ leftGapMember)
        rightRendered
  · have letterEq : letter = separator := by
      simpa [separatorEq] using leftSeparatorMember
    subst separator
    exact separatorNotRight rightRendered

private theorem exactCutDecomposition_suffix_renders_pairwise_disjoint
    {letters : List Nat} :
    ∀ {scanPrefix suffix : List ExactCutSegment},
      exactCutDecomposition letters = scanPrefix ++ suffix →
        suffix.Pairwise
          (fun left right =>
            UniqueSeparatorFourSupportsDisjoint
              left.render right.render) := by
  intro scanPrefix suffix decompositionEq
  induction suffix generalizing scanPrefix with
  | nil =>
      simp
  | cons left rest ih =>
      rw [List.pairwise_cons]
      constructor
      · intro right rightMember
        obtain ⟨between, after, restEq⟩ :=
          List.mem_iff_append.mp rightMember
        apply exactCutDecomposition_ordered_renders_disjoint
          (letters := letters)
          (before := scanPrefix)
          (between := between)
          (after := after)
          (left := left)
          (right := right)
        rw [decompositionEq, restEq]
      · apply ih (scanPrefix := scanPrefix ++ [left])
        simpa [List.append_assoc] using decompositionEq

/-- The rendered blocks of the exact-cut decomposition have pairwise-disjoint
supports. -/
theorem exactCutDecomposition_renders_pairwise_disjoint
    (letters : List Nat) :
    (exactCutDecomposition letters).Pairwise
      (fun left right =>
        UniqueSeparatorFourSupportsDisjoint
          left.render right.render) := by
  apply exactCutDecomposition_suffix_renders_pairwise_disjoint
    (letters := letters)
    (scanPrefix := [])
  simp

private theorem renderExactCutSegments_disjoint_of_pairwise_append
    {before after : List ExactCutSegment}
    (pairwise :
      (before ++ after).Pairwise
        (fun left right =>
          UniqueSeparatorFourSupportsDisjoint
            left.render right.render)) :
    UniqueSeparatorFourSupportsDisjoint
      (renderExactCutSegments before)
      (renderExactCutSegments after) := by
  have cross :=
    (List.pairwise_append.mp pairwise).2.2
  intro letter beforeMember afterMember
  change
    letter ∈ before.flatMap ExactCutSegment.render
      at beforeMember
  change
    letter ∈ after.flatMap ExactCutSegment.render
      at afterMember
  rw [List.mem_flatMap] at beforeMember afterMember
  rcases beforeMember with
    ⟨left, leftMember, letterInLeft⟩
  rcases afterMember with
    ⟨right, rightMember, letterInRight⟩
  exact
    (cross left leftMember right rightMember)
      letter letterInLeft letterInRight

/-- No exact separator cut can occur within a gap retained by the complete
exact-cut scanner. -/
theorem exactCutDecomposition_gap_not_exactCut
    {letters : List Nat} {segment : ExactCutSegment}
    {left right : List Nat} {separator : Nat}
    (segmentMember :
      segment ∈ exactCutDecomposition letters) :
    ¬ UniqueSeparatorFourExactCut
        segment.gap left separator right := by
  intro localCut
  obtain ⟨before, after, decompositionEq⟩ :=
    List.mem_iff_append.mp segmentMember
  have pairwise :=
    exactCutDecomposition_renders_pairwise_disjoint letters
  rw [decompositionEq] at pairwise
  have beforeSuffixDisjoint :
      UniqueSeparatorFourSupportsDisjoint
        (renderExactCutSegments before)
        (renderExactCutSegments (segment :: after)) :=
    renderExactCutSegments_disjoint_of_pairwise_append
      (before := before)
      (after := segment :: after)
      pairwise
  have tailPairwise :
      (segment :: after).Pairwise
        (fun left right =>
          UniqueSeparatorFourSupportsDisjoint
            left.render right.render) :=
    (List.pairwise_append.mp pairwise).2.1
  have segmentAfterDisjoint :
      UniqueSeparatorFourSupportsDisjoint
        segment.render
        (renderExactCutSegments after) := by
    have singletonAfterDisjoint :=
      renderExactCutSegments_disjoint_of_pairwise_append
        (before := [segment])
        (after := after)
        (by simpa using tailPairwise)
    simpa using singletonAfterDisjoint
  have separatorMemberGap : separator ∈ segment.gap := by
    rw [localCut.1]
    simp
  have countOne : letters.count separator = 1 :=
    (exactCutDecomposition_count_eq_gap_count
      segmentMember separatorMemberGap).trans localCut.2.1
  have lettersShape :
      letters =
        (renderExactCutSegments before ++ left) ++
          separator ::
            (right ++
              (segment.separator.toList ++
                renderExactCutSegments after)) := by
    calc
      letters =
          renderExactCutSegments
            (exactCutDecomposition letters) :=
        (render_exactCutDecomposition letters).symm
      _ =
          renderExactCutSegments
            (before ++ segment :: after) := by
        rw [decompositionEq]
      _ =
          (renderExactCutSegments before ++ left) ++
            separator ::
              (right ++
                (segment.separator.toList ++
                  renderExactCutSegments after)) := by
        simp [renderExactCutSegments, ExactCutSegment.render,
          localCut.1, List.append_assoc]
  have globalDisjoint :
      UniqueSeparatorFourSupportsDisjoint
        (renderExactCutSegments before ++ left)
        (right ++
          (segment.separator.toList ++
            renderExactCutSegments after)) := by
    intro letter globalLeftMember globalRightMember
    rw [List.mem_append] at globalLeftMember globalRightMember
    rcases globalLeftMember with
        beforeMember | localLeftMember
    · have rightInSuffix :
          letter ∈
            renderExactCutSegments (segment :: after) := by
        rcases globalRightMember with
            localRightMember | separatorOrAfterMember
        · change
            letter ∈
              (segment.gap ++ segment.separator.toList) ++
                renderExactCutSegments after
          exact
            List.mem_append_left _ <|
              List.mem_append_left _ <| by
                rw [localCut.1]
                exact
                  List.mem_append_right left <|
                    List.Mem.tail separator localRightMember
        · rw [List.mem_append] at separatorOrAfterMember
          rcases separatorOrAfterMember with
              separatorMember | afterMember
          · change
              letter ∈
                (segment.gap ++ segment.separator.toList) ++
                  renderExactCutSegments after
            exact
              List.mem_append_left _ <|
                List.mem_append_right _ separatorMember
          · change
              letter ∈
                (segment.gap ++ segment.separator.toList) ++
                  renderExactCutSegments after
            exact List.mem_append_right _ afterMember
      exact
        beforeSuffixDisjoint
          letter beforeMember rightInSuffix
    · have localLeftInGap : letter ∈ segment.gap := by
        rw [localCut.1]
        exact List.mem_append_left _ localLeftMember
      rcases globalRightMember with
          localRightMember | separatorOrAfterMember
      · exact
          localCut.2.2
            letter localLeftMember localRightMember
      · rw [List.mem_append] at separatorOrAfterMember
        rcases separatorOrAfterMember with
            separatorMember | afterMember
        · exact
            (exactCutDecomposition_gap_letter_not_separator
              segmentMember localLeftInGap) <|
              mem_exactCutSeparators_of_separator_toList
                segmentMember separatorMember
        · have localLeftInRender : letter ∈ segment.render := by
            change
              letter ∈
                segment.gap ++ segment.separator.toList
            exact
              List.mem_append_left _ localLeftInGap
          exact
            segmentAfterDisjoint
              letter localLeftInRender afterMember
  have globalCut :
      UniqueSeparatorFourExactCut letters
        (renderExactCutSegments before ++ left)
        separator
        (right ++
          (segment.separator.toList ++
            renderExactCutSegments after)) :=
    ⟨lettersShape, countOne, globalDisjoint⟩
  obtain
    ⟨emittedBefore, emittedSegment, emittedAfter,
      emittedShape, emittedSeparatorEq, _, _⟩ :=
    exactCutDecomposition_exactCut_iff.mp globalCut
  have emittedMember :
      emittedSegment ∈ exactCutDecomposition letters := by
    rw [emittedShape]
    simp
  have separatorEmitted :
      separator ∈
        exactCutSeparators
          (exactCutDecomposition letters) :=
    mem_exactCutSeparators_of_separator_eq
      emittedMember emittedSeparatorEq
  exact
    (exactCutDecomposition_gap_letter_not_separator
      segmentMember separatorMemberGap)
      separatorEmitted

/-- Existential separator-free form for every retained decomposition gap. -/
theorem exactCutDecomposition_gap_no_exactCut
    {letters : List Nat} {segment : ExactCutSegment}
    (segmentMember :
      segment ∈ exactCutDecomposition letters) :
    ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut
          segment.gap left separator right := by
  rintro ⟨left, separator, right, cut⟩
  exact
    exactCutDecomposition_gap_not_exactCut
      segmentMember cut

private theorem connectedComponent_pairwise_flatten_append_disjoint
    {before after : List (List Nat)}
    (pairwise :
      (before ++ after).Pairwise
        ConnectedComponentSupportsDisjoint) :
    ConnectedComponentSupportsDisjoint
      before.flatten after.flatten := by
  have cross :=
    (List.pairwise_append.mp pairwise).2.2
  intro letter beforeMember afterMember
  rw [List.mem_flatten] at beforeMember afterMember
  rcases beforeMember with
    ⟨left, leftMember, letterInLeft⟩
  rcases afterMember with
    ⟨right, rightMember, letterInRight⟩
  exact
    (cross left leftMember right rightMember)
      letter letterInLeft letterInRight

private theorem connectedComponentDecomposeList_singleton_exactCut
    {gap : List Nat} {before after : List (List Nat)}
    {separator : Nat}
    (decompositionEq :
      connectedComponentDecomposeList gap =
        before ++ [separator] :: after) :
    UniqueSeparatorFourExactCut gap
      before.flatten separator after.flatten := by
  have flattenEq :=
    connectedComponentDecomposeList_flatten gap
  rw [decompositionEq] at flattenEq
  have gapShape :
      gap = before.flatten ++ separator :: after.flatten := by
    simpa [List.append_assoc] using flattenEq.symm
  have pairwise :=
    connectedComponentDecomposeList_pairwiseDisjoint gap
  rw [decompositionEq] at pairwise
  have beforeSuffixDisjoint :
      ConnectedComponentSupportsDisjoint
        before.flatten
        ([separator] :: after).flatten :=
    connectedComponent_pairwise_flatten_append_disjoint
      (before := before)
      (after := [separator] :: after)
      pairwise
  have tailPairwise :
      ([separator] :: after).Pairwise
        ConnectedComponentSupportsDisjoint :=
    (List.pairwise_append.mp pairwise).2.1
  have singletonAfterDisjoint :
      ConnectedComponentSupportsDisjoint
        [[separator]].flatten after.flatten :=
    connectedComponent_pairwise_flatten_append_disjoint
      (before := [[separator]])
      (after := after)
      (by simpa using tailPairwise)
  have separatorNotBefore :
      separator ∉ before.flatten := by
    intro separatorBefore
    apply
      beforeSuffixDisjoint separator separatorBefore
    change separator ∈ [separator] ++ after.flatten
    simp
  have separatorNotAfter :
      separator ∉ after.flatten := by
    exact singletonAfterDisjoint separator (by simp)
  have beforeCountZero :
      before.flatten.count separator = 0 :=
    List.count_eq_zero.mpr separatorNotBefore
  have afterCountZero :
      after.flatten.count separator = 0 :=
    List.count_eq_zero.mpr separatorNotAfter
  have countOne : gap.count separator = 1 := by
    rw [gapShape, List.count_append, List.count_cons_self,
      beforeCountZero, afterCountZero]
  have disjoint :
      UniqueSeparatorFourSupportsDisjoint
        before.flatten after.flatten := by
    intro letter beforeMember afterMember
    apply beforeSuffixDisjoint letter beforeMember
    change letter ∈ [separator] ++ after.flatten
    exact List.mem_append_right _ afterMember
  exact ⟨gapShape, countOne, disjoint⟩

/-- If a list has no exact separator cut, none of its deterministic support
components can be a singleton. -/
theorem connectedComponentDecomposeList_component_length_ge_two_of_no_exactCut
    {gap component : List Nat}
    (noExactCut :
      ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut
          gap left separator right)
    (componentMember :
      component ∈ connectedComponentDecomposeList gap) :
    2 ≤ component.length := by
  by_cases lengthAtLeastTwo : 2 ≤ component.length
  · exact lengthAtLeastTwo
  · have componentNonempty :
        component ≠ [] :=
      connectedComponentDecomposeList_nonempty_components
        gap component componentMember
    have componentPositive : 0 < component.length :=
      List.length_pos_iff.mpr componentNonempty
    have componentLengthOne : component.length = 1 := by
      omega
    obtain ⟨separator, componentEq⟩ :=
      List.length_eq_one_iff.mp componentLengthOne
    obtain ⟨before, after, decompositionEq⟩ :=
      List.mem_iff_append.mp componentMember
    have localCut :
        UniqueSeparatorFourExactCut gap
          before.flatten separator after.flatten := by
      apply connectedComponentDecomposeList_singleton_exactCut
      simpa [componentEq] using decompositionEq
    exact False.elim <|
      noExactCut
        ⟨before.flatten, separator, after.flatten, localCut⟩

/-- Quantified form of the lower bound for all support components. -/
theorem connectedComponentDecomposeList_components_length_ge_two_of_no_exactCut
    {gap : List Nat}
    (noExactCut :
      ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut
          gap left separator right) :
    ∀ component ∈ connectedComponentDecomposeList gap,
      2 ≤ component.length := by
  intro component componentMember
  exact
    connectedComponentDecomposeList_component_length_ge_two_of_no_exactCut
      noExactCut componentMember

/-- Every support component inside an exact-cut decomposition gap has length
at least two. -/
theorem exactCutDecomposition_gap_component_length_ge_two
    {letters : List Nat} {segment : ExactCutSegment}
    {component : List Nat}
    (segmentMember :
      segment ∈ exactCutDecomposition letters)
    (componentMember :
      component ∈
        connectedComponentDecomposeList segment.gap) :
    2 ≤ component.length :=
  connectedComponentDecomposeList_component_length_ge_two_of_no_exactCut
    (exactCutDecomposition_gap_no_exactCut segmentMember)
    componentMember

end SemigroupBasis.CoRoots.S5_441
