import SemigroupBasis.CoRoots.Order6SporadicSection27F9BlockSupport
import SemigroupBasis.CoRoots.Order6SporadicSection27BetaWitnesses

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27

open SemigroupBasis.CoRoots.S5_870

/-! ## Prefix bookkeeping for sparse gap blocks -/

/-- The reverse marker accumulator after scanning a block prefix. -/
def seenAfterGapBlocks
    (seen : List Nat) (blocks : List FirstOccurrenceGapBlock) : List Nat :=
  (gapBlockMarkers blocks).reverse ++ seen

@[simp]
theorem seenAfterGapBlocks_nil (seen : List Nat) :
    seenAfterGapBlocks seen [] = seen := by
  simp [seenAfterGapBlocks, gapBlockMarkers]

@[simp]
theorem seenAfterGapBlocks_cons
    (seen : List Nat) (block : FirstOccurrenceGapBlock)
    (rest : List FirstOccurrenceGapBlock) :
    seenAfterGapBlocks seen (block :: rest) =
      seenAfterGapBlocks (block.marker :: seen) rest := by
  simp [seenAfterGapBlocks, gapBlockMarkers, List.append_assoc]

@[simp]
theorem seenAfterGapBlocks_append
    (seen : List Nat) (left right : List FirstOccurrenceGapBlock) :
    seenAfterGapBlocks seen (left ++ right) =
      seenAfterGapBlocks (seenAfterGapBlocks seen left) right := by
  simp [seenAfterGapBlocks, gapBlockMarkers, List.reverse_append,
    List.append_assoc]

@[simp]
theorem renderGapBlocks_append
    (left right : List FirstOccurrenceGapBlock) :
    renderGapBlocks (left ++ right) =
      renderGapBlocks left ++ renderGapBlocks right := by
  induction left with
  | nil => rfl
  | cons block rest induction =>
      simp [renderGapBlocks, induction, List.append_assoc]

@[simp]
theorem gapBlockMarkers_append
    (left right : List FirstOccurrenceGapBlock) :
    gapBlockMarkers (left ++ right) =
      gapBlockMarkers left ++ gapBlockMarkers right := by
  simp [gapBlockMarkers]

/-- Invert one sparse-block constructor without exposing proof-term details. -/
theorem SparseBlocks.cons_inv
    {seen : List Nat} {block : FirstOccurrenceGapBlock}
    {rest : List FirstOccurrenceGapBlock}
    (sparse : SparseBlocks seen (block :: rest)) :
    block.marker ∉ seen ∧
      ChoiceIn (block.marker :: seen) block.seconds ∧
      SparseBlocks (block.marker :: seen) rest := by
  cases sparse with
  | cons _ _ _ markerFresh choice tail =>
      exact ⟨markerFresh, choice, tail⟩

/-- Sparse blocks concatenate when the suffix uses the accumulator produced by
the prefix. -/
theorem SparseBlocks.append
    {seen : List Nat} {prefixBlocks suffix : List FirstOccurrenceGapBlock}
    (prefixSparse : SparseBlocks seen prefixBlocks)
    (suffixSparse :
      SparseBlocks (seenAfterGapBlocks seen prefixBlocks) suffix) :
    SparseBlocks seen (prefixBlocks ++ suffix) := by
  induction prefixSparse generalizing suffix with
  | nil seen =>
      simpa using suffixSparse
  | cons seen block rest markerFresh choice tail induction =>
      apply SparseBlocks.cons seen block (rest ++ suffix)
        markerFresh choice
      apply induction
      simpa using suffixSparse

/-- Invert sparsity across an arbitrary block-prefix split. -/
theorem SparseBlocks.split
    {seen : List Nat} {prefixBlocks suffix : List FirstOccurrenceGapBlock}
    (sparse : SparseBlocks seen (prefixBlocks ++ suffix)) :
    SparseBlocks seen prefixBlocks ∧
      SparseBlocks (seenAfterGapBlocks seen prefixBlocks) suffix := by
  induction prefixBlocks generalizing seen with
  | nil =>
      exact ⟨SparseBlocks.nil seen, by simpa using sparse⟩
  | cons block rest induction =>
      have head := sparse.cons_inv
      obtain ⟨restPrefix, suffixSparse⟩ := induction head.2.2
      constructor
      · exact SparseBlocks.cons seen block rest
          head.1 head.2.1 restPrefix
      · simpa using suffixSparse

private theorem gapBlock_eq
    (left right : FirstOccurrenceGapBlock)
    (marker : left.marker = right.marker)
    (seconds : left.seconds = right.seconds) :
    left = right := by
  cases left
  cases right
  simp_all

/-! ## Least differing block -/

/-- Pure list shape of the first block at which two equal-marker block lists
differ. -/
structure LeastDifferingBlockShape
    (leftBlocks rightBlocks : List FirstOccurrenceGapBlock) where
  commonPrefix : List FirstOccurrenceGapBlock
  leftBlock : FirstOccurrenceGapBlock
  rightBlock : FirstOccurrenceGapBlock
  leftTail : List FirstOccurrenceGapBlock
  rightTail : List FirstOccurrenceGapBlock
  left_eq :
    leftBlocks = commonPrefix ++ leftBlock :: leftTail
  right_eq :
    rightBlocks = commonPrefix ++ rightBlock :: rightTail
  sameMarker : leftBlock.marker = rightBlock.marker
  differentSeconds : leftBlock.seconds ≠ rightBlock.seconds
  tailMarkers_eq :
    gapBlockMarkers leftTail = gapBlockMarkers rightTail

private theorem exists_leastDifferingBlockShape :
    ∀ (leftBlocks rightBlocks : List FirstOccurrenceGapBlock),
      gapBlockMarkers leftBlocks = gapBlockMarkers rightBlocks →
      leftBlocks ≠ rightBlocks →
      Nonempty (LeastDifferingBlockShape leftBlocks rightBlocks)
  | [], [], _, different =>
      False.elim (different rfl)
  | [], _ :: _, markerSequence, _ => by
      simp [gapBlockMarkers] at markerSequence
  | _ :: _, [], markerSequence, _ => by
      simp [gapBlockMarkers] at markerSequence
  | leftBlock :: leftTail, rightBlock :: rightTail,
      markerSequence, different => by
      simp only [gapBlockMarkers, List.map_cons,
        FirstOccurrenceGapBlock.marker] at markerSequence
      have sameMarker : leftBlock.marker = rightBlock.marker :=
        (List.cons.inj markerSequence).1
      have tailMarkers :
          gapBlockMarkers leftTail = gapBlockMarkers rightTail :=
        (List.cons.inj markerSequence).2
      by_cases sameSeconds : leftBlock.seconds = rightBlock.seconds
      · have sameBlock :=
          gapBlock_eq leftBlock rightBlock sameMarker sameSeconds
        subst rightBlock
        have differentTail : leftTail ≠ rightTail := by
          intro equalTail
          exact different (congrArg (List.cons leftBlock) equalTail)
        obtain ⟨inner⟩ :=
          exists_leastDifferingBlockShape
            leftTail rightTail tailMarkers differentTail
        exact ⟨{
          commonPrefix := leftBlock :: inner.commonPrefix
          leftBlock := inner.leftBlock
          rightBlock := inner.rightBlock
          leftTail := inner.leftTail
          rightTail := inner.rightTail
          left_eq := by
            simpa using congrArg (List.cons leftBlock) inner.left_eq
          right_eq := by
            simpa using congrArg (List.cons leftBlock) inner.right_eq
          sameMarker := inner.sameMarker
          differentSeconds := inner.differentSeconds
          tailMarkers_eq := inner.tailMarkers_eq
        }⟩
      · exact ⟨{
          commonPrefix := []
          leftBlock := leftBlock
          rightBlock := rightBlock
          leftTail := leftTail
          rightTail := rightTail
          left_eq := rfl
          right_eq := rfl
          sameMarker := sameMarker
          differentSeconds := sameSeconds
          tailMarkers_eq := tailMarkers
        }⟩

/-- Least-difference shape together with the exact sparse prefix/head/tail
inversions on both sides.  Both choices are indexed by the same normalized
current-marker accumulator. -/
structure LeastDifferingSparseBlocks
    (seen : List Nat)
    (leftBlocks rightBlocks : List FirstOccurrenceGapBlock) where
  commonPrefix : List FirstOccurrenceGapBlock
  leftBlock : FirstOccurrenceGapBlock
  rightBlock : FirstOccurrenceGapBlock
  leftTail : List FirstOccurrenceGapBlock
  rightTail : List FirstOccurrenceGapBlock
  left_eq :
    leftBlocks = commonPrefix ++ leftBlock :: leftTail
  right_eq :
    rightBlocks = commonPrefix ++ rightBlock :: rightTail
  sameMarker : leftBlock.marker = rightBlock.marker
  differentSeconds : leftBlock.seconds ≠ rightBlock.seconds
  tailMarkers_eq :
    gapBlockMarkers leftTail = gapBlockMarkers rightTail
  leftPrefixSparse : SparseBlocks seen commonPrefix
  rightPrefixSparse : SparseBlocks seen commonPrefix
  markerFresh :
    leftBlock.marker ∉ seenAfterGapBlocks seen commonPrefix
  leftChoice :
    ChoiceIn
      (leftBlock.marker :: seenAfterGapBlocks seen commonPrefix)
      leftBlock.seconds
  rightChoice :
    ChoiceIn
      (leftBlock.marker :: seenAfterGapBlocks seen commonPrefix)
      rightBlock.seconds
  leftTailSparse :
    SparseBlocks
      (leftBlock.marker :: seenAfterGapBlocks seen commonPrefix)
      leftTail
  rightTailSparse :
    SparseBlocks
      (leftBlock.marker :: seenAfterGapBlocks seen commonPrefix)
      rightTail

/-- Equal marker lists and unequal sparse block lists have a first differing
block, with all sparse indices inverted at the common prefix. -/
theorem exists_leastDifferingSparseBlocks
    {seen : List Nat}
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (leftSparse : SparseBlocks seen leftBlocks)
    (rightSparse : SparseBlocks seen rightBlocks)
    (sameMarkers :
      gapBlockMarkers leftBlocks = gapBlockMarkers rightBlocks)
    (different : leftBlocks ≠ rightBlocks) :
    Nonempty (LeastDifferingSparseBlocks seen leftBlocks rightBlocks) := by
  obtain ⟨shape⟩ :=
    exists_leastDifferingBlockShape
      leftBlocks rightBlocks sameMarkers different
  have leftWhole :
      SparseBlocks seen
        (shape.commonPrefix ++ shape.leftBlock :: shape.leftTail) := by
    rw [← shape.left_eq]
    exact leftSparse
  have rightWhole :
      SparseBlocks seen
        (shape.commonPrefix ++ shape.rightBlock :: shape.rightTail) := by
    rw [← shape.right_eq]
    exact rightSparse
  obtain ⟨leftPrefixSparse, leftCurrentSparse⟩ := leftWhole.split
  obtain ⟨rightPrefixSparse, rightCurrentSparse⟩ := rightWhole.split
  have leftHead := leftCurrentSparse.cons_inv
  have rightHead := rightCurrentSparse.cons_inv
  have rightChoice :
      ChoiceIn
        (shape.leftBlock.marker ::
          seenAfterGapBlocks seen shape.commonPrefix)
        shape.rightBlock.seconds := by
    simpa only [shape.sameMarker] using rightHead.2.1
  have rightTailSparse :
      SparseBlocks
        (shape.leftBlock.marker ::
          seenAfterGapBlocks seen shape.commonPrefix)
        shape.rightTail := by
    simpa only [shape.sameMarker] using rightHead.2.2
  exact ⟨{
    commonPrefix := shape.commonPrefix
    leftBlock := shape.leftBlock
    rightBlock := shape.rightBlock
    leftTail := shape.leftTail
    rightTail := shape.rightTail
    left_eq := shape.left_eq
    right_eq := shape.right_eq
    sameMarker := shape.sameMarker
    differentSeconds := shape.differentSeconds
    tailMarkers_eq := shape.tailMarkers_eq
    leftPrefixSparse := leftPrefixSparse
    rightPrefixSparse := rightPrefixSparse
    markerFresh := leftHead.1
    leftChoice := leftHead.2.1
    rightChoice := rightChoice
    leftTailSparse := leftHead.2.2
    rightTailSparse := rightTailSparse
  }⟩

namespace LeastDifferingSparseBlocks

/-- The literal word prefix through the common current marker. -/
def renderedPrefix
    {seen : List Nat}
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference :
      LeastDifferingSparseBlocks seen leftBlocks rightBlocks) : List Nat :=
  renderGapBlocks difference.commonPrefix ++ [difference.leftBlock.marker]

theorem left_render_eq
    {seen : List Nat}
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference :
      LeastDifferingSparseBlocks seen leftBlocks rightBlocks) :
    renderGapBlocks leftBlocks =
      difference.renderedPrefix ++ difference.leftBlock.seconds ++
        renderGapBlocks difference.leftTail := by
  calc
    renderGapBlocks leftBlocks =
        renderGapBlocks
          (difference.commonPrefix ++
            difference.leftBlock :: difference.leftTail) :=
      congrArg renderGapBlocks difference.left_eq
    _ = difference.renderedPrefix ++ difference.leftBlock.seconds ++
          renderGapBlocks difference.leftTail := by
      simp [renderedPrefix, renderGapBlocks, List.append_assoc]

theorem right_render_eq
    {seen : List Nat}
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference :
      LeastDifferingSparseBlocks seen leftBlocks rightBlocks) :
    renderGapBlocks rightBlocks =
      difference.renderedPrefix ++ difference.rightBlock.seconds ++
        renderGapBlocks difference.rightTail := by
  calc
    renderGapBlocks rightBlocks =
        renderGapBlocks
          (difference.commonPrefix ++
            difference.rightBlock :: difference.rightTail) :=
      congrArg renderGapBlocks difference.right_eq
    _ = difference.renderedPrefix ++ difference.rightBlock.seconds ++
          renderGapBlocks difference.rightTail := by
      simp [renderedPrefix, renderGapBlocks, difference.sameMarker,
        List.append_assoc]

theorem left_markerSequence_eq
    {seen : List Nat}
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference :
      LeastDifferingSparseBlocks seen leftBlocks rightBlocks) :
    gapBlockMarkers leftBlocks =
      gapBlockMarkers difference.commonPrefix ++
        difference.leftBlock.marker ::
          gapBlockMarkers difference.leftTail := by
  simpa [gapBlockMarkers] using
    congrArg gapBlockMarkers difference.left_eq

theorem right_markerSequence_eq
    {seen : List Nat}
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference :
      LeastDifferingSparseBlocks seen leftBlocks rightBlocks) :
    gapBlockMarkers rightBlocks =
      gapBlockMarkers difference.commonPrefix ++
        difference.rightBlock.marker ::
          gapBlockMarkers difference.rightTail := by
  simpa [gapBlockMarkers] using
    congrArg gapBlockMarkers difference.right_eq

end LeastDifferingSparseBlocks

/-! ## The three oriented paper cases -/

/-- After possibly swapping the two words, unequal sparse choices at the least
differing block have exactly the three forms used in Proposition 27.3. -/
inductive OrientedChoiceDifference
    (markers : List Nat) (current : Nat) :
    List Nat → List Nat → Prop
  | selectedEmpty (selected : Nat)
      (atOrBefore :
        selected = current ∨ EarlierIn markers selected current) :
      OrientedChoiceDifference markers current [selected] []
  | selectedCurrent (selected : Nat)
      (beforeCurrent : EarlierIn markers selected current) :
      OrientedChoiceDifference markers current [selected] [current]
  | orderedSelected (earlier later : Nat)
      (earlierBeforeLater : EarlierIn markers earlier later)
      (laterBeforeCurrent : EarlierIn markers later current) :
      OrientedChoiceDifference markers current [earlier] [later]

private theorem earlierIn_append_right
    {markers : List Nat} {earlier later : Nat}
    (order : EarlierIn markers earlier later) (suffix : List Nat) :
    EarlierIn (markers ++ suffix) earlier later := by
  obtain ⟨before, middle, after, shape⟩ := order
  refine ⟨before, middle, after ++ suffix, ?_⟩
  rw [shape]
  simp [List.append_assoc]

private theorem earlierIn_current_of_mem_prefix
    {markerPrefix suffix : List Nat} {selected current : Nat}
    (member : selected ∈ markerPrefix) :
    EarlierIn (markerPrefix ++ current :: suffix) selected current := by
  obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp member
  refine ⟨before, after, suffix, ?_⟩
  rw [shape]

private theorem earlierIn_or_reverse_of_mem
    {markers : List Nat} {left right : Nat}
    (leftMember : left ∈ markers) (rightMember : right ∈ markers)
    (different : left ≠ right) :
    EarlierIn markers left right ∨ EarlierIn markers right left := by
  obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp leftMember
  have rightSide : right ∈ before ∨ right ∈ after := by
    rw [shape] at rightMember
    rcases List.mem_append.mp rightMember with inBefore | inCurrentAfter
    · exact Or.inl inBefore
    · rcases List.mem_cons.mp inCurrentAfter with atCurrent | inAfter
      · exact False.elim (different atCurrent.symm)
      · exact Or.inr inAfter
  rcases rightSide with inBefore | inAfter
  · obtain ⟨prior, middle, beforeShape⟩ :=
      List.mem_iff_append.mp inBefore
    apply Or.inr
    refine ⟨prior, middle, after, ?_⟩
    rw [shape, beforeShape]
  · obtain ⟨middle, trailing, afterShape⟩ :=
      List.mem_iff_append.mp inAfter
    apply Or.inl
    refine ⟨before, middle, trailing, ?_⟩
    rw [shape, afterShape]
    simp [List.append_assoc]

private theorem LeastDifferingSparseBlocks.selected_mem_prefixMarkers
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference : LeastDifferingSparseBlocks [] leftBlocks rightBlocks)
    {selected : Nat}
    (seenMember :
      selected ∈ seenAfterGapBlocks [] difference.commonPrefix) :
    selected ∈ gapBlockMarkers difference.commonPrefix := by
  simpa [seenAfterGapBlocks] using seenMember

private theorem LeastDifferingSparseBlocks.selectedAtOrBeforeCurrent
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference : LeastDifferingSparseBlocks [] leftBlocks rightBlocks)
    {selected : Nat}
    (allowed :
      selected ∈
        difference.leftBlock.marker ::
          seenAfterGapBlocks [] difference.commonPrefix) :
    selected = difference.leftBlock.marker ∨
      EarlierIn (gapBlockMarkers leftBlocks)
        selected difference.leftBlock.marker := by
  rcases List.mem_cons.mp allowed with atCurrent | inSeen
  · exact Or.inl atCurrent
  · apply Or.inr
    have inPrefix := difference.selected_mem_prefixMarkers inSeen
    rw [difference.left_markerSequence_eq]
    exact earlierIn_current_of_mem_prefix inPrefix

/-- Classify the unequal choices in a least-difference certificate into the
three oriented cases, returning the reverse orientation when symmetry is
required. -/
theorem LeastDifferingSparseBlocks.orientedChoiceDifference
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference : LeastDifferingSparseBlocks [] leftBlocks rightBlocks) :
    OrientedChoiceDifference
        (gapBlockMarkers leftBlocks) difference.leftBlock.marker
        difference.leftBlock.seconds difference.rightBlock.seconds ∨
      OrientedChoiceDifference
        (gapBlockMarkers leftBlocks) difference.leftBlock.marker
        difference.rightBlock.seconds difference.leftBlock.seconds := by
  rcases difference.leftChoice with leftEmpty |
      ⟨leftSelected, leftAllowed, leftShape⟩
  · rcases difference.rightChoice with rightEmpty |
        ⟨rightSelected, rightAllowed, rightShape⟩
    · exact False.elim <| difference.differentSeconds <|
        leftEmpty.trans rightEmpty.symm
    · have bound :=
        difference.selectedAtOrBeforeCurrent rightAllowed
      have oriented :
          OrientedChoiceDifference
            (gapBlockMarkers leftBlocks) difference.leftBlock.marker
            [rightSelected] [] :=
        OrientedChoiceDifference.selectedEmpty rightSelected bound
      exact Or.inr <| by
        simpa [rightShape, leftEmpty] using oriented
  · rcases difference.rightChoice with rightEmpty |
        ⟨rightSelected, rightAllowed, rightShape⟩
    · have bound :=
        difference.selectedAtOrBeforeCurrent leftAllowed
      have oriented :
          OrientedChoiceDifference
            (gapBlockMarkers leftBlocks) difference.leftBlock.marker
            [leftSelected] [] :=
        OrientedChoiceDifference.selectedEmpty leftSelected bound
      exact Or.inl <| by
        simpa [leftShape, rightEmpty] using oriented
    · have selectedDifferent : leftSelected ≠ rightSelected := by
        intro equal
        apply difference.differentSeconds
        simpa [leftShape, rightShape, equal]
      by_cases leftCurrent :
          leftSelected = difference.leftBlock.marker
      · by_cases rightCurrent :
            rightSelected = difference.leftBlock.marker
        · exact False.elim <| selectedDifferent <|
            leftCurrent.trans rightCurrent.symm
        · have rightBefore :=
            (difference.selectedAtOrBeforeCurrent rightAllowed).resolve_left
              rightCurrent
          have oriented :
              OrientedChoiceDifference
                (gapBlockMarkers leftBlocks) difference.leftBlock.marker
                [rightSelected] [difference.leftBlock.marker] :=
            OrientedChoiceDifference.selectedCurrent
              rightSelected rightBefore
          exact Or.inr <| by
            simpa [rightShape, leftShape, leftCurrent] using oriented
      · by_cases rightCurrent :
            rightSelected = difference.leftBlock.marker
        · have leftBefore :=
            (difference.selectedAtOrBeforeCurrent leftAllowed).resolve_left
              leftCurrent
          have oriented :
              OrientedChoiceDifference
                (gapBlockMarkers leftBlocks) difference.leftBlock.marker
                [leftSelected] [difference.leftBlock.marker] :=
            OrientedChoiceDifference.selectedCurrent
              leftSelected leftBefore
          exact Or.inl <| by
            simpa [leftShape, rightShape, rightCurrent] using oriented
        · have leftSeen :
              leftSelected ∈
                seenAfterGapBlocks [] difference.commonPrefix :=
            (List.mem_cons.mp leftAllowed).resolve_left leftCurrent
          have rightSeen :
              rightSelected ∈
                seenAfterGapBlocks [] difference.commonPrefix :=
            (List.mem_cons.mp rightAllowed).resolve_left rightCurrent
          have leftPrefix :=
            difference.selected_mem_prefixMarkers leftSeen
          have rightPrefix :=
            difference.selected_mem_prefixMarkers rightSeen
          have pairOrder :=
            earlierIn_or_reverse_of_mem
              leftPrefix rightPrefix selectedDifferent
          rcases pairOrder with leftBeforeRight | rightBeforeLeft
          · have leftRightFull :
                EarlierIn (gapBlockMarkers leftBlocks)
                  leftSelected rightSelected := by
              rw [difference.left_markerSequence_eq]
              exact earlierIn_append_right leftBeforeRight
                (difference.leftBlock.marker ::
                  gapBlockMarkers difference.leftTail)
            have rightBeforeCurrent :=
              (difference.selectedAtOrBeforeCurrent rightAllowed).resolve_left
                rightCurrent
            have oriented :
                OrientedChoiceDifference
                  (gapBlockMarkers leftBlocks) difference.leftBlock.marker
                  [leftSelected] [rightSelected] :=
              OrientedChoiceDifference.orderedSelected
                leftSelected rightSelected leftRightFull rightBeforeCurrent
            exact Or.inl <| by
              simpa [leftShape, rightShape] using oriented
          · have rightLeftFull :
                EarlierIn (gapBlockMarkers leftBlocks)
                  rightSelected leftSelected := by
              rw [difference.left_markerSequence_eq]
              exact earlierIn_append_right rightBeforeLeft
                (difference.leftBlock.marker ::
                  gapBlockMarkers difference.leftTail)
            have leftBeforeCurrent :=
              (difference.selectedAtOrBeforeCurrent leftAllowed).resolve_left
                leftCurrent
            have oriented :
                OrientedChoiceDifference
                  (gapBlockMarkers leftBlocks) difference.leftBlock.marker
                  [rightSelected] [leftSelected] :=
              OrientedChoiceDifference.orderedSelected
                rightSelected leftSelected rightLeftFull leftBeforeCurrent
            exact Or.inr <| by
              simpa [leftShape, rightShape] using oriented

/-! ## Ordered rendered-prefix split for Case 3 -/

/-- The exact rendered-prefix decomposition used in the third paper case.
`firstZone` is represented literally as `before ++ earlier :: between` so the
absence and chronology fields can feed the generic F9 crossing frame without
any further block reasoning. -/
structure OrderedRenderedPrefixSplit
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference : LeastDifferingSparseBlocks [] leftBlocks rightBlocks)
    (earlier later : Nat) where
  before : List Nat
  between : List Nat
  after : List Nat
  render_eq :
    renderGapBlocks difference.commonPrefix =
      before ++ earlier :: between ++ later :: after
  earlier_not_mem_before : earlier ∉ before
  later_not_mem_firstZone : later ∉ before ++ earlier :: between
  firstZone_chronology :
    ∀ letter, letter ∈ before ++ earlier :: between →
      EarlierIn (gapBlockMarkers leftBlocks) letter later

private theorem choiceIn_member
    {allowed seconds : List Nat}
    (choice : ChoiceIn allowed seconds) :
    ∀ {letter}, letter ∈ seconds → letter ∈ allowed := by
  intro letter member
  rcases choice with empty | ⟨selected, selectedAllowed, shape⟩
  · simp [empty] at member
  · rw [shape] at member
    have equal : letter = selected := by
      simpa only [List.mem_singleton] using member
    subst letter
    exact selectedAllowed

private theorem LeastDifferingSparseBlocks.leftSparse
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference : LeastDifferingSparseBlocks [] leftBlocks rightBlocks) :
    SparseBlocks [] leftBlocks := by
  rw [difference.left_eq]
  apply difference.leftPrefixSparse.append
  exact SparseBlocks.cons
    (seenAfterGapBlocks [] difference.commonPrefix)
    difference.leftBlock difference.leftTail difference.markerFresh
    difference.leftChoice difference.leftTailSparse

/-- Extract the first-occurrence block split behind an oriented Case-3 pair.
The two shape equalities and two strict orders are precisely the payload of
`OrientedChoiceDifference.orderedSelected`. -/
theorem LeastDifferingSparseBlocks.orderedRenderedPrefixSplit
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference : LeastDifferingSparseBlocks [] leftBlocks rightBlocks)
    {earlier later : Nat}
    (leftSeconds : difference.leftBlock.seconds = [earlier])
    (rightSeconds : difference.rightBlock.seconds = [later])
    (earlierBeforeLater :
      EarlierIn (gapBlockMarkers leftBlocks) earlier later)
    (laterBeforeCurrent :
      EarlierIn (gapBlockMarkers leftBlocks)
        later difference.leftBlock.marker) :
    Nonempty (OrderedRenderedPrefixSplit difference earlier later) := by
  have fullSparse := difference.leftSparse
  have markersNodup := fullSparse.markersNodup
  have earlierAllowed :
      earlier ∈
        difference.leftBlock.marker ::
          seenAfterGapBlocks [] difference.commonPrefix := by
    apply choiceIn_member difference.leftChoice
    simp [leftSeconds]
  have laterAllowed :
      later ∈
        difference.leftBlock.marker ::
          seenAfterGapBlocks [] difference.commonPrefix := by
    apply choiceIn_member difference.rightChoice
    simp [rightSeconds]
  have earlierRank := earlierBeforeLater.idxOf_lt markersNodup
  have laterRank := laterBeforeCurrent.idxOf_lt markersNodup
  have earlierNeLater : earlier ≠ later := by
    intro equal
    rw [equal] at earlierRank
    exact Nat.lt_irrefl _ earlierRank
  have laterNeCurrent : later ≠ difference.leftBlock.marker := by
    intro equal
    rw [equal] at laterRank
    exact Nat.lt_irrefl _ laterRank
  have earlierNeCurrent : earlier ≠ difference.leftBlock.marker := by
    intro equal
    rw [equal] at earlierRank
    exact (Nat.not_lt_of_ge (Nat.le_of_lt laterRank)) earlierRank
  have earlierSeen :
      earlier ∈ seenAfterGapBlocks [] difference.commonPrefix :=
    (List.mem_cons.mp earlierAllowed).resolve_left earlierNeCurrent
  have laterSeen :
      later ∈ seenAfterGapBlocks [] difference.commonPrefix :=
    (List.mem_cons.mp laterAllowed).resolve_left laterNeCurrent
  have earlierPrefix :=
    difference.selected_mem_prefixMarkers earlierSeen
  have laterPrefix :=
    difference.selected_mem_prefixMarkers laterSeen
  have prefixOrder :
      EarlierIn (gapBlockMarkers difference.commonPrefix)
        earlier later := by
    rcases earlierIn_or_reverse_of_mem
        earlierPrefix laterPrefix earlierNeLater with
      forward | reverse
    · exact forward
    · have reverseFull :
          EarlierIn (gapBlockMarkers leftBlocks) later earlier := by
        rw [difference.left_markerSequence_eq]
        exact earlierIn_append_right reverse
          (difference.leftBlock.marker ::
            gapBlockMarkers difference.leftTail)
      have reverseRank := reverseFull.idxOf_lt markersNodup
      exact False.elim <| Nat.not_lt_of_ge
        (Nat.le_of_lt earlierRank) reverseRank
  obtain ⟨earlierBlock, earlierBlockMember, earlierMarker⟩ :=
    List.mem_map.mp earlierPrefix
  obtain ⟨beforeBlocks, afterEarlierBlocks, firstBlockShape⟩ :=
    List.mem_iff_append.mp earlierBlockMember
  have laterAfterEarlier :
      later ∈ gapBlockMarkers afterEarlierBlocks := by
    rw [firstBlockShape, gapBlockMarkers_append] at laterPrefix
    change
      later ∈
        gapBlockMarkers beforeBlocks ++
          earlierBlock.marker :: gapBlockMarkers afterEarlierBlocks at laterPrefix
    rcases List.mem_append.mp laterPrefix with inBefore | inCurrentAfter
    · have reversePrefix :
          EarlierIn (gapBlockMarkers difference.commonPrefix)
            later earlier := by
        rw [firstBlockShape, gapBlockMarkers_append]
        change
          EarlierIn
            (gapBlockMarkers beforeBlocks ++
              earlierBlock.marker :: gapBlockMarkers afterEarlierBlocks)
            later earlier
        rw [earlierMarker]
        exact earlierIn_current_of_mem_prefix inBefore
      have prefixNodup := difference.leftPrefixSparse.markersNodup
      have forwardRank := prefixOrder.idxOf_lt prefixNodup
      have reverseRank := reversePrefix.idxOf_lt prefixNodup
      exact False.elim <| Nat.not_lt_of_ge
        (Nat.le_of_lt forwardRank) reverseRank
    · rcases List.mem_cons.mp inCurrentAfter with atEarlier | inAfter
      · exact False.elim <| earlierNeLater <|
          earlierMarker.symm.trans atEarlier.symm
      · exact inAfter
  obtain ⟨laterBlock, laterBlockMember, laterMarker⟩ :=
    List.mem_map.mp laterAfterEarlier
  obtain ⟨betweenBlocks, afterBlocks, secondBlockShape⟩ :=
    List.mem_iff_append.mp laterBlockMember
  have commonPrefixShape :
      difference.commonPrefix =
        beforeBlocks ++
          (earlierBlock ::
            (betweenBlocks ++ (laterBlock :: afterBlocks))) := by
    calc
      difference.commonPrefix =
          beforeBlocks ++ earlierBlock :: afterEarlierBlocks :=
        firstBlockShape
      _ = beforeBlocks ++
            (earlierBlock ::
              (betweenBlocks ++ (laterBlock :: afterBlocks))) := by
        rw [secondBlockShape]
  let before := renderGapBlocks beforeBlocks
  let between :=
    earlierBlock.seconds ++ renderGapBlocks betweenBlocks
  let after := laterBlock.seconds ++ renderGapBlocks afterBlocks
  have commonFormed := difference.leftPrefixSparse.wellFormed
  have commonFormedShape :
      GapBlocksWellFormed []
        (beforeBlocks ++
          (earlierBlock ::
            (betweenBlocks ++ (laterBlock :: afterBlocks)))) := by
    rw [← commonPrefixShape]
    exact commonFormed
  have earlierAbsent : earlier ∉ before := by
    have absent :=
      F9BlockSupport.futureMarker_not_mem_renderGapBlocks
        (priorBlocks := beforeBlocks) (nextBlock := earlierBlock)
        (rest := betweenBlocks ++ (laterBlock :: afterBlocks))
        commonFormedShape
    simpa [before, earlierMarker] using absent
  have laterFormed :
      GapBlocksWellFormed []
        ((beforeBlocks ++ (earlierBlock :: betweenBlocks)) ++
          (laterBlock :: afterBlocks)) := by
    simpa [List.append_assoc] using commonFormedShape
  have laterAbsent : later ∉ before ++ earlier :: between := by
    have absent :=
      F9BlockSupport.futureMarker_not_mem_renderGapBlocks
        (priorBlocks := beforeBlocks ++ earlierBlock :: betweenBlocks)
        (nextBlock := laterBlock) (rest := afterBlocks) laterFormed
    simpa [before, between, renderGapBlocks, earlierMarker, laterMarker,
      List.append_assoc] using absent
  have chronology :
      ∀ letter, letter ∈ before ++ earlier :: between →
        EarlierIn (gapBlockMarkers leftBlocks) letter later := by
    intro letter member
    have renderedMember :
        letter ∈
          renderGapBlocks
            (beforeBlocks ++ earlierBlock :: betweenBlocks) := by
      simpa [before, between, renderGapBlocks, earlierMarker,
        List.append_assoc] using member
    have localOrder :=
      F9BlockSupport.earlierIn_of_mem_renderGapBlocks_prefix
        (earlier := letter) (later := laterBlock.marker)
        laterFormed renderedMember
        (by simp [gapBlockMarkers])
    have commonOrder :
        EarlierIn (gapBlockMarkers difference.commonPrefix)
          letter later := by
      rw [commonPrefixShape]
      simpa [List.append_assoc, laterMarker] using localOrder
    rw [difference.left_markerSequence_eq]
    exact earlierIn_append_right commonOrder
      (difference.leftBlock.marker ::
        gapBlockMarkers difference.leftTail)
  exact ⟨{
    before := before
    between := between
    after := after
    render_eq := by
      rw [commonPrefixShape]
      simp [before, between, after, renderGapBlocks, earlierMarker,
        laterMarker, List.append_assoc]
    earlier_not_mem_before := earlierAbsent
    later_not_mem_firstZone := laterAbsent
    firstZone_chronology := chronology
  }⟩

/-! ## Common successor or terminal-fresh boundary -/

/-- The tail after the least differing block is either terminal (so the paper
appends a common fresh marker) or begins on both sides with the same next fresh
marker.  The successor case includes the next sparse inversion. -/
inductive LeastDifferenceTailBoundary
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference : LeastDifferingSparseBlocks [] leftBlocks rightBlocks) : Type
  | needsFresh
      (leftTail_eq : difference.leftTail = [])
      (rightTail_eq : difference.rightTail = []) :
      LeastDifferenceTailBoundary difference
  | successor
      (leftNext rightNext : FirstOccurrenceGapBlock)
      (leftRest rightRest : List FirstOccurrenceGapBlock)
      (leftTail_eq : difference.leftTail = leftNext :: leftRest)
      (rightTail_eq : difference.rightTail = rightNext :: rightRest)
      (sameMarker : leftNext.marker = rightNext.marker)
      (markerFresh :
        leftNext.marker ∉
          difference.leftBlock.marker ::
            seenAfterGapBlocks [] difference.commonPrefix)
      (leftChoice :
        ChoiceIn
          (leftNext.marker :: difference.leftBlock.marker ::
            seenAfterGapBlocks [] difference.commonPrefix)
          leftNext.seconds)
      (rightChoice :
        ChoiceIn
          (leftNext.marker :: difference.leftBlock.marker ::
            seenAfterGapBlocks [] difference.commonPrefix)
          rightNext.seconds)
      (leftRestSparse :
        SparseBlocks
          (leftNext.marker :: difference.leftBlock.marker ::
            seenAfterGapBlocks [] difference.commonPrefix)
          leftRest)
      (rightRestSparse :
        SparseBlocks
          (leftNext.marker :: difference.leftBlock.marker ::
            seenAfterGapBlocks [] difference.commonPrefix)
          rightRest)
      (restMarkers_eq :
        gapBlockMarkers leftRest = gapBlockMarkers rightRest) :
      LeastDifferenceTailBoundary difference

theorem LeastDifferingSparseBlocks.tailBoundary
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference : LeastDifferingSparseBlocks [] leftBlocks rightBlocks) :
    Nonempty (LeastDifferenceTailBoundary difference) := by
  cases leftTailShape : difference.leftTail with
  | nil =>
      cases rightTailShape : difference.rightTail with
      | nil =>
          exact ⟨LeastDifferenceTailBoundary.needsFresh
            leftTailShape rightTailShape⟩
      | cons rightNext rightRest =>
          have markers := difference.tailMarkers_eq
          rw [leftTailShape, rightTailShape] at markers
          simp [gapBlockMarkers] at markers
  | cons leftNext leftRest =>
      cases rightTailShape : difference.rightTail with
      | nil =>
          have markers := difference.tailMarkers_eq
          rw [leftTailShape, rightTailShape] at markers
          simp [gapBlockMarkers] at markers
      | cons rightNext rightRest =>
          have markers := difference.tailMarkers_eq
          rw [leftTailShape, rightTailShape] at markers
          simp only [gapBlockMarkers, List.map_cons,
            FirstOccurrenceGapBlock.marker] at markers
          have sameMarker : leftNext.marker = rightNext.marker :=
            (List.cons.inj markers).1
          have restMarkers :
              gapBlockMarkers leftRest = gapBlockMarkers rightRest :=
            (List.cons.inj markers).2
          have leftSparse := difference.leftTailSparse
          rw [leftTailShape] at leftSparse
          have rightSparse := difference.rightTailSparse
          rw [rightTailShape] at rightSparse
          have leftHead := leftSparse.cons_inv
          have rightHead := rightSparse.cons_inv
          have rightChoice :
              ChoiceIn
                (leftNext.marker :: difference.leftBlock.marker ::
                  seenAfterGapBlocks [] difference.commonPrefix)
                rightNext.seconds := by
            simpa only [sameMarker] using rightHead.2.1
          have rightRestSparse :
              SparseBlocks
                (leftNext.marker :: difference.leftBlock.marker ::
                  seenAfterGapBlocks [] difference.commonPrefix)
                rightRest := by
            simpa only [sameMarker] using rightHead.2.2
          exact ⟨LeastDifferenceTailBoundary.successor
            leftNext rightNext leftRest rightRest
            leftTailShape rightTailShape sameMarker leftHead.1
            leftHead.2.1 rightChoice leftHead.2.2 rightRestSparse
            restMarkers⟩

/-! ## Canonical packaging -/

/-- Least-difference sparse data plus the four global canonical obstructions
needed by the F9 separator extraction. -/
structure LeastDifferingBetaBlocks
    (leftBlocks rightBlocks : List FirstOccurrenceGapBlock) where
  difference : LeastDifferingSparseBlocks [] leftBlocks rightBlocks
  leftNoCrossing :
    ¬ Has27Crossing
      (gapBlockMarkers leftBlocks) (renderGapBlocks leftBlocks)
  leftNoAdjacentPair :
    ¬ Has27AdjacentPair
      (gapBlockMarkers leftBlocks) (renderGapBlocks leftBlocks)
  rightNoCrossing :
    ¬ Has27Crossing
      (gapBlockMarkers rightBlocks) (renderGapBlocks rightBlocks)
  rightNoAdjacentPair :
    ¬ Has27AdjacentPair
      (gapBlockMarkers rightBlocks) (renderGapBlocks rightBlocks)

/-- Two distinct beta-canonical block lists with the same marker list expose
all least-difference and canonical inversion data required by F9. -/
theorem exists_leastDifferingBetaBlocks
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (leftCanonical : BetaCanonicalBlocks leftBlocks)
    (rightCanonical : BetaCanonicalBlocks rightBlocks)
    (sameMarkers :
      gapBlockMarkers leftBlocks = gapBlockMarkers rightBlocks)
    (different : leftBlocks ≠ rightBlocks) :
    Nonempty (LeastDifferingBetaBlocks leftBlocks rightBlocks) := by
  obtain ⟨difference⟩ :=
    exists_leastDifferingSparseBlocks
      leftCanonical.sparse rightCanonical.sparse sameMarkers different
  exact ⟨{
    difference := difference
    leftNoCrossing := leftCanonical.noCrossing
    leftNoAdjacentPair := leftCanonical.noAdjacentPair
    rightNoCrossing := rightCanonical.noCrossing
    rightNoAdjacentPair := rightCanonical.noAdjacentPair
  }⟩

end SemigroupBasis.CoRoots.Order6SporadicSection27
