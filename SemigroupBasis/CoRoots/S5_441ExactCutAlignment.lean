import SemigroupBasis.CoRoots.S5_441GapSeparatorFree
import SemigroupBasis.Examples.UniqueSeparatorFourCanonical

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis
open SemigroupBasis.Examples

/-- Replace one exact-cut gap by its deterministic sorted support while
retaining its separator. -/
def exactCutSupportSegment
    (segment : ExactCutSegment) : UniqueSeparatorCanonicalSegment :=
  { quadratic := connectedComponentSortedSupport segment.gap
    separator := segment.separator }

/-- The scanner always has one final separator-free segment. It carries no
support information exactly when its gap is empty, so only that case is
omitted from the support skeleton. -/
def exactCutSupportSegment?
    (segment : ExactCutSegment) :
    Option UniqueSeparatorCanonicalSegment :=
  if segment.gap = [] ∧ segment.separator = none then
    none
  else
    some (exactCutSupportSegment segment)

/-- Support-only exact-cut alignment for an arbitrary segment list. -/
def exactCutSupportSegments
    (segments : List ExactCutSegment) :
    List UniqueSeparatorCanonicalSegment :=
  segments.filterMap exactCutSupportSegment?

/-- The support-only exact-cut skeleton of a list. -/
def exactCutSupportSkeleton
    (letters : List Nat) : List UniqueSeparatorCanonicalSegment :=
  exactCutSupportSegments (exactCutDecomposition letters)

@[simp]
theorem exactCutSupportSegments_append
    (left right : List ExactCutSegment) :
    exactCutSupportSegments (left ++ right) =
      exactCutSupportSegments left ++
        exactCutSupportSegments right := by
  simp [exactCutSupportSegments]

@[simp]
theorem exactCutSupportSegments_cons_of_separator_some
    {segment : ExactCutSegment} {separator : Nat}
    (separatorEq : segment.separator = some separator)
    (rest : List ExactCutSegment) :
    exactCutSupportSegments (segment :: rest) =
      exactCutSupportSegment segment ::
        exactCutSupportSegments rest := by
  simp [exactCutSupportSegments, exactCutSupportSegment?,
    separatorEq]

theorem mem_exactCutSupportSegments_iff
    {segments : List ExactCutSegment}
    {target : UniqueSeparatorCanonicalSegment} :
    target ∈ exactCutSupportSegments segments ↔
      ∃ source,
        source ∈ segments ∧
        ¬ (source.gap = [] ∧ source.separator = none) ∧
        target = exactCutSupportSegment source := by
  rw [exactCutSupportSegments, List.mem_filterMap]
  constructor
  · rintro ⟨source, sourceMember, mapped⟩
    by_cases omitted :
        source.gap = [] ∧ source.separator = none
    · simp [exactCutSupportSegment?, omitted] at mapped
    · have targetEq :
          target = exactCutSupportSegment source := by
        simpa [exactCutSupportSegment?, omitted] using mapped.symm
      exact ⟨source, sourceMember, omitted, targetEq⟩
  · rintro ⟨source, sourceMember, retained, rfl⟩
    refine ⟨source, sourceMember, ?_⟩
    simp [exactCutSupportSegment?, retained]

@[simp]
theorem exactCutSupportSegment_labels_mem_iff
    (tested : Nat) (segment : ExactCutSegment) :
    tested ∈ (exactCutSupportSegment segment).labels ↔
      tested ∈ segment.render := by
  cases segment with
  | mk gap separator =>
      cases separator <;>
        simp [exactCutSupportSegment,
          UniqueSeparatorCanonicalSegment.labels,
          ExactCutSegment.render,
          connectedComponentSortedSupport_mem_iff]

@[simp]
theorem exactCutSupportSegment_render_mem_iff
    (tested : Nat) (segment : ExactCutSegment) :
    tested ∈ (exactCutSupportSegment segment).render ↔
      tested ∈ segment.render :=
  (uniqueSeparatorCanonical_segment_render_mem_iff
    tested (exactCutSupportSegment segment)).trans
      (exactCutSupportSegment_labels_mem_iff tested segment)

/-- Filtering the empty terminal segment does not change rendered support. -/
theorem exactCutSupportSegments_render_mem_iff
    (tested : Nat) (segments : List ExactCutSegment) :
    tested ∈
        uniqueSeparatorCanonicalRender
          (exactCutSupportSegments segments) ↔
      tested ∈ renderExactCutSegments segments := by
  constructor
  · intro targetMember
    have targetLabelMember :
        tested ∈
          uniqueSeparatorCanonicalLabels
            (exactCutSupportSegments segments) :=
      (uniqueSeparatorCanonicalRender_mem_iff
        tested (exactCutSupportSegments segments)).mp targetMember
    change
      tested ∈
        (exactCutSupportSegments segments).flatMap
          UniqueSeparatorCanonicalSegment.labels
        at targetLabelMember
    rw [List.mem_flatMap] at targetLabelMember
    rcases targetLabelMember with
      ⟨target, targetInSkeleton, testedInTarget⟩
    obtain
      ⟨source, sourceMember, _retained, rfl⟩ :=
      mem_exactCutSupportSegments_iff.mp targetInSkeleton
    have testedInSource :
        tested ∈ source.render :=
      (exactCutSupportSegment_labels_mem_iff
        tested source).mp testedInTarget
    change
      tested ∈ segments.flatMap ExactCutSegment.render
    rw [List.mem_flatMap]
    exact ⟨source, sourceMember, testedInSource⟩
  · intro sourceMember
    change
      tested ∈ segments.flatMap ExactCutSegment.render
        at sourceMember
    rw [List.mem_flatMap] at sourceMember
    rcases sourceMember with
      ⟨source, sourceInSegments, testedInSource⟩
    have retained :
        ¬ (source.gap = [] ∧ source.separator = none) := by
      rintro ⟨gapEmpty, separatorNone⟩
      have sourceRenderEmpty : source.render = [] := by
        simp [ExactCutSegment.render, gapEmpty, separatorNone]
      rw [sourceRenderEmpty] at testedInSource
      simp at testedInSource
    have targetInSkeleton :
        exactCutSupportSegment source ∈
          exactCutSupportSegments segments :=
      mem_exactCutSupportSegments_iff.mpr
        ⟨source, sourceInSegments, retained, rfl⟩
    have targetLabelMember :
        tested ∈ (exactCutSupportSegment source).labels :=
      (exactCutSupportSegment_labels_mem_iff
        tested source).mpr testedInSource
    apply
      (uniqueSeparatorCanonicalRender_mem_iff
        tested (exactCutSupportSegments segments)).mpr
    change
      tested ∈
        (exactCutSupportSegments segments).flatMap
          UniqueSeparatorCanonicalSegment.labels
    rw [List.mem_flatMap]
    exact
      ⟨exactCutSupportSegment source,
        targetInSkeleton, targetLabelMember⟩

theorem exactCutSupportPrefix_mem_iff
    (tested : Nat) (before : List ExactCutSegment)
    (gap : List Nat) :
    tested ∈
        uniqueSeparatorCanonicalRender
            (exactCutSupportSegments before) ++
          uniqueSeparatorCanonicalRenderDoubles
            (connectedComponentSortedSupport gap) ↔
      tested ∈ renderExactCutSegments before ++ gap := by
  simp only [List.mem_append,
    exactCutSupportSegments_render_mem_iff,
    uniqueSeparatorCanonicalRenderDoubles_mem_iff,
    connectedComponentSortedSupport_mem_iff]

/-- The support skeleton retains exactly the emitted separators. -/
theorem mem_exactCutSupportSegments_separators_iff
    {segments : List ExactCutSegment} {separator : Nat} :
    separator ∈
        (exactCutSupportSegments segments).filterMap
          UniqueSeparatorCanonicalSegment.separator ↔
      separator ∈ exactCutSeparators segments := by
  unfold exactCutSeparators
  constructor
  · intro separatorMember
    rw [List.mem_filterMap] at separatorMember ⊢
    rcases separatorMember with
      ⟨target, targetMember, targetSeparatorEq⟩
    obtain
      ⟨source, sourceMember, _retained, rfl⟩ :=
      mem_exactCutSupportSegments_iff.mp targetMember
    exact
      ⟨source, sourceMember, by
        simpa [exactCutSupportSegment] using targetSeparatorEq⟩
  · intro separatorMember
    rw [List.mem_filterMap] at separatorMember ⊢
    rcases separatorMember with
      ⟨source, sourceMember, sourceSeparatorEq⟩
    have retained :
        ¬ (source.gap = [] ∧ source.separator = none) := by
      rintro ⟨_gapEmpty, separatorNone⟩
      rw [separatorNone] at sourceSeparatorEq
      simp at sourceSeparatorEq
    refine
      ⟨exactCutSupportSegment source,
        mem_exactCutSupportSegments_iff.mpr
          ⟨source, sourceMember, retained, rfl⟩,
        ?_⟩
    simpa [exactCutSupportSegment] using sourceSeparatorEq

/-- The exact-cut scanner always emits at least its terminal segment. -/
theorem exactCutDecomposition_ne_nil
    (letters : List Nat) :
    exactCutDecomposition letters ≠ [] := by
  intro decompositionEmpty
  have lettersEmpty : letters = [] := by
    rw [← render_exactCutDecomposition letters, decompositionEmpty]
    rfl
  subst letters
  simp [exactCutDecomposition, exactCutScanner] at decompositionEmpty

/-- Scanner separator membership is equivalent to existence of an exact cut
at that separator. -/
theorem mem_exactCutSeparators_iff_exactCut
    {letters : List Nat} {separator : Nat} :
    separator ∈
        exactCutSeparators (exactCutDecomposition letters) ↔
      ∃ left right,
        UniqueSeparatorFourExactCut
          letters left separator right := by
  constructor
  · intro separatorMember
    unfold exactCutSeparators at separatorMember
    rw [List.mem_filterMap] at separatorMember
    rcases separatorMember with
      ⟨segment, segmentMember, separatorEq⟩
    obtain ⟨before, after, decompositionEq⟩ :=
      List.mem_iff_append.mp segmentMember
    exact
      ⟨renderExactCutSegments before ++ segment.gap,
        renderExactCutSegments after,
        exactCutDecomposition_separator_exactCut
          decompositionEq separatorEq⟩
  · rintro ⟨left, right, cut⟩
    obtain
      ⟨before, segment, after, decompositionEq,
        separatorEq, _leftEq, _rightEq⟩ :=
      exactCutDecomposition_exactCut_iff.mp cut
    unfold exactCutSeparators
    rw [List.mem_filterMap]
    refine ⟨segment, ?_, separatorEq⟩
    rw [decompositionEq]
    simp

theorem mem_exactCutSupportSkeleton_separators_iff_exactCut
    {letters : List Nat} {separator : Nat} :
    separator ∈
        (exactCutSupportSkeleton letters).filterMap
          UniqueSeparatorCanonicalSegment.separator ↔
      ∃ left right,
        UniqueSeparatorFourExactCut
          letters left separator right := by
  rw [exactCutSupportSkeleton,
    mem_exactCutSupportSegments_separators_iff,
    mem_exactCutSeparators_iff_exactCut]

private theorem exactCutSupportSegment_labels_nodup
    {letters : List Nat} {segment : ExactCutSegment}
    (segmentMember :
      segment ∈ exactCutDecomposition letters) :
    (exactCutSupportSegment segment).labels.Nodup := by
  have supportNodup :=
    connectedComponentSortedSupport_nodup segment.gap
  cases separatorEq : segment.separator with
  | none =>
      simpa [exactCutSupportSegment,
        UniqueSeparatorCanonicalSegment.labels,
        separatorEq] using supportNodup
  | some separator =>
      have separatorMember :
          separator ∈
            exactCutSeparators
              (exactCutDecomposition letters) := by
        unfold exactCutSeparators
        rw [List.mem_filterMap]
        exact ⟨segment, segmentMember, separatorEq⟩
      have separatorNotGap :
          separator ∉ segment.gap := by
        intro separatorInGap
        exact
          (exactCutDecomposition_gap_letter_not_separator
            segmentMember separatorInGap) separatorMember
      have separatorNotSupport :
          separator ∉
            connectedComponentSortedSupport segment.gap := by
        intro separatorInSupport
        exact separatorNotGap <|
          (connectedComponentSortedSupport_mem_iff
            separator segment.gap).mp separatorInSupport
      simp only [exactCutSupportSegment,
        UniqueSeparatorCanonicalSegment.labels,
        separatorEq, Option.toList_some]
      apply List.nodup_append.mpr
      refine ⟨supportNodup, by simp, ?_⟩
      intro left leftMember right rightMember equal
      have rightEq : right = separator := by
        simpa using rightMember
      subst right
      subst left
      exact separatorNotSupport leftMember

private theorem exactCutSupportSegments_labels_nodup
    {letters : List Nat} {segments : List ExactCutSegment}
    (subsegments :
      ∀ segment, segment ∈ segments →
        segment ∈ exactCutDecomposition letters)
    (pairwise :
      segments.Pairwise
        (fun left right =>
          UniqueSeparatorFourSupportsDisjoint
            left.render right.render)) :
    (uniqueSeparatorCanonicalLabels
      (exactCutSupportSegments segments)).Nodup := by
  induction segments with
  | nil =>
      simp [exactCutSupportSegments,
        uniqueSeparatorCanonicalLabels]
  | cons segment rest ih =>
      rw [List.pairwise_cons] at pairwise
      have tailNodup :
          (uniqueSeparatorCanonicalLabels
            (exactCutSupportSegments rest)).Nodup :=
        ih
          (fun candidate candidateMember =>
            subsegments candidate
              (List.Mem.tail segment candidateMember))
          pairwise.2
      by_cases omitted :
          segment.gap = [] ∧ segment.separator = none
      · simpa [exactCutSupportSegments,
          exactCutSupportSegment?, omitted] using tailNodup
      · have segmentNodup :
            (exactCutSupportSegment segment).labels.Nodup :=
          exactCutSupportSegment_labels_nodup <|
            subsegments segment (List.Mem.head rest)
        have labelsDisjoint :
            ∀ label,
              label ∈ (exactCutSupportSegment segment).labels →
              label ∉
                uniqueSeparatorCanonicalLabels
                  (exactCutSupportSegments rest) := by
          intro label firstMember tailMember
          have firstRenderMember :
              label ∈ segment.render :=
            (exactCutSupportSegment_labels_mem_iff
              label segment).mp firstMember
          have tailSkeletonMember :
              label ∈
                uniqueSeparatorCanonicalRender
                  (exactCutSupportSegments rest) :=
            (uniqueSeparatorCanonicalRender_mem_iff
              label (exactCutSupportSegments rest)).mpr tailMember
          have tailSourceMember :
              label ∈ renderExactCutSegments rest :=
            (exactCutSupportSegments_render_mem_iff
              label rest).mp tailSkeletonMember
          change
            label ∈ rest.flatMap ExactCutSegment.render
              at tailSourceMember
          rw [List.mem_flatMap] at tailSourceMember
          rcases tailSourceMember with
            ⟨candidate, candidateMember, candidateRenderMember⟩
          exact
            (pairwise.1 candidate candidateMember)
              label firstRenderMember candidateRenderMember
        have combinedNodup :
            ((exactCutSupportSegment segment).labels ++
              uniqueSeparatorCanonicalLabels
                (exactCutSupportSegments rest)).Nodup := by
          apply List.nodup_append.mpr
          refine ⟨segmentNodup, tailNodup, ?_⟩
          intro left leftMember right rightMember equal
          subst right
          exact labelsDisjoint left leftMember rightMember
        simpa [exactCutSupportSegments,
          exactCutSupportSegment?, omitted,
          uniqueSeparatorCanonicalLabels] using combinedNodup

private theorem exactCutDecomposition_suffix_pairwise_separator_isSome
    {letters : List Nat} :
    ∀ {scanPrefix suffix : List ExactCutSegment},
      exactCutDecomposition letters = scanPrefix ++ suffix →
      suffix.Pairwise
        (fun left _right => left.separator.isSome) := by
  intro scanPrefix suffix decompositionEq
  induction suffix generalizing scanPrefix with
  | nil =>
      simp
  | cons segment rest ih =>
      rw [List.pairwise_cons]
      constructor
      · intro candidate candidateMember
        obtain ⟨separator, separatorEq⟩ :=
          exactCutDecomposition_separator_some_of_after_ne_nil
            (letters := letters)
            (before := scanPrefix)
            (segment := segment)
            (after := rest)
            decompositionEq
            (List.ne_nil_of_mem candidateMember)
        simp [separatorEq]
      · apply ih (scanPrefix := scanPrefix ++ [segment])
        simpa [List.append_assoc] using decompositionEq

private theorem exactCutDecomposition_pairwise_separator_isSome
    (letters : List Nat) :
    (exactCutDecomposition letters).Pairwise
      (fun left _right => left.separator.isSome) := by
  apply exactCutDecomposition_suffix_pairwise_separator_isSome
    (letters := letters)
    (scanPrefix := [])
  simp

private theorem exactCutSupportSegments_pairwise_separator_isSome
    {segments : List ExactCutSegment}
    (pairwise :
      segments.Pairwise
        (fun left _right => left.separator.isSome)) :
    (exactCutSupportSegments segments).Pairwise
      (fun left _right => left.separator.isSome) := by
  induction segments with
  | nil =>
      simp [exactCutSupportSegments]
  | cons segment rest ih =>
      rw [List.pairwise_cons] at pairwise
      have tailPairwise := ih pairwise.2
      by_cases omitted :
          segment.gap = [] ∧ segment.separator = none
      · simpa [exactCutSupportSegments,
          exactCutSupportSegment?, omitted] using tailPairwise
      · have firstRelation :
            ∀ target,
              target ∈ exactCutSupportSegments rest →
              (exactCutSupportSegment segment).separator.isSome := by
          intro target targetMember
          obtain
            ⟨source, sourceMember, _sourceRetained, _targetEq⟩ :=
            mem_exactCutSupportSegments_iff.mp targetMember
          have sourceRelation :=
            pairwise.1 source sourceMember
          simpa [exactCutSupportSegment] using sourceRelation
        have mappedPairwise :
            (exactCutSupportSegment segment ::
              exactCutSupportSegments rest).Pairwise
                (fun left _right => left.separator.isSome) := by
          rw [List.pairwise_cons]
          exact ⟨firstRelation, tailPairwise⟩
        simpa [exactCutSupportSegments,
          exactCutSupportSegment?, omitted] using mappedPairwise

/-- The support-only scanner skeleton satisfies the canonical segment-list
contract used by unique-separator injectivity. -/
theorem exactCutSupportSkeleton_canonical
    (letters : List Nat) :
    UniqueSeparatorCanonical
      (exactCutSupportSkeleton letters) := by
  have labelsNodup :
      (uniqueSeparatorCanonicalLabels
        (exactCutSupportSkeleton letters)).Nodup := by
    apply exactCutSupportSegments_labels_nodup
      (letters := letters)
      (segments := exactCutDecomposition letters)
    · intro segment segmentMember
      exact segmentMember
    · exact exactCutDecomposition_renders_pairwise_disjoint letters
  have separatorPairwise :
      (exactCutSupportSkeleton letters).Pairwise
        (fun left _right => left.separator.isSome) := by
    apply exactCutSupportSegments_pairwise_separator_isSome
    exact exactCutDecomposition_pairwise_separator_isSome letters
  refine ⟨labelsNodup, ?_, ?_, ?_⟩
  · intro target targetMember
    obtain
      ⟨source, _sourceMember, _retained, rfl⟩ :=
      mem_exactCutSupportSegments_iff.mp targetMember
    exact connectedComponentSortedSupport_sorted source.gap
  · intro before segment rest skeletonEq separatorNone
    rw [skeletonEq] at separatorPairwise
    have suffixPairwise :
        (segment :: rest).Pairwise
          (fun left _right => left.separator.isSome) :=
      (List.pairwise_append.mp separatorPairwise).2.1
    cases rest with
    | nil =>
        rfl
    | cons next tail =>
        have separatorSome :=
          (List.pairwise_cons.mp suffixPairwise).1
            next (List.Mem.head tail)
        exact False.elim <| by
          simpa [separatorNone] using separatorSome
  · intro target targetMember quadraticEmpty
    obtain
      ⟨source, _sourceMember, retained, rfl⟩ :=
      mem_exactCutSupportSegments_iff.mp targetMember
    have supportEmpty :
        connectedComponentSortedSupport source.gap = [] := by
      simpa [exactCutSupportSegment] using quadraticEmpty
    have gapEmpty : source.gap = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro tested testedMember
      have supportMember :
          tested ∈ connectedComponentSortedSupport source.gap :=
        (connectedComponentSortedSupport_mem_iff
          tested source.gap).2 testedMember
      rw [supportEmpty] at supportMember
      exact (by simpa using supportMember)
    cases separatorEq : source.separator with
    | none =>
        exact False.elim <| retained ⟨gapEmpty, separatorEq⟩
    | some separator =>
        simp [exactCutSupportSegment, separatorEq]

theorem exactCutSupportSkeleton_render_mem_iff
    (letters : List Nat) (tested : Nat) :
    tested ∈
        uniqueSeparatorCanonicalRender
          (exactCutSupportSkeleton letters) ↔
      tested ∈ letters := by
  rw [exactCutSupportSkeleton,
    exactCutSupportSegments_render_mem_iff,
    render_exactCutDecomposition]

private theorem exactCut_separator_not_left
    {letters left right : List Nat} {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        letters left separator right) :
    separator ∉ left := by
  intro member
  have positive : 0 < left.count separator :=
    List.count_pos_iff.mpr member
  have countOne := cut.2.1
  rw [cut.1, List.count_append, List.count_cons_self] at countOne
  omega

private theorem exactCut_append_separator_injective
    {α : Type} [DecidableEq α] {separator : α} :
    ∀ {left right leftTail rightTail : List α},
      separator ∉ left →
      separator ∉ right →
      left ++ separator :: leftTail =
        right ++ separator :: rightTail →
      left = right ∧ leftTail = rightTail
  | [], [], leftTail, rightTail, _, _, equality => by
      simpa using equality
  | [], rightHead :: right, leftTail, rightTail, _,
      separatorNotRight, equality => by
      have separatorNeRightHead : separator ≠ rightHead := by
        intro separatorEq
        subst rightHead
        exact separatorNotRight (by simp)
      have headsEqual : separator = rightHead := by
        simpa using congrArg List.head? equality
      exact False.elim (separatorNeRightHead headsEqual)
  | leftHead :: left, [], leftTail, rightTail,
      separatorNotLeft, _, equality => by
      have separatorNeLeftHead : separator ≠ leftHead := by
        intro separatorEq
        subst leftHead
        exact separatorNotLeft (by simp)
      have headsEqual : leftHead = separator := by
        simpa using congrArg List.head? equality
      exact False.elim (separatorNeLeftHead headsEqual.symm)
  | leftHead :: left, rightHead :: right, leftTail, rightTail,
      separatorNotLeft, separatorNotRight, equality => by
      have leftAbsence :
          separator ≠ leftHead ∧ separator ∉ left := by
        simpa only [List.mem_cons, not_or] using separatorNotLeft
      have rightAbsence :
          separator ≠ rightHead ∧ separator ∉ right := by
        simpa only [List.mem_cons, not_or] using separatorNotRight
      have consEquality :
          leftHead = rightHead ∧
            left ++ separator :: leftTail =
              right ++ separator :: rightTail := by
        simpa only [List.cons_append, List.cons.injEq] using equality
      rcases consEquality with ⟨rfl, restEquality⟩
      have tailEquality :=
        exactCut_append_separator_injective
          leftAbsence.2 rightAbsence.2 restEquality
      exact
        ⟨congrArg (List.cons leftHead) tailEquality.1,
          tailEquality.2⟩

private theorem exactCut_sides_unique
    {letters firstLeft firstRight secondLeft secondRight : List Nat}
    {separator : Nat}
    (first :
      UniqueSeparatorFourExactCut
        letters firstLeft separator firstRight)
    (second :
      UniqueSeparatorFourExactCut
        letters secondLeft separator secondRight) :
    firstLeft = secondLeft ∧ firstRight = secondRight :=
  exactCut_append_separator_injective
    (exactCut_separator_not_left first)
    (exactCut_separator_not_left second)
    (first.1.symm.trans second.1)

/-- Transport one exact cut from the original list to its support skeleton.
Both side supports are preserved exactly. -/
theorem exactCutSupportSkeleton_transportExactCut
    {letters left right : List Nat} {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        letters left separator right) :
    ∃ skeletonLeft skeletonRight,
      UniqueSeparatorFourExactCut
          (uniqueSeparatorCanonicalRender
            (exactCutSupportSkeleton letters))
          skeletonLeft separator skeletonRight ∧
        (∀ tested, tested ∈ skeletonLeft ↔ tested ∈ left) ∧
        (∀ tested, tested ∈ skeletonRight ↔ tested ∈ right) := by
  obtain
    ⟨before, segment, after, decompositionEq,
      separatorEq, leftEq, rightEq⟩ :=
    exactCutDecomposition_exactCut_iff.mp cut
  have skeletonShape :
      exactCutSupportSkeleton letters =
        exactCutSupportSegments before ++
          exactCutSupportSegment segment ::
            exactCutSupportSegments after := by
    rw [exactCutSupportSkeleton, decompositionEq,
      exactCutSupportSegments_append,
      exactCutSupportSegments_cons_of_separator_some
        separatorEq]
  let skeletonLeft :=
    uniqueSeparatorCanonicalRender
        (exactCutSupportSegments before) ++
      uniqueSeparatorCanonicalRenderDoubles
        (connectedComponentSortedSupport segment.gap)
  let skeletonRight :=
    uniqueSeparatorCanonicalRender
      (exactCutSupportSegments after)
  have separatorMember :
      separator ∈
        (exactCutSupportSkeleton letters).filterMap
          UniqueSeparatorCanonicalSegment.separator :=
    (mem_exactCutSupportSkeleton_separators_iff_exactCut).mpr
      ⟨left, right, cut⟩
  have countOne :
      (uniqueSeparatorCanonicalRender
        (exactCutSupportSkeleton letters)).count separator = 1 :=
    (uniqueSeparatorCanonical_separator_mem_iff_count_one
      (exactCutSupportSkeleton_canonical letters)
      separator).mp separatorMember
  have split :
      uniqueSeparatorCanonicalRender
          (exactCutSupportSkeleton letters) =
        skeletonLeft ++ separator :: skeletonRight := by
    rw [skeletonShape]
    simp [skeletonLeft, skeletonRight,
      uniqueSeparatorCanonicalRender_append,
      uniqueSeparatorCanonicalRender,
      UniqueSeparatorCanonicalSegment.render,
      exactCutSupportSegment, separatorEq,
      List.append_assoc]
  have leftSupport :
      ∀ tested, tested ∈ skeletonLeft ↔ tested ∈ left := by
    intro tested
    rw [← leftEq]
    exact
      exactCutSupportPrefix_mem_iff
        tested before segment.gap
  have rightSupport :
      ∀ tested, tested ∈ skeletonRight ↔ tested ∈ right := by
    intro tested
    rw [← rightEq]
    exact
      exactCutSupportSegments_render_mem_iff tested after
  have disjoint :
      UniqueSeparatorFourSupportsDisjoint
        skeletonLeft skeletonRight := by
    intro tested leftMember rightMember
    exact
      cut.2.2 tested
        ((leftSupport tested).mp leftMember)
        ((rightSupport tested).mp rightMember)
  exact
    ⟨skeletonLeft, skeletonRight,
      ⟨split, countOne, disjoint⟩,
      leftSupport, rightSupport⟩

/-- Reflect one exact cut of the support skeleton back to the original list,
again preserving both side supports. -/
theorem exactCutSupportSkeleton_reflectExactCut
    {letters skeletonLeft skeletonRight : List Nat}
    {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        (uniqueSeparatorCanonicalRender
          (exactCutSupportSkeleton letters))
        skeletonLeft separator skeletonRight) :
    ∃ left right,
      UniqueSeparatorFourExactCut
          letters left separator right ∧
        (∀ tested, tested ∈ skeletonLeft ↔ tested ∈ left) ∧
        (∀ tested, tested ∈ skeletonRight ↔ tested ∈ right) := by
  have separatorMember :
      separator ∈
        (exactCutSupportSkeleton letters).filterMap
          UniqueSeparatorCanonicalSegment.separator :=
    uniqueSeparatorCanonical_exactCut_separator_mem
      (exactCutSupportSkeleton_canonical letters) cut
  obtain ⟨left, right, sourceCut⟩ :=
    (mem_exactCutSupportSkeleton_separators_iff_exactCut).mp
      separatorMember
  obtain
    ⟨alignedLeft, alignedRight, alignedCut,
      alignedLeftSupport, alignedRightSupport⟩ :=
    exactCutSupportSkeleton_transportExactCut sourceCut
  have sidesEq :=
    exactCut_sides_unique cut alignedCut
  refine ⟨left, right, sourceCut, ?_, ?_⟩
  · intro tested
    rw [sidesEq.1]
    exact alignedLeftSupport tested
  · intro tested
    rw [sidesEq.2]
    exact alignedRightSupport tested

/-- Transport a skeleton exact cut across words with the same exact-cut
signature. -/
theorem
    exactCutSupportSkeleton_transportExactCut_of_sameExactCutSignature
    {source target : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature
        source target)
    {sourceLeft sourceRight : List Nat} {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        (uniqueSeparatorCanonicalRender
          (exactCutSupportSkeleton source.toList))
        sourceLeft separator sourceRight) :
    ∃ targetLeft targetRight,
      UniqueSeparatorFourExactCut
          (uniqueSeparatorCanonicalRender
            (exactCutSupportSkeleton target.toList))
          targetLeft separator targetRight ∧
        (∀ tested, tested ∈ targetLeft ↔ tested ∈ sourceLeft) ∧
        (∀ tested, tested ∈ targetRight ↔ tested ∈ sourceRight) := by
  obtain
    ⟨originalLeft, originalRight, sourceCut,
      sourceLeftSupport, sourceRightSupport⟩ :=
    exactCutSupportSkeleton_reflectExactCut cut
  obtain
    ⟨targetOriginalLeft, targetOriginalRight, targetCut,
      targetLeftSupport, targetRightSupport⟩ :=
    SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature.transport
      same sourceCut
  obtain
    ⟨targetLeft, targetRight, targetSkeletonCut,
      targetSkeletonLeftSupport, targetSkeletonRightSupport⟩ :=
    exactCutSupportSkeleton_transportExactCut targetCut
  refine
    ⟨targetLeft, targetRight, targetSkeletonCut, ?_, ?_⟩
  · intro tested
    exact
      (targetSkeletonLeftSupport tested).trans <|
        (targetLeftSupport tested).trans
          (sourceLeftSupport tested).symm
  · intro tested
    exact
      (targetSkeletonRightSupport tested).trans <|
        (targetRightSupport tested).trans
          (sourceRightSupport tested).symm

theorem
    exactCutSupportSkeleton_sameSignature_of_sameSupport_sameExactCutSignature
    {left right : Word Nat}
    (sameSupport :
      SemigroupBasis.CoRoots.S5_441Invariant.SameSupport left right)
    (sameExactCuts :
      SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature
        left right) :
    UniqueSeparatorCanonicalSameSignature
      (exactCutSupportSkeleton left.toList)
      (exactCutSupportSkeleton right.toList) := by
  refine ⟨?_, ?_, ?_⟩
  · intro tested
    rw [exactCutSupportSkeleton_render_mem_iff,
      exactCutSupportSkeleton_render_mem_iff]
    exact sameSupport tested
  · intro leftPrefix leftSuffix separator cut
    exact
      exactCutSupportSkeleton_transportExactCut_of_sameExactCutSignature
        sameExactCuts cut
  · intro rightPrefix rightSuffix separator cut
    exact
      exactCutSupportSkeleton_transportExactCut_of_sameExactCutSignature
        (SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature.symm
          sameExactCuts)
        cut

/-- Support and exact-cut signature determine the exact-cut support skeleton. -/
theorem
    exactCutSupportSkeleton_eq_of_sameSupport_sameExactCutSignature
    {left right : Word Nat}
    (sameSupport :
      SemigroupBasis.CoRoots.S5_441Invariant.SameSupport left right)
    (sameExactCuts :
      SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature
        left right) :
    exactCutSupportSkeleton left.toList =
      exactCutSupportSkeleton right.toList :=
  uniqueSeparatorCanonical_eq_of_sameSignature
    (exactCutSupportSkeleton_canonical left.toList)
    (exactCutSupportSkeleton_canonical right.toList)
    (exactCutSupportSkeleton_sameSignature_of_sameSupport_sameExactCutSignature
      sameSupport sameExactCuts)

theorem exactCutSupportSkeleton_eq_of_sameParitySeparatorSignature
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_441Invariant.SameParitySeparatorSignature
        left right) :
    exactCutSupportSkeleton left.toList =
      exactCutSupportSkeleton right.toList :=
  exactCutSupportSkeleton_eq_of_sameSupport_sameExactCutSignature
    same.support same.exactCuts

end SemigroupBasis.CoRoots.S5_441
