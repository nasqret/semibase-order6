import SemigroupBasis.CoRoots.S5_378CanonicalGap
import SemigroupBasis.CoRoots.S5_441ExactCutAlignment
import SemigroupBasis.CoRoots.S5_441GapCountLocalization

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_378

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev CutSegment :=
  SemigroupBasis.CoRoots.S5_441.ExactCutSegment

/-- Every nonempty exact-cut-free gap derives all the way to a canonical
least-endpoint, globally sorted, cap-two envelope. -/
theorem existsCanonicalGapNormal
    {gap : List Nat}
    (gapNonempty : gap ≠ [])
    (noExactCut :
      ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut gap left separator right) :
    ∃ endpoint interior,
      ListDerives gap (gapEnvelopeRender endpoint interior) ∧
      endpoint ∉ interior ∧
      interior.Pairwise (· ≤ ·) ∧
      (∀ tested,
        (gapEnvelopeRender endpoint interior).count tested =
          min (gap.count tested) 2) ∧
      (∀ tested,
        2 ≤ gap.count tested → endpoint ≤ tested) := by
  obtain
    ⟨initialEndpoint, initialInterior, initialDerivation,
      initialAbsent, initialLimited, initialCapped⟩ :=
    existsGapEnvelopeNormalOfNoExactCut
      gapNonempty noExactCut
  obtain
    ⟨endpoint, interior, refinement,
      endpointAbsent, interiorSorted, capped, least⟩ :=
    canonicalGapRefinement gap initialEndpoint initialInterior
      initialAbsent initialLimited initialCapped
  exact
    ⟨endpoint, interior, initialDerivation.trans refinement,
      endpointAbsent, interiorSorted, capped, least⟩

/-- Two canonical gap envelopes are equal whenever their source cap-two
profiles agree. -/
theorem canonicalGapRender_eq_of_cappedCounts
    {left right : List Nat}
    {leftEndpoint rightEndpoint : Nat}
    {leftInterior rightInterior : List Nat}
    (leftAbsent : leftEndpoint ∉ leftInterior)
    (rightAbsent : rightEndpoint ∉ rightInterior)
    (leftSorted : leftInterior.Pairwise (· ≤ ·))
    (rightSorted : rightInterior.Pairwise (· ≤ ·))
    (leftCapped :
      ∀ tested,
        (gapEnvelopeRender leftEndpoint leftInterior).count tested =
          min (left.count tested) 2)
    (rightCapped :
      ∀ tested,
        (gapEnvelopeRender rightEndpoint rightInterior).count tested =
          min (right.count tested) 2)
    (leftLeast :
      ∀ tested, 2 ≤ left.count tested → leftEndpoint ≤ tested)
    (rightLeast :
      ∀ tested, 2 ≤ right.count tested → rightEndpoint ≤ tested)
    (sameCapped :
      ∀ tested,
        min (left.count tested) 2 = min (right.count tested) 2) :
    gapEnvelopeRender leftEndpoint leftInterior =
      gapEnvelopeRender rightEndpoint rightInterior := by
  have leftInteriorEndpointCount :
      leftInterior.count leftEndpoint = 0 :=
    List.count_eq_zero.mpr leftAbsent
  have rightInteriorEndpointCount :
      rightInterior.count rightEndpoint = 0 :=
    List.count_eq_zero.mpr rightAbsent
  have leftTargetEndpointCount :
      (gapEnvelopeRender leftEndpoint leftInterior).count
          leftEndpoint = 2 := by
    simp [gapEnvelopeRender, leftInteriorEndpointCount]
  have rightTargetEndpointCount :
      (gapEnvelopeRender rightEndpoint rightInterior).count
          rightEndpoint = 2 := by
    simp [gapEnvelopeRender, rightInteriorEndpointCount]
  have leftEndpointMultiple : 2 ≤ left.count leftEndpoint := by
    have capped := leftCapped leftEndpoint
    rw [leftTargetEndpointCount] at capped
    omega
  have rightEndpointMultiple : 2 ≤ right.count rightEndpoint := by
    have capped := rightCapped rightEndpoint
    rw [rightTargetEndpointCount] at capped
    omega
  have leftEndpointMultipleRight :
      2 ≤ right.count leftEndpoint := by
    have profiles := sameCapped leftEndpoint
    rw [Nat.min_eq_right leftEndpointMultiple] at profiles
    omega
  have rightEndpointMultipleLeft :
      2 ≤ left.count rightEndpoint := by
    have profiles := sameCapped rightEndpoint
    rw [Nat.min_eq_right rightEndpointMultiple] at profiles
    omega
  have endpointEq : leftEndpoint = rightEndpoint :=
    Nat.le_antisymm
      (leftLeast rightEndpoint rightEndpointMultipleLeft)
      (rightLeast leftEndpoint leftEndpointMultipleRight)
  subst rightEndpoint
  have interiorCountEq :
      ∀ tested,
        leftInterior.count tested = rightInterior.count tested := by
    intro tested
    by_cases testedEq : tested = leftEndpoint
    · subst tested
      exact
        leftInteriorEndpointCount.trans
          rightInteriorEndpointCount.symm
    · have fullCountEq :
          (gapEnvelopeRender leftEndpoint leftInterior).count tested =
            (gapEnvelopeRender leftEndpoint rightInterior).count tested :=
        (leftCapped tested).trans <|
          (sameCapped tested).trans (rightCapped tested).symm
      simpa [gapEnvelopeRender, testedEq,
        Ne.symm testedEq] using fullCountEq
  have interiorPermutation : leftInterior.Perm rightInterior :=
    List.perm_iff_count.mpr interiorCountEq
  have interiorEq : leftInterior = rightInterior :=
    List.Perm.eq_of_pairwise
      (fun _ _ _ _ leftLe rightLe =>
        Nat.le_antisymm leftLe rightLe)
      leftSorted rightSorted interiorPermutation
  rw [interiorEq]

private theorem supportSkeleton_eq
    {left right : Word Nat}
    (sameSupport : SameSupport left right)
    (sameExactCuts : SameExactCutSignature left right) :
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton
        left.toList =
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton
        right.toList := by
  apply
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton_eq_of_sameSupport_sameExactCutSignature
  · intro tested
    exact sameSupport tested
  · intro separator leftSupport rightSupport
    simpa only [
      SemigroupBasis.CoRoots.S5_441Invariant.ExactCutSignature,
      ExactCutSignature
    ] using sameExactCuts separator leftSupport rightSupport

private theorem alignedGapCappedCounts
    {leftLetters rightLetters : List Nat}
    {leftSegment rightSegment : CutSegment}
    (leftMember :
      leftSegment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
          leftLetters)
    (rightMember :
      rightSegment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
          rightLetters)
    (supportEq :
      connectedComponentSortedSupport leftSegment.gap =
        connectedComponentSortedSupport rightSegment.gap)
    (globalCapped :
      ∀ tested,
        min (leftLetters.count tested) 2 =
          min (rightLetters.count tested) 2) :
    ∀ tested,
      min (leftSegment.gap.count tested) 2 =
        min (rightSegment.gap.count tested) 2 := by
  intro tested
  by_cases leftGapMember : tested ∈ leftSegment.gap
  · have leftSupportMember :
        tested ∈ connectedComponentSortedSupport leftSegment.gap :=
      (connectedComponentSortedSupport_mem_iff
        tested leftSegment.gap).2 leftGapMember
    have rightSupportMember :
        tested ∈ connectedComponentSortedSupport rightSegment.gap := by
      rw [← supportEq]
      exact leftSupportMember
    have rightGapMember : tested ∈ rightSegment.gap :=
      (connectedComponentSortedSupport_mem_iff
        tested rightSegment.gap).1 rightSupportMember
    have leftLocalized :=
      SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_count_eq_gap_count
          leftMember leftGapMember
    have rightLocalized :=
      SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_count_eq_gap_count
          rightMember rightGapMember
    rw [← leftLocalized, ← rightLocalized]
    exact globalCapped tested
  · have leftSupportAbsent :
        tested ∉ connectedComponentSortedSupport leftSegment.gap := by
      intro supportMember
      exact leftGapMember <|
        (connectedComponentSortedSupport_mem_iff
          tested leftSegment.gap).1 supportMember
    have rightSupportAbsent :
        tested ∉ connectedComponentSortedSupport rightSegment.gap := by
      rw [← supportEq]
      exact leftSupportAbsent
    have rightGapAbsent : tested ∉ rightSegment.gap := by
      intro rightMember'
      exact rightSupportAbsent <|
        (connectedComponentSortedSupport_mem_iff
          tested rightSegment.gap).2 rightMember'
    have leftZero : leftSegment.gap.count tested = 0 :=
      List.count_eq_zero.mpr leftGapMember
    have rightZero : rightSegment.gap.count tested = 0 :=
      List.count_eq_zero.mpr rightGapAbsent
    simp [leftZero, rightZero]

private theorem alignedSegments_common
    {leftLetters rightLetters : List Nat}
    {leftSegment rightSegment : CutSegment}
    (leftMember :
      leftSegment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
          leftLetters)
    (rightMember :
      rightSegment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
          rightLetters)
    (supportSegmentEq :
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment
          leftSegment =
        SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment
          rightSegment)
    (globalCapped :
      ∀ tested,
        min (leftLetters.count tested) 2 =
          min (rightLetters.count tested) 2) :
    ∃ common,
      ListDerives leftSegment.render common ∧
      ListDerives rightSegment.render common := by
  have supportEq :
      connectedComponentSortedSupport leftSegment.gap =
        connectedComponentSortedSupport rightSegment.gap := by
    exact congrArg
      UniqueSeparatorCanonicalSegment.quadratic supportSegmentEq
  have separatorEq :
      leftSegment.separator = rightSegment.separator := by
    exact congrArg
      UniqueSeparatorCanonicalSegment.separator supportSegmentEq
  by_cases leftGapEmpty : leftSegment.gap = []
  · have rightGapEmpty : rightSegment.gap = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro tested rightGapMember
      have rightSupportMember :
          tested ∈ connectedComponentSortedSupport rightSegment.gap :=
        (connectedComponentSortedSupport_mem_iff
          tested rightSegment.gap).2 rightGapMember
      rw [← supportEq] at rightSupportMember
      have leftGapMember : tested ∈ leftSegment.gap :=
        (connectedComponentSortedSupport_mem_iff
          tested leftSegment.gap).1 rightSupportMember
      exact (by simpa [leftGapEmpty] using leftGapMember)
    refine ⟨leftSegment.separator.toList, ?_, ?_⟩
    · simpa [SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
        leftGapEmpty] using
        (S5_107.ListDerives.refl
          (basis := basis) leftSegment.separator.toList)
    · simpa [SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
        rightGapEmpty, separatorEq] using
        (S5_107.ListDerives.refl
          (basis := basis) rightSegment.separator.toList)
  · have rightGapNonempty : rightSegment.gap ≠ [] := by
      intro rightGapEmpty
      obtain ⟨tested, testedMember⟩ :=
        List.exists_mem_of_ne_nil leftSegment.gap leftGapEmpty
      have leftSupportMember :
          tested ∈ connectedComponentSortedSupport leftSegment.gap :=
        (connectedComponentSortedSupport_mem_iff
          tested leftSegment.gap).2 testedMember
      rw [supportEq] at leftSupportMember
      have rightGapMember : tested ∈ rightSegment.gap :=
        (connectedComponentSortedSupport_mem_iff
          tested rightSegment.gap).1 leftSupportMember
      exact (List.ne_nil_of_mem rightGapMember) rightGapEmpty
    have leftNoExactCut :=
      SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_gap_no_exactCut
        leftMember
    have rightNoExactCut :=
      SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_gap_no_exactCut
        rightMember
    obtain
      ⟨leftEndpoint, leftInterior, leftDerivation,
        leftAbsent, leftSorted, leftCapped, leftLeast⟩ :=
      existsCanonicalGapNormal leftGapEmpty leftNoExactCut
    obtain
      ⟨rightEndpoint, rightInterior, rightDerivation,
        rightAbsent, rightSorted, rightCapped, rightLeast⟩ :=
      existsCanonicalGapNormal rightGapNonempty rightNoExactCut
    have gapCapped :=
      alignedGapCappedCounts
        leftMember rightMember supportEq globalCapped
    have canonicalEq :
        gapEnvelopeRender leftEndpoint leftInterior =
          gapEnvelopeRender rightEndpoint rightInterior :=
      canonicalGapRender_eq_of_cappedCounts
        leftAbsent rightAbsent leftSorted rightSorted
        leftCapped rightCapped leftLeast rightLeast gapCapped
    let common :=
      gapEnvelopeRender leftEndpoint leftInterior ++
        leftSegment.separator.toList
    have leftSegmentDerivation :
        ListDerives leftSegment.render common := by
      simpa [common,
        SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render] using
        S5_107.ListDerives.append leftDerivation
          leftSegment.separator.toList
    have rightSegmentDerivation :
        ListDerives rightSegment.render common := by
      have appended :=
        S5_107.ListDerives.append rightDerivation
          rightSegment.separator.toList
      simpa [common,
        SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
        canonicalEq, separatorEq] using appended
    exact ⟨common, leftSegmentDerivation, rightSegmentDerivation⟩

private def retainCutSegment (segment : CutSegment) : Bool :=
  decide (¬ (segment.gap = [] ∧ segment.separator = none))

private def retainedCutSegments
    (segments : List CutSegment) : List CutSegment :=
  segments.filter retainCutSegment

private theorem render_retainedCutSegments
    (segments : List CutSegment) :
    SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
        (retainedCutSegments segments) =
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
        segments := by
  induction segments with
  | nil => rfl
  | cons segment remaining induction =>
      unfold retainedCutSegments at induction
      by_cases omitted :
          segment.gap = [] ∧ segment.separator = none
      · simp [retainedCutSegments, retainCutSegment, omitted,
          SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
          induction]
      · simp [retainedCutSegments, retainCutSegment, omitted,
          induction]

private theorem supportSegments_eq_map_retained
    (segments : List CutSegment) :
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments segments =
      (retainedCutSegments segments).map
        SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment := by
  induction segments with
  | nil => rfl
  | cons segment remaining induction =>
      unfold retainedCutSegments at induction
      unfold SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments at induction
      by_cases omitted :
          segment.gap = [] ∧ segment.separator = none
      · simp [retainedCutSegments, retainCutSegment,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment?,
          omitted, induction]
      · simp [retainedCutSegments, retainCutSegment,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment?,
          omitted, induction]

private theorem retainedCutSegments_member
    {segment : CutSegment} {segments : List CutSegment}
    (member : segment ∈ retainedCutSegments segments) :
    segment ∈ segments :=
  (List.mem_filter.mp member).1

private theorem assembleRetainedSegments
    (leftLetters rightLetters : List Nat)
    (globalCapped :
      ∀ tested,
        min (leftLetters.count tested) 2 =
          min (rightLetters.count tested) 2) :
    ∀ (leftSegments rightSegments : List CutSegment),
      (∀ segment, segment ∈ leftSegments →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
            leftLetters) →
      (∀ segment, segment ∈ rightSegments →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
            rightLetters) →
      leftSegments.map
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment =
        rightSegments.map
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment →
      ∃ common,
        ListDerives
          (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            leftSegments) common ∧
        ListDerives
          (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            rightSegments) common
  | [], [], _, _, _ =>
      ⟨[], S5_107.ListDerives.refl [],
        S5_107.ListDerives.refl []⟩
  | [], _ :: _, _, _, supportEq => by
      simp at supportEq
  | _ :: _, [], _, _, supportEq => by
      simp at supportEq
  | leftSegment :: leftRemaining,
      rightSegment :: rightRemaining,
      leftMembers, rightMembers, supportEq => by
      simp only [List.map_cons, List.cons.injEq] at supportEq
      have leftSegmentMember :=
        leftMembers leftSegment (by simp)
      have rightSegmentMember :=
        rightMembers rightSegment (by simp)
      obtain
        ⟨headCommon, leftHeadDerivation,
          rightHeadDerivation⟩ :=
        alignedSegments_common
          leftSegmentMember rightSegmentMember
          supportEq.1 globalCapped
      obtain
        ⟨tailCommon, leftTailDerivation,
          rightTailDerivation⟩ :=
        assembleRetainedSegments leftLetters rightLetters globalCapped
          leftRemaining rightRemaining
          (fun segment member =>
            leftMembers segment
              (List.Mem.tail leftSegment member))
          (fun segment member =>
            rightMembers segment
              (List.Mem.tail rightSegment member))
          supportEq.2
      have leftHeadStep :
          ListDerives
            (leftSegment.render ++
              SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                leftRemaining)
            (headCommon ++
              SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                leftRemaining) :=
        S5_107.ListDerives.append leftHeadDerivation
          (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            leftRemaining)
      have leftTailStep :
          ListDerives
            (headCommon ++
              SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                leftRemaining)
            (headCommon ++ tailCommon) :=
        S5_107.ListDerives.prepend headCommon leftTailDerivation
      have rightHeadStep :
          ListDerives
            (rightSegment.render ++
              SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                rightRemaining)
            (headCommon ++
              SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                rightRemaining) :=
        S5_107.ListDerives.append rightHeadDerivation
          (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            rightRemaining)
      have rightTailStep :
          ListDerives
            (headCommon ++
              SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                rightRemaining)
            (headCommon ++ tailCommon) :=
        S5_107.ListDerives.prepend headCommon rightTailDerivation
      exact
        ⟨headCommon ++ tailCommon,
          by simpa using leftHeadStep.trans leftTailStep,
          by simpa using rightHeadStep.trans rightTailStep⟩
termination_by leftSegments rightSegments =>
  leftSegments.length + rightSegments.length

/-- Full contextual assembly across the deterministic exact-separator
decomposition. -/
theorem exactCutAssembly : ExactCutAssemblyObligation := by
  intro left right sameSupport sameExactCuts globalCapped
  let leftSegments :=
    SemigroupBasis.CoRoots.S5_441.exactCutDecomposition left.toList
  let rightSegments :=
    SemigroupBasis.CoRoots.S5_441.exactCutDecomposition right.toList
  let leftRetained := retainedCutSegments leftSegments
  let rightRetained := retainedCutSegments rightSegments
  have skeletonEq :=
    supportSkeleton_eq sameSupport sameExactCuts
  have supportSegmentsEq :
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments
          leftSegments =
        SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments
          rightSegments := by
    simpa [leftSegments, rightSegments,
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton] using
        skeletonEq
  have retainedSupportEq :
      leftRetained.map
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment =
        rightRetained.map
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment := by
    rw [← supportSegments_eq_map_retained,
      ← supportSegments_eq_map_retained]
    exact supportSegmentsEq
  have leftMembers :
      ∀ segment, segment ∈ leftRetained →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
            left.toList := by
    intro segment member
    exact retainedCutSegments_member member
  have rightMembers :
      ∀ segment, segment ∈ rightRetained →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
            right.toList := by
    intro segment member
    exact retainedCutSegments_member member
  obtain ⟨common, leftDerivation, rightDerivation⟩ :=
    assembleRetainedSegments left.toList right.toList globalCapped
      leftRetained rightRetained
      leftMembers rightMembers retainedSupportEq
  have leftRenderEq :
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          leftRetained = left.toList := by
    calc
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          leftRetained =
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            leftSegments :=
        render_retainedCutSegments leftSegments
      _ = left.toList := by
        simpa [leftSegments] using
          SemigroupBasis.CoRoots.S5_441.render_exactCutDecomposition
            left.toList
  have rightRenderEq :
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          rightRetained = right.toList := by
    calc
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          rightRetained =
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            rightSegments :=
        render_retainedCutSegments rightSegments
      _ = right.toList := by
        simpa [rightSegments] using
          SemigroupBasis.CoRoots.S5_441.render_exactCutDecomposition
            right.toList
  rw [leftRenderEq] at leftDerivation
  rw [rightRenderEq] at rightDerivation
  exact ⟨common, leftDerivation, rightDerivation⟩

/-- Equal separator/simple signatures are derivationally sufficient. -/
theorem listDerivesOfSameSignature
    {left right : Word Nat}
    (same : SameSeparatorSimpleSignature left right) :
    ListDerives left.toList right.toList := by
  obtain ⟨common, leftDerivation, rightDerivation⟩ :=
    exactCutAssembly same.support same.exactCuts
      (SameSeparatorSimpleSignature.cappedCount_eq same)
  exact leftDerivation.trans rightDerivation.symm

/-- Word-level signature sufficiency for the B378 basis. -/
theorem derivesOfSameSignature
    {left right : Word Nat}
    (same : SameSeparatorSimpleSignature left right) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [S5_107.listWordOfCons, Word.toList] using
            S5_107.ListDerives.toWord
              (listDerivesOfSameSignature same)

end SemigroupBasis.CoRoots.S5_378
