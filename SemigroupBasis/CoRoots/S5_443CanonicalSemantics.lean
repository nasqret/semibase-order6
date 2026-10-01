import SemigroupBasis.CoRoots.S5_443CanonicalSyntax
import SemigroupBasis.CoRoots.S5_443Semantics

namespace SemigroupBasis.CoRoots.S5_443Family.CanonicalSemantics

open SemigroupBasis
open SemigroupBasis.Examples
open CanonicalSyntax
open S5_614Semantics

theorem repeatedBlock_eq_of_label_exponent
    {left right : EdmundsPeriodTwoRepeatedBlock}
    (labelEq : left.label = right.label)
    (exponentEq : left.exponent = right.exponent) :
    left = right :=
  edmundsPeriodTwoRepeatedBlock_eq_of_label_eq_exponent_eq
    labelEq exponentEq

private theorem sorted_eq_of_mem_iff
    {xs ys : List Nat}
    (sortedX : xs.Pairwise (· ≤ ·))
    (sortedY : ys.Pairwise (· ≤ ·))
    (nodupX : xs.Nodup) (nodupY : ys.Nodup)
    (sameMem : ∀ z, z ∈ xs ↔ z ∈ ys) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          have := (sameMem y).2 (List.Mem.head ys)
          contradiction
  | cons x xs ih =>
      cases ys with
      | nil =>
          have := (sameMem x).1 (List.Mem.head xs)
          contradiction
      | cons y ys =>
          have xInY := (sameMem x).1 (List.Mem.head xs)
          have yInX := (sameMem y).2 (List.Mem.head ys)
          have yLeX : y ≤ x := by
            by_cases hxy : x = y
            · omega
            · have xTail : x ∈ ys := by
                simpa [hxy] using xInY
              exact List.rel_of_pairwise_cons sortedY xTail
          have xLeY : x ≤ y := by
            by_cases hyx : y = x
            · omega
            · have yTail : y ∈ xs := by
                simpa [hyx] using yInX
              exact List.rel_of_pairwise_cons sortedX yTail
          have hxy : x = y := by omega
          subst y
          congr 1
          apply ih sortedX.tail sortedY.tail nodupX.tail nodupY.tail
          intro z
          by_cases hzx : z = x
          · subst z
            have hxnot : x ∉ xs := by
              intro hx
              exact (List.rel_of_pairwise_cons nodupX hx) rfl
            have hynot : x ∉ ys := by
              intro hy
              exact (List.rel_of_pairwise_cons nodupY hy) rfl
            simp [hxnot, hynot]
          · simpa [hzx] using sameMem z

theorem mem_renderRepeated_iff_label
    (z : Nat) :
    ∀ blocks : List EdmundsPeriodTwoRepeatedBlock,
      z ∈ renderEdmundsPeriodTwoRepeatedBlocks blocks ↔
        z ∈ blocks.map EdmundsPeriodTwoRepeatedBlock.label
  | [] => by
      simp [renderEdmundsPeriodTwoRepeatedBlocks]
  | block :: rest => by
      simp only [renderEdmundsPeriodTwoRepeatedBlocks,
        List.flatMap_cons, List.map_cons, List.mem_append,
        List.mem_cons]
      have current : z ∈ block.render ↔ z = block.label := by
        cases block <;>
          simp [EdmundsPeriodTwoRepeatedBlock.render,
            EdmundsPeriodTwoRepeatedBlock.toBlock,
            EdmundsPeriodTwoRepeatedBlock.label,
            EdmundsPeriodTwoBlock.render,
            EdmundsPeriodTwoBlock.label]
      have remaining :
          z ∈ List.flatMap EdmundsPeriodTwoRepeatedBlock.render rest ↔
            z ∈ rest.map EdmundsPeriodTwoRepeatedBlock.label := by
        simpa [renderEdmundsPeriodTwoRepeatedBlocks] using
          mem_renderRepeated_iff_label z rest
      exact or_congr current remaining

theorem mem_segment_render_iff_label
    (z : Nat) (segment : EdmundsPeriodTwoSegment) :
    z ∈ segment.render ↔ z ∈ segment.labels := by
  cases segment with
  | mk repeated singleton =>
      cases singleton <;>
        simp [EdmundsPeriodTwoSegment.render,
          EdmundsPeriodTwoSegment.labels,
          mem_renderRepeated_iff_label]

theorem mem_renderSegments_iff_label
    (z : Nat) :
    ∀ segments : List EdmundsPeriodTwoSegment,
      z ∈ renderEdmundsPeriodTwoSegments segments ↔
        z ∈ allEdmundsPeriodTwoSegmentLabels segments
  | [] => by
      simp [renderEdmundsPeriodTwoSegments,
        allEdmundsPeriodTwoSegmentLabels]
  | segment :: rest => by
      change
        z ∈ segment.render ++
              renderEdmundsPeriodTwoSegments rest ↔
          z ∈ segment.labels ++
              allEdmundsPeriodTwoSegmentLabels rest
      rw [List.mem_append, List.mem_append,
        mem_segment_render_iff_label,
        mem_renderSegments_iff_label]

theorem eval_tail_via_mask
    (segment : EdmundsPeriodTwoSegment)
    (rest : List EdmundsPeriodTwoSegment)
    (canonical : SegmentsCanonical (segment :: rest))
    (valuation : Nat → Fin 5) :
    listEval (maskValuation segment.labels valuation)
        (renderEdmundsPeriodTwoSegments (segment :: rest)) =
      listEval valuation (renderEdmundsPeriodTwoSegments rest) := by
  have prefixCovered :
      ∀ z, z ∈ segment.render → z ∈ segment.labels := by
    intro z hz
    exact (mem_segment_render_iff_label z segment).mp hz
  have suffixDisjoint :
      ∀ z, z ∈ renderEdmundsPeriodTwoSegments rest →
        z ∉ segment.labels := by
    intro z hz zFirst
    have zRest :
        z ∈ allEdmundsPeriodTwoSegmentLabels rest :=
      (mem_renderSegments_iff_label z rest).mp hz
    exact
      (edmundsPeriodTwoFirstSegmentDisjoint canonical z zFirst)
        zRest
  simpa [renderEdmundsPeriodTwoSegments] using
    listEval_mask_prefix segment.labels segment.render
      (renderEdmundsPeriodTwoSegments rest) valuation
      prefixCovered suffixDisjoint

theorem singleton_mem_split
    (z : Nat) :
    ∀ {segments : List EdmundsPeriodTwoSegment},
      z ∈ edmundsPeriodTwoSingletonLabels segments →
      ∃ before repeated after,
        segments =
          before ++
            ({ repeated := repeated, singleton := some z } :
              EdmundsPeriodTwoSegment) :: after
  | [], h => by
      simp [edmundsPeriodTwoSingletonLabels] at h
  | segment :: rest, h => by
      cases hs : segment.singleton with
      | none =>
          have tailMem :
              z ∈ edmundsPeriodTwoSingletonLabels rest := by
            simpa [edmundsPeriodTwoSingletonLabels, hs] using h
          obtain ⟨before, repeated, after, split⟩ :=
            singleton_mem_split z tailMem
          exact ⟨segment :: before, repeated, after, by
            simp [split]⟩
      | some x =>
          have casesMem :
              z = x ∨
                z ∈ edmundsPeriodTwoSingletonLabels rest := by
            simpa [edmundsPeriodTwoSingletonLabels, hs] using h
          rcases casesMem with rfl | tailMem
          · exact ⟨[], segment.repeated, rest, by
              cases segment
              simp at hs
              subst hs
              rfl⟩
          · obtain ⟨before, repeated, after, split⟩ :=
              singleton_mem_split z tailMem
            exact ⟨segment :: before, repeated, after, by
              simp [split]⟩

theorem prefixBefore_first_singleton
    (marker : Nat)
    (segment : EdmundsPeriodTwoSegment)
    (rest : List EdmundsPeriodTwoSegment)
    (singletonEq : segment.singleton = some marker)
    (countOne :
      (renderEdmundsPeriodTwoSegments
        (segment :: rest)).count marker = 1) :
    prefixBefore marker
        (renderEdmundsPeriodTwoSegments (segment :: rest)) =
      renderEdmundsPeriodTwoRepeatedBlocks segment.repeated := by
  cases segment with
  | mk repeated singleton =>
      simp only at singletonEq
      subst singleton
      simp only [renderEdmundsPeriodTwoSegments, List.flatMap_cons,
        EdmundsPeriodTwoSegment.render, Option.toList_some] at countOne ⊢
      have countOne' :
          (renderEdmundsPeriodTwoRepeatedBlocks repeated ++
            marker :: renderEdmundsPeriodTwoSegments rest).count marker =
              1 := by
        simpa [List.append_assoc] using countOne
      simpa [renderEdmundsPeriodTwoSegments, List.append_assoc] using
        prefixBefore_eq_of_split_count_one marker
          (renderEdmundsPeriodTwoRepeatedBlocks repeated)
          (renderEdmundsPeriodTwoSegments rest) countOne'

theorem first_singleton_prefix_mem_iff
    (marker selected : Nat)
    (segment : EdmundsPeriodTwoSegment)
    (rest : List EdmundsPeriodTwoSegment)
    (singletonEq : segment.singleton = some marker)
    (countOne :
      (renderEdmundsPeriodTwoSegments
        (segment :: rest)).count marker = 1) :
    selected ∈ prefixBefore marker
        (renderEdmundsPeriodTwoSegments (segment :: rest)) ↔
      selected ∈
        segment.repeated.map EdmundsPeriodTwoRepeatedBlock.label := by
  rw [prefixBefore_first_singleton marker segment rest
    singletonEq countOne]
  exact mem_renderRepeated_iff_label selected segment.repeated

theorem first_singleton_precedes_later
    (firstMarker laterMarker : Nat)
    (segment : EdmundsPeriodTwoSegment)
    (rest : List EdmundsPeriodTwoSegment)
    (canonical : SegmentsCanonical (segment :: rest))
    (firstEq : segment.singleton = some firstMarker)
    (_different : firstMarker ≠ laterMarker)
    (laterMem :
      laterMarker ∈ edmundsPeriodTwoSingletonLabels rest)
    (laterCount :
      (renderEdmundsPeriodTwoSegments
        (segment :: rest)).count laterMarker = 1) :
    firstMarker ∈ prefixBefore laterMarker
      (renderEdmundsPeriodTwoSegments (segment :: rest)) := by
  obtain ⟨before, repeated, after, restSplit⟩ :=
    singleton_mem_split laterMarker laterMem
  let prefixList :=
    segment.render ++
      renderEdmundsPeriodTwoSegments before ++
        renderEdmundsPeriodTwoRepeatedBlocks repeated
  let suffix := renderEdmundsPeriodTwoSegments after
  have rendered :
      renderEdmundsPeriodTwoSegments (segment :: rest) =
        prefixList ++ laterMarker :: suffix := by
    rw [restSplit]
    simp [renderEdmundsPeriodTwoSegments,
      prefixList, suffix, EdmundsPeriodTwoSegment.render,
      List.append_assoc]
  have splitCount :
      (prefixList ++ laterMarker :: suffix).count laterMarker = 1 := by
    rw [← rendered]
    exact laterCount
  rw [rendered,
    prefixBefore_eq_of_split_count_one laterMarker
      prefixList suffix splitCount]
  have markerInFirst : firstMarker ∈ segment.render := by
    cases segment with
    | mk segmentRepeated singleton =>
        simp only at firstEq
        subst singleton
        simp [EdmundsPeriodTwoSegment.render]
  exact List.mem_append_left _ <|
    List.mem_append_left _ markerInFirst

theorem first_singleton_excludes_later
    (firstMarker laterMarker : Nat)
    (segment : EdmundsPeriodTwoSegment)
    (rest : List EdmundsPeriodTwoSegment)
    (canonical : SegmentsCanonical (segment :: rest))
    (firstEq : segment.singleton = some firstMarker)
    (laterMem :
      laterMarker ∈ edmundsPeriodTwoSingletonLabels rest)
    (firstCount :
      (renderEdmundsPeriodTwoSegments
        (segment :: rest)).count firstMarker = 1) :
    laterMarker ∉ prefixBefore firstMarker
      (renderEdmundsPeriodTwoSegments (segment :: rest)) := by
  rw [prefixBefore_first_singleton firstMarker segment rest
    firstEq firstCount]
  intro laterInRepeated
  have laterFirst :
      laterMarker ∈ segment.labels := by
    have inLabels :=
      (mem_renderRepeated_iff_label laterMarker
        segment.repeated).mp laterInRepeated
    exact List.mem_append_left _ inLabels
  have laterRest :
      laterMarker ∈ allEdmundsPeriodTwoSegmentLabels rest := by
    obtain ⟨before, repeated, after, split⟩ :=
      singleton_mem_split laterMarker laterMem
    rw [split]
    simp [allEdmundsPeriodTwoSegmentLabels,
      EdmundsPeriodTwoSegment.labels]
  exact
    (edmundsPeriodTwoFirstSegmentDisjoint canonical
      laterMarker laterFirst) laterRest

private theorem first_repeated_labels_nodup
    {segment : EdmundsPeriodTwoSegment}
    {rest : List EdmundsPeriodTwoSegment}
    (canonical : SegmentsCanonical (segment :: rest)) :
    (segment.repeated.map
      EdmundsPeriodTwoRepeatedBlock.label).Nodup := by
  have labelsNodup :
      (segment.labels ++
        allEdmundsPeriodTwoSegmentLabels rest).Nodup := by
    simpa [allEdmundsPeriodTwoSegmentLabels] using canonical.1
  have segmentNodup := (List.nodup_append.mp labelsNodup).1
  exact (List.nodup_append.mp <| by
    simpa [EdmundsPeriodTwoSegment.labels] using segmentNodup).1

private theorem first_segment_render_ne_nil
    {segment : EdmundsPeriodTwoSegment}
    {rest : List EdmundsPeriodTwoSegment}
    (canonical : SegmentsCanonical (segment :: rest)) :
    segment.render ≠ [] := by
  cases repeatedEq : segment.repeated with
  | nil =>
      have some :=
        canonical.2.2.2 segment (List.Mem.head rest) repeatedEq
      cases singletonEq : segment.singleton with
      | none =>
          simp [singletonEq] at some
      | some x =>
          simp [EdmundsPeriodTwoSegment.render,
            repeatedEq, singletonEq]
  | cons block blocks =>
      cases block <;>
        simp [EdmundsPeriodTwoSegment.render,
          repeatedEq, renderEdmundsPeriodTwoRepeatedBlocks,
          EdmundsPeriodTwoRepeatedBlock.render,
          EdmundsPeriodTwoRepeatedBlock.toBlock,
          EdmundsPeriodTwoBlock.render]

private theorem rendered_segments_ne_nil
    {segment : EdmundsPeriodTwoSegment}
    {rest : List EdmundsPeriodTwoSegment}
    (canonical : SegmentsCanonical (segment :: rest)) :
    renderEdmundsPeriodTwoSegments (segment :: rest) ≠ [] := by
  intro empty
  have firstEmpty : segment.render = [] := by
    have := congrArg (fun xs => xs.take segment.render.length) empty
    simpa [renderEdmundsPeriodTwoSegments] using this
  exact first_segment_render_ne_nil canonical firstEmpty

private theorem repeated_label_mem_iff_render_mem
    (z : Nat) (blocks : List EdmundsPeriodTwoRepeatedBlock) :
    z ∈ blocks.map EdmundsPeriodTwoRepeatedBlock.label ↔
      z ∈ renderEdmundsPeriodTwoRepeatedBlocks blocks :=
  (mem_renderRepeated_iff_label z blocks).symm

/-- The exact table separates canonical segmented forms. Counts recover every
block tag, singleton-prefix tests align the separators, and masking removes an
agreed first segment before recursion. -/
theorem canonical_segments_eq_of_eval_eq
    {left right : List EdmundsPeriodTwoSegment}
    (leftCanonical : SegmentsCanonical left)
    (rightCanonical : SegmentsCanonical right)
    (equalEval :
      ∀ valuation : Nat → Fin 5,
        listEval valuation (renderEdmundsPeriodTwoSegments left) =
          listEval valuation (renderEdmundsPeriodTwoSegments right)) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons second rightRest =>
          have rightNonempty :
              renderEdmundsPeriodTwoSegments
                (second :: rightRest) ≠ [] :=
            rendered_segments_ne_nil rightCanonical
          obtain ⟨z, zMem⟩ :=
            List.exists_mem_of_ne_nil _ rightNonempty
          have rightPositive :
              0 <
                (renderEdmundsPeriodTwoSegments
                  (second :: rightRest)).count z :=
            List.count_pos_iff.mpr zMem
          have counts :=
            count_eq_of_equalEval
              (left := [])
              (right :=
                renderEdmundsPeriodTwoSegments
                  (second :: rightRest))
              (fun z => by simp)
              (renderEdmundsPeriodTwoSegments_count_le_three
                rightCanonical)
              (by simpa [renderEdmundsPeriodTwoSegments] using equalEval)
          have := counts z
          simp at this
          omega
  | cons first leftRest ih =>
      cases right with
      | nil =>
          have leftNonempty :
              renderEdmundsPeriodTwoSegments
                (first :: leftRest) ≠ [] :=
            rendered_segments_ne_nil leftCanonical
          obtain ⟨z, zMem⟩ :=
            List.exists_mem_of_ne_nil _ leftNonempty
          have leftPositive :
              0 <
                (renderEdmundsPeriodTwoSegments
                  (first :: leftRest)).count z :=
            List.count_pos_iff.mpr zMem
          have counts :=
            count_eq_of_equalEval
              (left :=
                renderEdmundsPeriodTwoSegments
                  (first :: leftRest))
              (right := [])
              (renderEdmundsPeriodTwoSegments_count_le_three
                leftCanonical)
              (fun z => by simp)
              (by simpa [renderEdmundsPeriodTwoSegments] using equalEval)
          have := counts z
          simp at this
          omega
      | cons second rightRest =>
          have countEq :
              ∀ z,
                (renderEdmundsPeriodTwoSegments
                  (first :: leftRest)).count z =
                (renderEdmundsPeriodTwoSegments
                  (second :: rightRest)).count z :=
            count_eq_of_equalEval
              (renderEdmundsPeriodTwoSegments_count_le_three
                leftCanonical)
              (renderEdmundsPeriodTwoSegments_count_le_three
                rightCanonical)
              equalEval
          cases firstSingleton : first.singleton with
          | none =>
              have leftRestEmpty : leftRest = [] :=
                leftCanonical.2.2.1 [] first leftRest rfl
                  firstSingleton
              subst leftRest
              cases secondSingleton : second.singleton with
              | some y =>
                  have yRightSingleton :
                      y ∈ edmundsPeriodTwoSingletonLabels
                        (second :: rightRest) := by
                    simp [edmundsPeriodTwoSingletonLabels,
                      secondSingleton]
                  have yRightCount :
                      (renderEdmundsPeriodTwoSegments
                        (second :: rightRest)).count y = 1 :=
                    (mem_edmundsPeriodTwoSingletonLabels_iff_count_one
                      rightCanonical y).mp yRightSingleton
                  have yLeftCount :
                      (renderEdmundsPeriodTwoSegments [first]).count y =
                        1 := by
                    rw [countEq y]
                    exact yRightCount
                  have yLeftSingleton :
                      y ∈ edmundsPeriodTwoSingletonLabels [first] :=
                    (mem_edmundsPeriodTwoSingletonLabels_iff_count_one
                      leftCanonical y).mpr yLeftCount
                  simp [edmundsPeriodTwoSingletonLabels,
                    firstSingleton] at yLeftSingleton
              | none =>
                  have rightRestEmpty : rightRest = [] :=
                    rightCanonical.2.2.1 [] second rightRest rfl
                      secondSingleton
                  subst rightRest
                  have firstSorted :=
                    leftCanonical.2.1 first (List.Mem.head [])
                  have secondSorted :=
                    rightCanonical.2.1 second (List.Mem.head [])
                  have firstNodup :=
                    first_repeated_labels_nodup leftCanonical
                  have secondNodup :=
                    first_repeated_labels_nodup rightCanonical
                  have sameLabelMem :
                      ∀ z,
                        z ∈ first.repeated.map
                            EdmundsPeriodTwoRepeatedBlock.label ↔
                          z ∈ second.repeated.map
                            EdmundsPeriodTwoRepeatedBlock.label := by
                    intro z
                    rw [repeated_label_mem_iff_render_mem,
                      repeated_label_mem_iff_render_mem,
                      List.count_pos_iff.symm,
                      List.count_pos_iff.symm]
                    simpa [renderEdmundsPeriodTwoSegments,
                      EdmundsPeriodTwoSegment.render,
                      firstSingleton, secondSingleton] using
                        congrArg (fun n => 0 < n) (countEq z)
                  have sameRenderedCount :
                      ∀ z,
                        (renderEdmundsPeriodTwoRepeatedBlocks
                          first.repeated).count z =
                          (renderEdmundsPeriodTwoRepeatedBlocks
                            second.repeated).count z := by
                    intro z
                    simpa [renderEdmundsPeriodTwoSegments,
                      EdmundsPeriodTwoSegment.render,
                      firstSingleton, secondSingleton] using countEq z
                  have repeatedEq :
                      first.repeated = second.repeated :=
                    edmundsPeriodTwoSortedRepeated_eq_of_label_mem_and_render_count
                      firstSorted secondSorted firstNodup secondNodup
                      sameLabelMem sameRenderedCount
                  cases first
                  cases second
                  simp_all
          | some x =>
              have xLeftSingleton :
                  x ∈ edmundsPeriodTwoSingletonLabels
                    (first :: leftRest) := by
                simp [edmundsPeriodTwoSingletonLabels,
                  firstSingleton]
              have xLeftCount :
                  (renderEdmundsPeriodTwoSegments
                    (first :: leftRest)).count x = 1 :=
                (mem_edmundsPeriodTwoSingletonLabels_iff_count_one
                  leftCanonical x).mp xLeftSingleton
              cases secondSingleton : second.singleton with
              | none =>
                  have rightRestEmpty : rightRest = [] :=
                    rightCanonical.2.2.1 [] second rightRest rfl
                      secondSingleton
                  subst rightRest
                  have xRightCount :
                      (renderEdmundsPeriodTwoSegments [second]).count x =
                        1 := by
                    rw [← countEq x]
                    exact xLeftCount
                  have xRightSingleton :
                      x ∈ edmundsPeriodTwoSingletonLabels [second] :=
                    (mem_edmundsPeriodTwoSingletonLabels_iff_count_one
                      rightCanonical x).mpr xRightCount
                  simp [edmundsPeriodTwoSingletonLabels,
                    secondSingleton] at xRightSingleton
              | some y =>
                  have yRightSingleton :
                      y ∈ edmundsPeriodTwoSingletonLabels
                        (second :: rightRest) := by
                    simp [edmundsPeriodTwoSingletonLabels,
                      secondSingleton]
                  have yRightCount :
                      (renderEdmundsPeriodTwoSegments
                        (second :: rightRest)).count y = 1 :=
                    (mem_edmundsPeriodTwoSingletonLabels_iff_count_one
                      rightCanonical y).mp yRightSingleton
                  have yLeftCount :
                      (renderEdmundsPeriodTwoSegments
                        (first :: leftRest)).count y = 1 := by
                    rw [countEq y]
                    exact yRightCount
                  have xRightCount :
                      (renderEdmundsPeriodTwoSegments
                        (second :: rightRest)).count x = 1 := by
                    rw [← countEq x]
                    exact xLeftCount
                  have hxy : x = y := by
                    apply Classical.byContradiction
                    intro different
                    have xRightSingleton :
                        x ∈ edmundsPeriodTwoSingletonLabels
                          (second :: rightRest) :=
                      (mem_edmundsPeriodTwoSingletonLabels_iff_count_one
                        rightCanonical x).mpr xRightCount
                    have xRightRest :
                        x ∈ edmundsPeriodTwoSingletonLabels rightRest := by
                      simpa [edmundsPeriodTwoSingletonLabels,
                        secondSingleton, different] using xRightSingleton
                    have yLeftSingleton :
                        y ∈ edmundsPeriodTwoSingletonLabels
                          (first :: leftRest) :=
                      (mem_edmundsPeriodTwoSingletonLabels_iff_count_one
                        leftCanonical y).mpr yLeftCount
                    have yLeftRest :
                        y ∈ edmundsPeriodTwoSingletonLabels leftRest := by
                      simpa [edmundsPeriodTwoSingletonLabels,
                        firstSingleton, Ne.symm different] using
                          yLeftSingleton
                    have leftPrefix :
                        x ∈ prefixBefore y
                          (renderEdmundsPeriodTwoSegments
                            (first :: leftRest)) :=
                      first_singleton_precedes_later x y first leftRest
                        leftCanonical firstSingleton different
                        yLeftRest yLeftCount
                    have rightNotPrefix :
                        x ∉ prefixBefore y
                          (renderEdmundsPeriodTwoSegments
                            (second :: rightRest)) :=
                      first_singleton_excludes_later y x second rightRest
                        rightCanonical secondSingleton xRightRest
                        yRightCount
                    have prefixEq :=
                      prefixBefore_mem_iff_of_equalEval
                        equalEval y x yLeftCount yRightCount
                    exact rightNotPrefix (prefixEq.mp leftPrefix)
                  subst y
                  have sameLabelMem :
                      ∀ z,
                        z ∈ first.repeated.map
                            EdmundsPeriodTwoRepeatedBlock.label ↔
                          z ∈ second.repeated.map
                            EdmundsPeriodTwoRepeatedBlock.label := by
                    intro z
                    rw [← first_singleton_prefix_mem_iff
                          x z first leftRest firstSingleton xLeftCount,
                      ← first_singleton_prefix_mem_iff
                          x z second rightRest secondSingleton xRightCount]
                    exact prefixBefore_mem_iff_of_equalEval
                      equalEval x z xLeftCount xRightCount
                  have firstSorted :=
                    leftCanonical.2.1 first
                      (List.Mem.head leftRest)
                  have secondSorted :=
                    rightCanonical.2.1 second
                      (List.Mem.head rightRest)
                  have firstNodup :=
                    first_repeated_labels_nodup leftCanonical
                  have secondNodup :=
                    first_repeated_labels_nodup rightCanonical
                  have repeatedEq :
                      first.repeated = second.repeated :=
                    edmundsPeriodTwoSortedRepeated_eq_of_label_mem_and_tag_counts
                      firstSorted secondSorted firstNodup secondNodup
                      sameLabelMem
                      (fun z =>
                        (renderEdmundsPeriodTwoSegments
                          (first :: leftRest)).count z)
                      (fun z =>
                        (renderEdmundsPeriodTwoSegments
                          (second :: rightRest)).count z)
                      countEq
                      (by
                        intro block blockMem
                        have globalMem :
                            block ∈
                              allEdmundsPeriodTwoRepeatedBlocks
                                (first :: leftRest) := by
                          simp [allEdmundsPeriodTwoRepeatedBlocks,
                            blockMem]
                        exact
                          (mem_edmundsPeriodTwoRepeatedBlock_iff_count_exponent
                            leftCanonical block).mp globalMem)
                      (by
                        intro block blockMem
                        have globalMem :
                            block ∈
                              allEdmundsPeriodTwoRepeatedBlocks
                                (second :: rightRest) := by
                          simp [allEdmundsPeriodTwoRepeatedBlocks,
                            blockMem]
                        exact
                          (mem_edmundsPeriodTwoRepeatedBlock_iff_count_exponent
                            rightCanonical block).mp globalMem)
                  have firstEq : first = second := by
                    cases first
                    cases second
                    simp_all
                  subst second
                  have tailEvalEqual :
                      ∀ valuation : Nat → Fin 5,
                        listEval valuation
                            (renderEdmundsPeriodTwoSegments leftRest) =
                          listEval valuation
                            (renderEdmundsPeriodTwoSegments rightRest) := by
                    intro valuation
                    let masked :=
                      maskValuation first.labels valuation
                    exact
                      (eval_tail_via_mask first leftRest
                        leftCanonical valuation).symm.trans <|
                        (equalEval masked).trans <|
                          eval_tail_via_mask first rightRest
                            rightCanonical valuation
                  have tailsEqual :=
                    ih (edmundsPeriodTwoTailCanonical leftCanonical)
                      (edmundsPeriodTwoTailCanonical rightCanonical)
                      tailEvalEqual
                  rw [tailsEqual]

end SemigroupBasis.CoRoots.S5_443Family.CanonicalSemantics
