import SemigroupBasis.Examples.UniqueSeparatorFourInvariant
import SemigroupBasis.Examples.UniqueSeparatorFourNormalForm
import SemigroupBasis.Examples.UniqueSeparatorFourListDerives
import SemigroupBasis.Examples.UniqueSeparatorFourSaturation

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Render each quadratic label as an adjacent square. -/
def uniqueSeparatorCanonicalRenderDoubles (labels : List Nat) : List Nat :=
  labels.flatMap (fun label => [label, label])

/-- A canonical square segment stores each quadratic label once, followed by
an optional globally linear separator. -/
structure UniqueSeparatorCanonicalSegment where
  quadratic : List Nat
  separator : Option Nat
deriving DecidableEq, Repr

def UniqueSeparatorCanonicalSegment.labels
    (segment : UniqueSeparatorCanonicalSegment) : List Nat :=
  segment.quadratic ++ segment.separator.toList

def UniqueSeparatorCanonicalSegment.render
    (segment : UniqueSeparatorCanonicalSegment) : List Nat :=
  uniqueSeparatorCanonicalRenderDoubles segment.quadratic ++
    segment.separator.toList

def uniqueSeparatorCanonicalLabels
    (segments : List UniqueSeparatorCanonicalSegment) : List Nat :=
  segments.flatMap UniqueSeparatorCanonicalSegment.labels

def uniqueSeparatorCanonicalRender
    (segments : List UniqueSeparatorCanonicalSegment) : List Nat :=
  segments.flatMap UniqueSeparatorCanonicalSegment.render

/-- Canonical square-segment lists have globally distinct labels, sorted
quadratic blocks, only a terminal separator-free block, and no empty block
without a separator. -/
def UniqueSeparatorCanonical
    (segments : List UniqueSeparatorCanonicalSegment) : Prop :=
  (uniqueSeparatorCanonicalLabels segments).Nodup ∧
    (∀ segment, segment ∈ segments →
      segment.quadratic.Pairwise (· ≤ ·)) ∧
    (∀ before segment rest,
      segments = before ++ segment :: rest →
      segment.separator = none → rest = []) ∧
    (∀ segment, segment ∈ segments →
      segment.quadratic = [] → segment.separator.isSome)

/-- The precise extra condition needed after endpoint capping and splitting:
no quadratic label crosses a surviving linear separator. Together with the
existing count-two theorem, this says both occurrences lie in one raw block. -/
def UniqueSeparatorRawSaturated
    (segments : List UniqueSeparatorSquareSegment) : Prop :=
  ∀ before segment rest separator,
    segments = before ++ segment :: rest →
    segment.separator = some separator →
    UniqueSeparatorFourSupportsDisjoint
      (uniqueSeparatorRenderSquareSegments before ++ segment.quadratic)
      (uniqueSeparatorRenderSquareSegments rest)

/-- The concrete saturation phase supplies exactly the raw separator
condition required by canonical square-block normalization. -/
theorem uniqueSeparatorSplitLinear_saturate_rawSaturated
    (letters : List Nat) :
    UniqueSeparatorRawSaturated
      (uniqueSeparatorSplitLinear
        (uniqueSeparatorSaturate letters)) := by
  intro before segment rest separator segmentsShape separatorShape
  exact
    uniqueSeparatorSplitLinear_saturate_separatorDisjoint
      letters before segment rest separator
      segmentsShape separatorShape

/-- Output contract for the final normalizer. The construction phase must
produce canonical segments together with a basis derivation to their render. -/
structure UniqueSeparatorCanonicalization
    (source : List Nat) : Type where
  segments : List UniqueSeparatorCanonicalSegment
  canonical : UniqueSeparatorCanonical segments
  derives :
    UniqueSeparatorListDerives
      source (uniqueSeparatorCanonicalRender segments)

@[simp]
theorem uniqueSeparatorCanonicalRenderDoubles_nil :
    uniqueSeparatorCanonicalRenderDoubles [] = [] :=
  rfl

@[simp]
theorem uniqueSeparatorCanonicalRenderDoubles_cons
    (label : Nat) (labels : List Nat) :
    uniqueSeparatorCanonicalRenderDoubles (label :: labels) =
      label :: label :: uniqueSeparatorCanonicalRenderDoubles labels := by
  rfl

theorem uniqueSeparatorCanonicalRenderDoubles_append
    (left right : List Nat) :
    uniqueSeparatorCanonicalRenderDoubles (left ++ right) =
      uniqueSeparatorCanonicalRenderDoubles left ++
        uniqueSeparatorCanonicalRenderDoubles right := by
  simp [uniqueSeparatorCanonicalRenderDoubles, List.flatMap_append]

theorem uniqueSeparatorCanonicalRenderDoubles_count
    (tested : Nat) :
    ∀ labels : List Nat,
      (uniqueSeparatorCanonicalRenderDoubles labels).count tested =
        2 * labels.count tested
  | [] => by simp
  | label :: labels => by
      rw [uniqueSeparatorCanonicalRenderDoubles_cons]
      simp only [List.count_cons]
      rw [uniqueSeparatorCanonicalRenderDoubles_count tested labels]
      split <;> omega

theorem uniqueSeparatorCanonicalRenderDoubles_mem_iff
    (tested : Nat) :
    ∀ labels : List Nat,
      tested ∈ uniqueSeparatorCanonicalRenderDoubles labels ↔
        tested ∈ labels
  | [] => by simp
  | label :: labels => by
      rw [uniqueSeparatorCanonicalRenderDoubles_cons]
      simp [uniqueSeparatorCanonicalRenderDoubles_mem_iff tested labels]

theorem uniqueSeparatorCanonicalRenderDoubles_eq_nil_iff
    (labels : List Nat) :
    uniqueSeparatorCanonicalRenderDoubles labels = [] ↔ labels = [] := by
  constructor
  · intro renderedEmpty
    cases labels with
    | nil => rfl
    | cons label labels =>
        simp at renderedEmpty
  · rintro rfl
    rfl

theorem uniqueSeparatorCanonicalRender_append
    (left right : List UniqueSeparatorCanonicalSegment) :
    uniqueSeparatorCanonicalRender (left ++ right) =
      uniqueSeparatorCanonicalRender left ++
        uniqueSeparatorCanonicalRender right := by
  simp [uniqueSeparatorCanonicalRender, List.flatMap_append]

theorem uniqueSeparatorCanonicalLabels_append
    (left right : List UniqueSeparatorCanonicalSegment) :
    uniqueSeparatorCanonicalLabels (left ++ right) =
      uniqueSeparatorCanonicalLabels left ++
        uniqueSeparatorCanonicalLabels right := by
  simp [uniqueSeparatorCanonicalLabels, List.flatMap_append]

theorem uniqueSeparatorCanonicalRender_mem_iff
    (tested : Nat) :
    ∀ segments : List UniqueSeparatorCanonicalSegment,
      tested ∈ uniqueSeparatorCanonicalRender segments ↔
        tested ∈ uniqueSeparatorCanonicalLabels segments
  | [] => by simp [uniqueSeparatorCanonicalRender,
      uniqueSeparatorCanonicalLabels]
  | segment :: rest => by
      simp only [uniqueSeparatorCanonicalRender,
        uniqueSeparatorCanonicalLabels, List.flatMap_cons,
        List.mem_append]
      change
        tested ∈ segment.render ∨
            tested ∈ uniqueSeparatorCanonicalRender rest ↔
          tested ∈ segment.labels ∨
            tested ∈ uniqueSeparatorCanonicalLabels rest
      rw [uniqueSeparatorCanonicalRender_mem_iff tested rest]
      cases segment with
      | mk quadratic separator =>
          cases separator <;>
            simp [UniqueSeparatorCanonicalSegment.render,
              UniqueSeparatorCanonicalSegment.labels,
              uniqueSeparatorCanonicalRenderDoubles_mem_iff]

theorem uniqueSeparatorCanonicalRender_count (tested : Nat) :
    ∀ segments : List UniqueSeparatorCanonicalSegment,
      (uniqueSeparatorCanonicalRender segments).count tested =
        2 * (segments.flatMap
            UniqueSeparatorCanonicalSegment.quadratic).count tested +
          (segments.filterMap
            UniqueSeparatorCanonicalSegment.separator).count tested
  | [] => by simp [uniqueSeparatorCanonicalRender]
  | segment :: rest => by
      rw [show
        uniqueSeparatorCanonicalRender (segment :: rest) =
          segment.render ++ uniqueSeparatorCanonicalRender rest by rfl]
      rw [List.count_append]
      cases segment with
      | mk quadratic separator =>
          cases separator with
          | none =>
              simp only [UniqueSeparatorCanonicalSegment.render,
                Option.toList_none, List.append_nil,
                List.flatMap_cons, List.filterMap_cons_none]
              rw [uniqueSeparatorCanonicalRenderDoubles_count,
                uniqueSeparatorCanonicalRender_count]
              rw [List.count_append]
              omega
          | some separator =>
              change
                (uniqueSeparatorCanonicalRenderDoubles quadratic ++
                    [separator]).count tested +
                    (uniqueSeparatorCanonicalRender rest).count tested =
                  2 * (quadratic ++
                    rest.flatMap
                      UniqueSeparatorCanonicalSegment.quadratic).count tested +
                    (separator :: rest.filterMap
                      UniqueSeparatorCanonicalSegment.separator).count tested
              rw [List.count_append,
                uniqueSeparatorCanonicalRenderDoubles_count,
                uniqueSeparatorCanonicalRender_count,
                List.count_append]
              simp only [List.count_cons, List.count_nil, Nat.zero_add]
              omega

theorem uniqueSeparatorCanonicalLabels_count (tested : Nat) :
    ∀ segments : List UniqueSeparatorCanonicalSegment,
      (uniqueSeparatorCanonicalLabels segments).count tested =
        (segments.flatMap
            UniqueSeparatorCanonicalSegment.quadratic).count tested +
          (segments.filterMap
            UniqueSeparatorCanonicalSegment.separator).count tested
  | [] => by simp [uniqueSeparatorCanonicalLabels]
  | segment :: rest => by
      rw [show
        uniqueSeparatorCanonicalLabels (segment :: rest) =
          segment.labels ++ uniqueSeparatorCanonicalLabels rest by rfl]
      rw [List.count_append]
      cases segment with
      | mk quadratic separator =>
          cases separator with
          | none =>
              simp only [UniqueSeparatorCanonicalSegment.labels,
                Option.toList_none, List.append_nil,
                List.flatMap_cons, List.filterMap_cons_none]
              rw [uniqueSeparatorCanonicalLabels_count,
                List.count_append]
              omega
          | some separator =>
              change
                (quadratic ++ [separator]).count tested +
                    (uniqueSeparatorCanonicalLabels rest).count tested =
                  (quadratic ++
                    rest.flatMap
                      UniqueSeparatorCanonicalSegment.quadratic).count tested +
                    (separator :: rest.filterMap
                      UniqueSeparatorCanonicalSegment.separator).count tested
              rw [List.count_append,
                uniqueSeparatorCanonicalLabels_count,
                List.count_append]
              simp only [List.count_cons, List.count_nil, Nat.zero_add]
              omega

theorem uniqueSeparatorCanonical_count_le_two
    {segments : List UniqueSeparatorCanonicalSegment}
    (canonical : UniqueSeparatorCanonical segments) (tested : Nat) :
    (uniqueSeparatorCanonicalRender segments).count tested ≤ 2 := by
  let quadraticLabels :=
    segments.flatMap UniqueSeparatorCanonicalSegment.quadratic
  let separatorLabels :=
    segments.filterMap UniqueSeparatorCanonicalSegment.separator
  have renderedCount :
      (uniqueSeparatorCanonicalRender segments).count tested =
        2 * quadraticLabels.count tested +
          separatorLabels.count tested := by
    simpa [quadraticLabels, separatorLabels] using
      uniqueSeparatorCanonicalRender_count tested segments
  have labelCount :
      (uniqueSeparatorCanonicalLabels segments).count tested =
        quadraticLabels.count tested + separatorLabels.count tested := by
    simpa [quadraticLabels, separatorLabels] using
      uniqueSeparatorCanonicalLabels_count tested segments
  have atMostOne :
      (uniqueSeparatorCanonicalLabels segments).count tested ≤ 1 := by
    rw [canonical.1.count]
    split <;> omega
  rw [labelCount] at atMostOne
  rw [renderedCount]
  omega

theorem uniqueSeparatorCanonical_quadratic_mem_iff_count_two
    {segments : List UniqueSeparatorCanonicalSegment}
    (canonical : UniqueSeparatorCanonical segments) (tested : Nat) :
    tested ∈ segments.flatMap
        UniqueSeparatorCanonicalSegment.quadratic ↔
      (uniqueSeparatorCanonicalRender segments).count tested = 2 := by
  let quadraticLabels :=
    segments.flatMap UniqueSeparatorCanonicalSegment.quadratic
  let separatorLabels :=
    segments.filterMap UniqueSeparatorCanonicalSegment.separator
  have renderedCount :
      (uniqueSeparatorCanonicalRender segments).count tested =
        2 * quadraticLabels.count tested +
          separatorLabels.count tested := by
    simpa [quadraticLabels, separatorLabels] using
      uniqueSeparatorCanonicalRender_count tested segments
  have labelCount :
      (uniqueSeparatorCanonicalLabels segments).count tested =
        quadraticLabels.count tested + separatorLabels.count tested := by
    simpa [quadraticLabels, separatorLabels] using
      uniqueSeparatorCanonicalLabels_count tested segments
  have atMostOne :
      quadraticLabels.count tested + separatorLabels.count tested ≤ 1 := by
    rw [← labelCount, canonical.1.count]
    split <;> omega
  change tested ∈ quadraticLabels ↔ _
  constructor
  · intro member
    have positive : 0 < quadraticLabels.count tested :=
      List.count_pos_iff.mpr member
    rw [renderedCount]
    omega
  · intro countTwo
    rw [renderedCount] at countTwo
    have positive : 0 < quadraticLabels.count tested := by omega
    exact List.count_pos_iff.mp positive

theorem uniqueSeparatorCanonical_separator_mem_iff_count_one
    {segments : List UniqueSeparatorCanonicalSegment}
    (canonical : UniqueSeparatorCanonical segments) (tested : Nat) :
    tested ∈ segments.filterMap
        UniqueSeparatorCanonicalSegment.separator ↔
      (uniqueSeparatorCanonicalRender segments).count tested = 1 := by
  let quadraticLabels :=
    segments.flatMap UniqueSeparatorCanonicalSegment.quadratic
  let separatorLabels :=
    segments.filterMap UniqueSeparatorCanonicalSegment.separator
  have renderedCount :
      (uniqueSeparatorCanonicalRender segments).count tested =
        2 * quadraticLabels.count tested +
          separatorLabels.count tested := by
    simpa [quadraticLabels, separatorLabels] using
      uniqueSeparatorCanonicalRender_count tested segments
  have labelCount :
      (uniqueSeparatorCanonicalLabels segments).count tested =
        quadraticLabels.count tested + separatorLabels.count tested := by
    simpa [quadraticLabels, separatorLabels] using
      uniqueSeparatorCanonicalLabels_count tested segments
  have atMostOne :
      quadraticLabels.count tested + separatorLabels.count tested ≤ 1 := by
    rw [← labelCount, canonical.1.count]
    split <;> omega
  change tested ∈ separatorLabels ↔ _
  constructor
  · intro member
    have positive : 0 < separatorLabels.count tested :=
      List.count_pos_iff.mpr member
    rw [renderedCount]
    omega
  · intro countOne
    rw [renderedCount] at countOne
    have positive : 0 < separatorLabels.count tested := by omega
    exact List.count_pos_iff.mp positive

private theorem uniqueSeparatorSortedNodup_eq_of_mem_iff
    {left right : List Nat}
    (leftSorted : left.Pairwise (· ≤ ·))
    (rightSorted : right.Pairwise (· ≤ ·))
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (sameMem : ∀ label, label ∈ left ↔ label ∈ right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          have := (sameMem head).2 (List.Mem.head tail)
          contradiction
  | cons leftHead leftTail ih =>
      cases right with
      | nil =>
          have := (sameMem leftHead).1 (List.Mem.head leftTail)
          contradiction
      | cons rightHead rightTail =>
          have leftHeadInRight :=
            (sameMem leftHead).1 (List.Mem.head leftTail)
          have rightHeadInLeft :=
            (sameMem rightHead).2 (List.Mem.head rightTail)
          have rightHeadLeLeftHead : rightHead ≤ leftHead := by
            by_cases equal : leftHead = rightHead
            · omega
            · have tailMember : leftHead ∈ rightTail := by
                simpa [equal] using leftHeadInRight
              exact List.rel_of_pairwise_cons rightSorted tailMember
          have leftHeadLeRightHead : leftHead ≤ rightHead := by
            by_cases equal : rightHead = leftHead
            · omega
            · have tailMember : rightHead ∈ leftTail := by
                simpa [equal] using rightHeadInLeft
              exact List.rel_of_pairwise_cons leftSorted tailMember
          have headsEqual : leftHead = rightHead := by omega
          subst rightHead
          congr 1
          apply ih leftSorted.tail rightSorted.tail
            leftNodup.tail rightNodup.tail
          intro label
          by_cases equal : label = leftHead
          · subst label
            have leftAbsent : leftHead ∉ leftTail := by
              simpa using (List.nodup_cons.mp leftNodup).1
            have rightAbsent : leftHead ∉ rightTail := by
              simpa using (List.nodup_cons.mp rightNodup).1
            simp [leftAbsent, rightAbsent]
          · simpa [equal] using sameMem label

theorem uniqueSeparatorCanonical_tail
    {segment : UniqueSeparatorCanonicalSegment}
    {rest : List UniqueSeparatorCanonicalSegment}
    (canonical : UniqueSeparatorCanonical (segment :: rest)) :
    UniqueSeparatorCanonical rest := by
  have labelsNodup :
      (segment.labels ++ uniqueSeparatorCanonicalLabels rest).Nodup := by
    simpa [uniqueSeparatorCanonicalLabels] using canonical.1
  refine ⟨(List.nodup_append.mp labelsNodup).2.1, ?_, ?_, ?_⟩
  · intro candidate member
    exact canonical.2.1 candidate (List.Mem.tail segment member)
  · intro before candidate tail split separatorNone
    exact canonical.2.2.1 (segment :: before) candidate tail
      (by simpa [split]) separatorNone
  · intro candidate member quadraticEmpty
    exact canonical.2.2.2 candidate
      (List.Mem.tail segment member) quadraticEmpty

theorem uniqueSeparatorCanonical_firstLabels_disjoint
    {segment : UniqueSeparatorCanonicalSegment}
    {rest : List UniqueSeparatorCanonicalSegment}
    (canonical : UniqueSeparatorCanonical (segment :: rest)) :
    ∀ label, label ∈ segment.labels →
      label ∉ uniqueSeparatorCanonicalLabels rest := by
  have labelsNodup :
      (segment.labels ++ uniqueSeparatorCanonicalLabels rest).Nodup := by
    simpa [uniqueSeparatorCanonicalLabels] using canonical.1
  exact fun label firstMember tailMember =>
    (List.nodup_append.mp labelsNodup).2.2
      label firstMember label tailMember rfl

theorem uniqueSeparatorCanonical_firstQuadratic_nodup
    {segment : UniqueSeparatorCanonicalSegment}
    {rest : List UniqueSeparatorCanonicalSegment}
    (canonical : UniqueSeparatorCanonical (segment :: rest)) :
    segment.quadratic.Nodup := by
  have firstLabelsNodup : segment.labels.Nodup := by
    have labelsNodup :
        (segment.labels ++ uniqueSeparatorCanonicalLabels rest).Nodup := by
      simpa [uniqueSeparatorCanonicalLabels] using canonical.1
    exact (List.nodup_append.mp labelsNodup).1
  cases segment with
  | mk quadratic separator =>
      cases separator with
      | none =>
          simpa [UniqueSeparatorCanonicalSegment.labels] using
            firstLabelsNodup
      | some value =>
          have appended :=
            (List.nodup_append.mp firstLabelsNodup).1
          simpa [UniqueSeparatorCanonicalSegment.labels] using appended

theorem uniqueSeparatorCanonical_segment_render_mem_iff
    (tested : Nat) (segment : UniqueSeparatorCanonicalSegment) :
    tested ∈ segment.render ↔ tested ∈ segment.labels := by
  cases segment with
  | mk quadratic separator =>
      cases separator <;>
        simp [UniqueSeparatorCanonicalSegment.render,
          UniqueSeparatorCanonicalSegment.labels,
          uniqueSeparatorCanonicalRenderDoubles_mem_iff]

theorem uniqueSeparatorCanonical_segment_render_ne_nil
    {segments : List UniqueSeparatorCanonicalSegment}
    (canonical : UniqueSeparatorCanonical segments)
    {segment : UniqueSeparatorCanonicalSegment}
    (member : segment ∈ segments) :
    segment.render ≠ [] := by
  cases segment with
  | mk quadratic separator =>
      cases separator with
      | none =>
          intro renderedEmpty
          have quadraticEmpty : quadratic = [] :=
            (uniqueSeparatorCanonicalRenderDoubles_eq_nil_iff
              quadratic).mp <| by
                simpa [UniqueSeparatorCanonicalSegment.render] using
                  renderedEmpty
          have separatorSome :=
            canonical.2.2.2
              ⟨quadratic, none⟩ member quadraticEmpty
          simp at separatorSome
      | some value =>
          simp [UniqueSeparatorCanonicalSegment.render]

theorem uniqueSeparatorCanonicalRender_ne_nil_of_cons
    {segment : UniqueSeparatorCanonicalSegment}
    {rest : List UniqueSeparatorCanonicalSegment}
    (canonical : UniqueSeparatorCanonical (segment :: rest)) :
    uniqueSeparatorCanonicalRender (segment :: rest) ≠ [] := by
  intro renderedEmpty
  have firstEmpty : segment.render = [] := by
    have appended :
        segment.render ++ uniqueSeparatorCanonicalRender rest = [] := by
      simpa [uniqueSeparatorCanonicalRender] using renderedEmpty
    exact (List.append_eq_nil_iff.mp appended).1
  exact
    uniqueSeparatorCanonical_segment_render_ne_nil canonical
      (List.Mem.head rest) firstEmpty

theorem uniqueSeparatorCanonicalRender_eq_nil_iff
    {segments : List UniqueSeparatorCanonicalSegment}
    (canonical : UniqueSeparatorCanonical segments) :
    uniqueSeparatorCanonicalRender segments = [] ↔ segments = [] := by
  constructor
  · intro renderedEmpty
    cases segments with
    | nil => rfl
    | cons segment rest =>
        exact False.elim <|
          uniqueSeparatorCanonicalRender_ne_nil_of_cons canonical
            renderedEmpty
  · rintro rfl
    rfl

private theorem uniqueSeparatorCanonical_append_separator_injective
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
        uniqueSeparatorCanonical_append_separator_injective
          leftAbsence.2 rightAbsence.2 restEquality
      exact
        ⟨congrArg (List.cons leftHead) tailEquality.1,
          tailEquality.2⟩

theorem uniqueSeparatorCanonical_firstExactCut
    {segment : UniqueSeparatorCanonicalSegment}
    {rest : List UniqueSeparatorCanonicalSegment}
    (canonical : UniqueSeparatorCanonical (segment :: rest))
    {separator : Nat}
    (separatorEq : segment.separator = some separator) :
    UniqueSeparatorFourExactCut
      (uniqueSeparatorCanonicalRender (segment :: rest))
      (uniqueSeparatorCanonicalRenderDoubles segment.quadratic)
      separator
      (uniqueSeparatorCanonicalRender rest) := by
  have separatorMember :
      separator ∈
        (segment :: rest).filterMap
          UniqueSeparatorCanonicalSegment.separator := by
    simp [separatorEq]
  have countOne :
      (uniqueSeparatorCanonicalRender (segment :: rest)).count
          separator = 1 :=
    (uniqueSeparatorCanonical_separator_mem_iff_count_one
      canonical separator).mp separatorMember
  have split :
      uniqueSeparatorCanonicalRender (segment :: rest) =
        uniqueSeparatorCanonicalRenderDoubles segment.quadratic ++
          separator :: uniqueSeparatorCanonicalRender rest := by
    cases segment with
    | mk quadratic candidate =>
        simp only at separatorEq
        subst candidate
        simp [uniqueSeparatorCanonicalRender,
          UniqueSeparatorCanonicalSegment.render]
  have disjoint :
      UniqueSeparatorFourSupportsDisjoint
        (uniqueSeparatorCanonicalRenderDoubles segment.quadratic)
        (uniqueSeparatorCanonicalRender rest) := by
    intro label leftMember rightMember
    have quadraticMember : label ∈ segment.quadratic :=
      (uniqueSeparatorCanonicalRenderDoubles_mem_iff
        label segment.quadratic).mp leftMember
    have firstLabelMember : label ∈ segment.labels := by
      simp [UniqueSeparatorCanonicalSegment.labels, quadraticMember]
    have tailLabelMember :
        label ∈ uniqueSeparatorCanonicalLabels rest :=
      (uniqueSeparatorCanonicalRender_mem_iff label rest).mp rightMember
    exact
      uniqueSeparatorCanonical_firstLabels_disjoint canonical
        label firstLabelMember tailLabelMember
  exact ⟨split, countOne, disjoint⟩

private theorem uniqueSeparatorExactCut_separator_not_left
    {letters left right : List Nat} {separator : Nat}
    (cut : UniqueSeparatorFourExactCut letters left separator right) :
    separator ∉ left := by
  intro member
  have positive : 0 < left.count separator :=
    List.count_pos_iff.mpr member
  have countOne := cut.2.1
  rw [cut.1, List.count_append, List.count_cons_self] at countOne
  omega

private theorem uniqueSeparatorExactCut_separator_not_right
    {letters left right : List Nat} {separator : Nat}
    (cut : UniqueSeparatorFourExactCut letters left separator right) :
    separator ∉ right := by
  intro member
  have positive : 0 < right.count separator :=
    List.count_pos_iff.mpr member
  have countOne := cut.2.1
  rw [cut.1, List.count_append, List.count_cons_self] at countOne
  omega

private theorem uniqueSeparatorExactCut_left_mem
    {letters left right : List Nat} {separator tested : Nat}
    (cut : UniqueSeparatorFourExactCut letters left separator right)
    (member : tested ∈ left) :
    tested ∈ letters := by
  rw [cut.1]
  exact List.mem_append_left _ member

private theorem uniqueSeparatorExactCut_right_mem
    {letters left right : List Nat} {separator tested : Nat}
    (cut : UniqueSeparatorFourExactCut letters left separator right)
    (member : tested ∈ right) :
    tested ∈ letters := by
  rw [cut.1]
  exact List.mem_append_right _ (List.Mem.tail separator member)

private theorem uniqueSeparatorExactCut_addPrefix
    {letters left right pre : List Nat} {separator : Nat}
    (cut : UniqueSeparatorFourExactCut letters left separator right)
    (separatorNotPrefix : separator ∉ pre)
    (prefixDisjointRight :
      UniqueSeparatorFourSupportsDisjoint pre right) :
    UniqueSeparatorFourExactCut
      (pre ++ letters) (pre ++ left) separator right := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cut.1]
    simp [List.append_assoc]
  · rw [List.count_append,
      List.count_eq_zero.mpr separatorNotPrefix, cut.2.1]
  · intro tested member rightMember
    rcases List.mem_append.mp member with prefixMember | leftMember
    · exact prefixDisjointRight tested prefixMember rightMember
    · exact cut.2.2 tested leftMember rightMember

private theorem uniqueSeparatorExactCut_dropPrefix
    {separator : Nat} :
    ∀ {pre letters left right : List Nat},
      separator ∉ pre →
      UniqueSeparatorFourExactCut
          (pre ++ letters) left separator right →
      ∃ tailLeft,
        left = pre ++ tailLeft ∧
          UniqueSeparatorFourExactCut
            letters tailLeft separator right
  | [], letters, left, right, _, cut => by
      exact ⟨left, by simp, by simpa using cut⟩
  | prefixHead :: prefixTail, letters, left, right,
      separatorNotPrefix, cut => by
      have headDifferent : prefixHead ≠ separator := by
        intro equality
        subst prefixHead
        exact separatorNotPrefix (by simp)
      cases left with
      | nil =>
          have headsEqual : prefixHead = separator := by
            simpa [List.cons_append] using
              congrArg List.head? cut.1
          exact False.elim (headDifferent headsEqual)
      | cons leftHead leftTail =>
          have splitTail :
              prefixTail ++ letters =
                leftTail ++ separator :: right := by
            have split := cut.1
            simp only [List.cons_append, List.cons.injEq] at split
            exact split.2
          have headEqual : prefixHead = leftHead := by
            have split := cut.1
            simp only [List.cons_append, List.cons.injEq] at split
            exact split.1
          subst leftHead
          have tailCount :
              (prefixTail ++ letters).count separator = 1 := by
            have fullCount := cut.2.1
            simp only [List.cons_append,
              List.count_cons_of_ne headDifferent] at fullCount
            exact fullCount
          have tailDisjoint :
              UniqueSeparatorFourSupportsDisjoint leftTail right := by
            intro tested leftMember rightMember
            exact cut.2.2 tested
              (List.Mem.tail prefixHead leftMember) rightMember
          have tailCut :
              UniqueSeparatorFourExactCut
                (prefixTail ++ letters) leftTail separator right :=
            ⟨splitTail, tailCount, tailDisjoint⟩
          have separatorNotTail : separator ∉ prefixTail := by
            intro member
            exact separatorNotPrefix
              (List.Mem.tail prefixHead member)
          obtain ⟨tailLeft, leftEq, reducedCut⟩ :=
            uniqueSeparatorExactCut_dropPrefix
              separatorNotTail tailCut
          exact
            ⟨tailLeft, by simp [leftEq], reducedCut⟩

theorem uniqueSeparatorCanonical_firstRender_disjoint
    {segment : UniqueSeparatorCanonicalSegment}
    {rest : List UniqueSeparatorCanonicalSegment}
    (canonical : UniqueSeparatorCanonical (segment :: rest)) :
    UniqueSeparatorFourSupportsDisjoint
      segment.render (uniqueSeparatorCanonicalRender rest) := by
  intro tested firstMember tailMember
  have firstLabelMember : tested ∈ segment.labels :=
    (uniqueSeparatorCanonical_segment_render_mem_iff
      tested segment).mp firstMember
  have tailLabelMember :
      tested ∈ uniqueSeparatorCanonicalLabels rest :=
    (uniqueSeparatorCanonicalRender_mem_iff tested rest).mp tailMember
  exact
    uniqueSeparatorCanonical_firstLabels_disjoint canonical
      tested firstLabelMember tailLabelMember

/-- Equality of support and of every exact separator-cut signature. This is
the semantic information about canonical words used by the injectivity proof. -/
def UniqueSeparatorCanonicalSameSignature
    (left right : List UniqueSeparatorCanonicalSegment) : Prop :=
  (∀ tested,
      tested ∈ uniqueSeparatorCanonicalRender left ↔
        tested ∈ uniqueSeparatorCanonicalRender right) ∧
    (∀ {leftPrefix leftSuffix separator},
      UniqueSeparatorFourExactCut
          (uniqueSeparatorCanonicalRender left)
          leftPrefix separator leftSuffix →
      ∃ rightPrefix rightSuffix,
        UniqueSeparatorFourExactCut
            (uniqueSeparatorCanonicalRender right)
            rightPrefix separator rightSuffix ∧
          (∀ tested, tested ∈ rightPrefix ↔ tested ∈ leftPrefix) ∧
          (∀ tested, tested ∈ rightSuffix ↔ tested ∈ leftSuffix)) ∧
    (∀ {rightPrefix rightSuffix separator},
      UniqueSeparatorFourExactCut
          (uniqueSeparatorCanonicalRender right)
          rightPrefix separator rightSuffix →
      ∃ leftPrefix leftSuffix,
        UniqueSeparatorFourExactCut
            (uniqueSeparatorCanonicalRender left)
            leftPrefix separator leftSuffix ∧
          (∀ tested, tested ∈ leftPrefix ↔ tested ∈ rightPrefix) ∧
          (∀ tested, tested ∈ leftSuffix ↔ tested ∈ rightSuffix))

theorem UniqueSeparatorCanonicalSameSignature.symm
    {left right : List UniqueSeparatorCanonicalSegment}
    (same : UniqueSeparatorCanonicalSameSignature left right) :
    UniqueSeparatorCanonicalSameSignature right left :=
  ⟨fun tested => (same.1 tested).symm, same.2.2, same.2.1⟩

private theorem uniqueSeparatorCanonical_tailTransport
    {segment : UniqueSeparatorCanonicalSegment}
    {sourceRest targetRest : List UniqueSeparatorCanonicalSegment}
    (sourceCanonical :
      UniqueSeparatorCanonical (segment :: sourceRest))
    (targetCanonical :
      UniqueSeparatorCanonical (segment :: targetRest))
    (transport :
      ∀ {sourcePrefix sourceSuffix separator},
        UniqueSeparatorFourExactCut
            (uniqueSeparatorCanonicalRender (segment :: sourceRest))
            sourcePrefix separator sourceSuffix →
        ∃ targetPrefix targetSuffix,
          UniqueSeparatorFourExactCut
              (uniqueSeparatorCanonicalRender (segment :: targetRest))
              targetPrefix separator targetSuffix ∧
            (∀ tested, tested ∈ targetPrefix ↔
              tested ∈ sourcePrefix) ∧
            (∀ tested, tested ∈ targetSuffix ↔
              tested ∈ sourceSuffix)) :
    ∀ {sourcePrefix sourceSuffix separator},
      UniqueSeparatorFourExactCut
          (uniqueSeparatorCanonicalRender sourceRest)
          sourcePrefix separator sourceSuffix →
      ∃ targetPrefix targetSuffix,
        UniqueSeparatorFourExactCut
            (uniqueSeparatorCanonicalRender targetRest)
            targetPrefix separator targetSuffix ∧
          (∀ tested, tested ∈ targetPrefix ↔
            tested ∈ sourcePrefix) ∧
          (∀ tested, tested ∈ targetSuffix ↔
            tested ∈ sourceSuffix) := by
  intro sourcePrefix sourceSuffix separator tailCut
  have sourceDisjoint :=
    uniqueSeparatorCanonical_firstRender_disjoint sourceCanonical
  have targetDisjoint :=
    uniqueSeparatorCanonical_firstRender_disjoint targetCanonical
  have separatorTailMember :
      separator ∈ uniqueSeparatorCanonicalRender sourceRest := by
    rw [tailCut.1]
    exact List.mem_append_right _ (List.Mem.head _)
  have separatorNotFirst : separator ∉ segment.render := by
    intro firstMember
    exact sourceDisjoint separator firstMember separatorTailMember
  have prefixDisjointSuffix :
      UniqueSeparatorFourSupportsDisjoint
        segment.render sourceSuffix := by
    intro tested firstMember suffixMember
    exact sourceDisjoint tested firstMember
      (uniqueSeparatorExactCut_right_mem tailCut suffixMember)
  have wholeCut :
      UniqueSeparatorFourExactCut
        (uniqueSeparatorCanonicalRender (segment :: sourceRest))
        (segment.render ++ sourcePrefix)
        separator sourceSuffix := by
    change
      UniqueSeparatorFourExactCut
        (segment.render ++ uniqueSeparatorCanonicalRender sourceRest)
        (segment.render ++ sourcePrefix) separator sourceSuffix
    exact uniqueSeparatorExactCut_addPrefix tailCut
      separatorNotFirst prefixDisjointSuffix
  obtain
    ⟨wholeTargetPrefix, targetSuffix, targetCut,
      prefixSupport, suffixSupport⟩ :=
    transport wholeCut
  obtain ⟨targetPrefix, wholePrefixEq, reducedCut⟩ :=
    uniqueSeparatorExactCut_dropPrefix separatorNotFirst <| by
      change
        UniqueSeparatorFourExactCut
          (segment.render ++ uniqueSeparatorCanonicalRender targetRest)
          wholeTargetPrefix separator targetSuffix
      exact targetCut
  refine ⟨targetPrefix, targetSuffix, reducedCut, ?_, suffixSupport⟩
  intro tested
  have targetPrefixInTail :
      tested ∈ targetPrefix →
        tested ∈ uniqueSeparatorCanonicalRender targetRest :=
    fun member => uniqueSeparatorExactCut_left_mem reducedCut member
  have sourcePrefixInTail :
      tested ∈ sourcePrefix →
        tested ∈ uniqueSeparatorCanonicalRender sourceRest :=
    fun member => uniqueSeparatorExactCut_left_mem tailCut member
  constructor
  · intro member
    have wholeMember :
        tested ∈ wholeTargetPrefix := by
      rw [wholePrefixEq]
      exact List.mem_append_right _ member
    have sourceWholeMember := (prefixSupport tested).1 wholeMember
    rcases List.mem_append.mp sourceWholeMember with
      firstMember | sourceMember
    · exact False.elim <|
        targetDisjoint tested firstMember
          (targetPrefixInTail member)
    · exact sourceMember
  · intro member
    have sourceWholeMember :
        tested ∈ segment.render ++ sourcePrefix :=
      List.mem_append_right _ member
    have targetWholeMember := (prefixSupport tested).2 sourceWholeMember
    rw [wholePrefixEq] at targetWholeMember
    rcases List.mem_append.mp targetWholeMember with
      firstMember | targetMember
    · exact False.elim <|
        sourceDisjoint tested firstMember
          (sourcePrefixInTail member)
    · exact targetMember

private theorem uniqueSeparatorCanonicalSameSignature_tail
    {segment : UniqueSeparatorCanonicalSegment}
    {leftRest rightRest : List UniqueSeparatorCanonicalSegment}
    (leftCanonical :
      UniqueSeparatorCanonical (segment :: leftRest))
    (rightCanonical :
      UniqueSeparatorCanonical (segment :: rightRest))
    (same :
      UniqueSeparatorCanonicalSameSignature
        (segment :: leftRest) (segment :: rightRest)) :
    UniqueSeparatorCanonicalSameSignature leftRest rightRest := by
  have leftDisjoint :=
    uniqueSeparatorCanonical_firstRender_disjoint leftCanonical
  have rightDisjoint :=
    uniqueSeparatorCanonical_firstRender_disjoint rightCanonical
  have supportEq :
      ∀ tested,
        tested ∈ uniqueSeparatorCanonicalRender leftRest ↔
          tested ∈ uniqueSeparatorCanonicalRender rightRest := by
    intro tested
    constructor
    · intro leftMember
      have wholeLeftMember :
          tested ∈
            uniqueSeparatorCanonicalRender (segment :: leftRest) := by
        exact List.mem_append_right segment.render leftMember
      have wholeRightMember := (same.1 tested).1 wholeLeftMember
      change
        tested ∈ segment.render ++
          uniqueSeparatorCanonicalRender rightRest at wholeRightMember
      rcases List.mem_append.mp wholeRightMember with
        firstMember | tailMember
      · exact False.elim <|
          leftDisjoint tested firstMember leftMember
      · exact tailMember
    · intro rightMember
      have wholeRightMember :
          tested ∈
            uniqueSeparatorCanonicalRender (segment :: rightRest) := by
        exact List.mem_append_right segment.render rightMember
      have wholeLeftMember := (same.1 tested).2 wholeRightMember
      change
        tested ∈ segment.render ++
          uniqueSeparatorCanonicalRender leftRest at wholeLeftMember
      rcases List.mem_append.mp wholeLeftMember with
        firstMember | tailMember
      · exact False.elim <|
          rightDisjoint tested firstMember rightMember
      · exact tailMember
  exact
    ⟨supportEq,
      uniqueSeparatorCanonical_tailTransport
        leftCanonical rightCanonical same.2.1,
      uniqueSeparatorCanonical_tailTransport
        rightCanonical leftCanonical same.2.2⟩

theorem uniqueSeparatorCanonical_exactCut_separator_mem
    {segments : List UniqueSeparatorCanonicalSegment}
    (canonical : UniqueSeparatorCanonical segments)
    {left right : List Nat} {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        (uniqueSeparatorCanonicalRender segments)
        left separator right) :
    separator ∈ segments.filterMap
        UniqueSeparatorCanonicalSegment.separator :=
  (uniqueSeparatorCanonical_separator_mem_iff_count_one
    canonical separator).mpr cut.2.1

/-- Canonical square-segment lists are determined by support and exact-cut
signatures. -/
theorem uniqueSeparatorCanonical_eq_of_sameSignature
    {left right : List UniqueSeparatorCanonicalSegment}
    (leftCanonical : UniqueSeparatorCanonical left)
    (rightCanonical : UniqueSeparatorCanonical right)
    (same : UniqueSeparatorCanonicalSameSignature left right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons first rest =>
          exfalso
          have renderedNonempty :=
            uniqueSeparatorCanonicalRender_ne_nil_of_cons rightCanonical
          obtain ⟨tested, testedMember⟩ :
              ∃ tested,
                tested ∈
                  uniqueSeparatorCanonicalRender (first :: rest) := by
            exact List.exists_mem_of_ne_nil _ renderedNonempty
          have impossible := (same.1 tested).2 testedMember
          simpa [uniqueSeparatorCanonicalRender] using impossible
  | cons first leftRest ih =>
      cases right with
      | nil =>
          exfalso
          have renderedNonempty :=
            uniqueSeparatorCanonicalRender_ne_nil_of_cons leftCanonical
          obtain ⟨tested, testedMember⟩ :
              ∃ tested,
                tested ∈
                  uniqueSeparatorCanonicalRender
                    (first :: leftRest) := by
            exact List.exists_mem_of_ne_nil _ renderedNonempty
          have impossible := (same.1 tested).1 testedMember
          simpa [uniqueSeparatorCanonicalRender] using impossible
      | cons second rightRest =>
          cases firstSeparatorEq : first.separator with
          | none =>
              have leftRestEmpty : leftRest = [] :=
                leftCanonical.2.2.1 [] first leftRest
                  (by rfl) firstSeparatorEq
              subst leftRest
              cases secondSeparatorEq : second.separator with
              | some separator =>
                  have rightCut :=
                    uniqueSeparatorCanonical_firstExactCut
                      rightCanonical secondSeparatorEq
                  obtain
                    ⟨leftPrefix, leftSuffix, leftCut, _, _⟩ :=
                    same.2.2 rightCut
                  have separatorMember :=
                    uniqueSeparatorCanonical_exactCut_separator_mem
                      leftCanonical leftCut
                  simpa [firstSeparatorEq] using separatorMember
              | none =>
                  have rightRestEmpty : rightRest = [] :=
                    rightCanonical.2.2.1 [] second rightRest
                      (by rfl) secondSeparatorEq
                  subst rightRest
                  have sameQuadraticMem :
                      ∀ tested,
                        tested ∈ first.quadratic ↔
                          tested ∈ second.quadratic := by
                    intro tested
                    rw [←
                      uniqueSeparatorCanonicalRenderDoubles_mem_iff
                        tested first.quadratic,
                      ←
                      uniqueSeparatorCanonicalRenderDoubles_mem_iff
                        tested second.quadratic]
                    have support := same.1 tested
                    simpa [uniqueSeparatorCanonicalRender,
                      UniqueSeparatorCanonicalSegment.render,
                      firstSeparatorEq, secondSeparatorEq] using support
                  have firstSorted :=
                    leftCanonical.2.1 first (List.Mem.head [])
                  have secondSorted :=
                    rightCanonical.2.1 second (List.Mem.head [])
                  have quadraticEq :
                      first.quadratic = second.quadratic :=
                    uniqueSeparatorSortedNodup_eq_of_mem_iff
                      firstSorted secondSorted
                      (uniqueSeparatorCanonical_firstQuadratic_nodup
                        leftCanonical)
                      (uniqueSeparatorCanonical_firstQuadratic_nodup
                        rightCanonical)
                      sameQuadraticMem
                  have firstEq : first = second := by
                    cases first
                    cases second
                    simp_all
                  rw [firstEq]
          | some leftSeparator =>
              cases secondSeparatorEq : second.separator with
              | none =>
                  have rightRestEmpty : rightRest = [] :=
                    rightCanonical.2.2.1 [] second rightRest
                      (by rfl) secondSeparatorEq
                  subst rightRest
                  have leftCut :=
                    uniqueSeparatorCanonical_firstExactCut
                      leftCanonical firstSeparatorEq
                  obtain
                    ⟨rightPrefix, rightSuffix, rightCut, _, _⟩ :=
                    same.2.1 leftCut
                  have separatorMember :=
                    uniqueSeparatorCanonical_exactCut_separator_mem
                      rightCanonical rightCut
                  simpa [secondSeparatorEq] using separatorMember
              | some rightSeparator =>
                  have leftCut :=
                    uniqueSeparatorCanonical_firstExactCut
                      leftCanonical firstSeparatorEq
                  obtain
                    ⟨rightPrefixAtLeftSeparator,
                      rightSuffixAtLeftSeparator,
                      rightCutAtLeftSeparator,
                      rightPrefixSupport, _⟩ :=
                    same.2.1 leftCut
                  have rightCut :=
                    uniqueSeparatorCanonical_firstExactCut
                      rightCanonical secondSeparatorEq
                  obtain
                    ⟨leftPrefixAtRightSeparator,
                      leftSuffixAtRightSeparator,
                      leftCutAtRightSeparator,
                      _, _⟩ :=
                    same.2.2 rightCut
                  have separatorsEqual :
                      leftSeparator = rightSeparator := by
                    apply Classical.byContradiction
                    intro separatorsDifferent
                    have leftSeparatorNotSecondRender :
                        leftSeparator ∉ second.render := by
                      intro member
                      have labelMember :
                          leftSeparator ∈ second.labels :=
                        (uniqueSeparatorCanonical_segment_render_mem_iff
                          leftSeparator second).mp member
                      have quadraticMember :
                          leftSeparator ∈ second.quadratic := by
                        simpa [UniqueSeparatorCanonicalSegment.labels,
                          secondSeparatorEq, separatorsDifferent] using
                            labelMember
                      have globalQuadraticMember :
                          leftSeparator ∈
                            (second :: rightRest).flatMap
                              UniqueSeparatorCanonicalSegment.quadratic := by
                        simp [quadraticMember]
                      have countTwo :=
                        (uniqueSeparatorCanonical_quadratic_mem_iff_count_two
                          rightCanonical leftSeparator).mp
                            globalQuadraticMember
                      have countOne :=
                        rightCutAtLeftSeparator.2.1
                      omega
                    obtain
                      ⟨rightTailPrefix, rightPrefixEq, _⟩ :=
                      uniqueSeparatorExactCut_dropPrefix
                        leftSeparatorNotSecondRender <| by
                          change
                            UniqueSeparatorFourExactCut
                              (second.render ++
                                uniqueSeparatorCanonicalRender rightRest)
                              rightPrefixAtLeftSeparator
                              leftSeparator
                              rightSuffixAtLeftSeparator
                          exact rightCutAtLeftSeparator
                    have rightSeparatorInTargetPrefix :
                        rightSeparator ∈
                          rightPrefixAtLeftSeparator := by
                      rw [rightPrefixEq]
                      apply List.mem_append_left
                      cases second with
                      | mk quadratic separator =>
                          simp only at secondSeparatorEq
                          subst separator
                          simp [UniqueSeparatorCanonicalSegment.render]
                    have rightSeparatorInLeftQuadraticRender :
                        rightSeparator ∈
                          uniqueSeparatorCanonicalRenderDoubles
                            first.quadratic :=
                      (rightPrefixSupport rightSeparator).1
                        rightSeparatorInTargetPrefix
                    have rightSeparatorInLeftQuadratic :
                        rightSeparator ∈ first.quadratic :=
                      (uniqueSeparatorCanonicalRenderDoubles_mem_iff
                        rightSeparator first.quadratic).mp
                          rightSeparatorInLeftQuadraticRender
                    have globalQuadraticMember :
                        rightSeparator ∈
                          (first :: leftRest).flatMap
                            UniqueSeparatorCanonicalSegment.quadratic := by
                      simp [rightSeparatorInLeftQuadratic]
                    have rightSeparatorCountTwo :
                        (uniqueSeparatorCanonicalRender
                          (first :: leftRest)).count rightSeparator = 2 := by
                      exact
                        (uniqueSeparatorCanonical_quadratic_mem_iff_count_two
                          leftCanonical rightSeparator).mp
                            globalQuadraticMember
                    have rightSeparatorCountOne :=
                      leftCutAtRightSeparator.2.1
                    omega
                  subst rightSeparator
                  have ownRightCut :=
                    uniqueSeparatorCanonical_firstExactCut
                      rightCanonical secondSeparatorEq
                  have leftSeparatorNotRightPrefix :
                      leftSeparator ∉ rightPrefixAtLeftSeparator :=
                    uniqueSeparatorExactCut_separator_not_left
                      rightCutAtLeftSeparator
                  have leftSeparatorNotOwnPrefix :
                      leftSeparator ∉
                        uniqueSeparatorCanonicalRenderDoubles
                          second.quadratic :=
                    uniqueSeparatorExactCut_separator_not_left ownRightCut
                  have splitEquality :
                      rightPrefixAtLeftSeparator ++
                          leftSeparator ::
                            rightSuffixAtLeftSeparator =
                        uniqueSeparatorCanonicalRenderDoubles
                            second.quadratic ++
                          leftSeparator ::
                            uniqueSeparatorCanonicalRender rightRest :=
                    rightCutAtLeftSeparator.1.symm.trans ownRightCut.1
                  have prefixAndSuffixEq :=
                    uniqueSeparatorCanonical_append_separator_injective
                      leftSeparatorNotRightPrefix
                      leftSeparatorNotOwnPrefix splitEquality
                  have sameQuadraticMem :
                      ∀ tested,
                        tested ∈ first.quadratic ↔
                          tested ∈ second.quadratic := by
                    intro tested
                    rw [←
                      uniqueSeparatorCanonicalRenderDoubles_mem_iff
                        tested first.quadratic,
                      ←
                      uniqueSeparatorCanonicalRenderDoubles_mem_iff
                        tested second.quadratic,
                      ← prefixAndSuffixEq.1]
                    exact (rightPrefixSupport tested).symm
                  have firstSorted :=
                    leftCanonical.2.1 first
                      (List.Mem.head leftRest)
                  have secondSorted :=
                    rightCanonical.2.1 second
                      (List.Mem.head rightRest)
                  have quadraticEq :
                      first.quadratic = second.quadratic :=
                    uniqueSeparatorSortedNodup_eq_of_mem_iff
                      firstSorted secondSorted
                      (uniqueSeparatorCanonical_firstQuadratic_nodup
                        leftCanonical)
                      (uniqueSeparatorCanonical_firstQuadratic_nodup
                        rightCanonical)
                      sameQuadraticMem
                  have firstEq : first = second := by
                    cases first
                    cases second
                    simp_all
                  subst second
                  have tailSame :=
                    uniqueSeparatorCanonicalSameSignature_tail
                      leftCanonical rightCanonical same
                  have tailEq :=
                    ih
                      (uniqueSeparatorCanonical_tail leftCanonical)
                      (uniqueSeparatorCanonical_tail rightCanonical)
                      tailSame
                  rw [tailEq]

/-- Equal `S4_69` term functions induce the same support and exact-cut
signature on their canonical renders. -/
theorem uniqueSeparatorCanonicalSameSignature_of_equalEval
    {left right : List UniqueSeparatorCanonicalSegment}
    (leftWord rightWord : Word Nat)
    (leftRendered :
      leftWord.toList = uniqueSeparatorCanonicalRender left)
    (rightRendered :
      rightWord.toList = uniqueSeparatorCanonicalRender right)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        uniqueSeparatorFour.semigroup.eval valuation leftWord =
          uniqueSeparatorFour.semigroup.eval valuation rightWord) :
    UniqueSeparatorCanonicalSameSignature left right := by
  have supportEq :
      ∀ tested,
        tested ∈ uniqueSeparatorCanonicalRender left ↔
          tested ∈ uniqueSeparatorCanonicalRender right := by
    intro tested
    have support :=
      uniqueSeparatorFourEqualEval_support_iff
        leftWord rightWord equalEval tested
    rwa [leftRendered, rightRendered] at support
  have forward :
      ∀ {leftPrefix leftSuffix separator},
        UniqueSeparatorFourExactCut
            (uniqueSeparatorCanonicalRender left)
            leftPrefix separator leftSuffix →
        ∃ rightPrefix rightSuffix,
          UniqueSeparatorFourExactCut
              (uniqueSeparatorCanonicalRender right)
              rightPrefix separator rightSuffix ∧
            (∀ tested, tested ∈ rightPrefix ↔
              tested ∈ leftPrefix) ∧
            (∀ tested, tested ∈ rightSuffix ↔
              tested ∈ leftSuffix) := by
    intro leftPrefix leftSuffix separator cut
    have wordCut :
        UniqueSeparatorFourExactCut
          leftWord.toList leftPrefix separator leftSuffix := by
      rwa [leftRendered]
    obtain
      ⟨rightPrefix, rightSuffix, targetCut,
        prefixSupport, suffixSupport⟩ :=
      uniqueSeparatorFourEqualEval_transportExactCut
        leftWord rightWord equalEval wordCut
    rw [rightRendered] at targetCut
    exact
      ⟨rightPrefix, rightSuffix, targetCut,
        prefixSupport, suffixSupport⟩
  have backward :
      ∀ {rightPrefix rightSuffix separator},
        UniqueSeparatorFourExactCut
            (uniqueSeparatorCanonicalRender right)
            rightPrefix separator rightSuffix →
        ∃ leftPrefix leftSuffix,
          UniqueSeparatorFourExactCut
              (uniqueSeparatorCanonicalRender left)
              leftPrefix separator leftSuffix ∧
            (∀ tested, tested ∈ leftPrefix ↔
              tested ∈ rightPrefix) ∧
            (∀ tested, tested ∈ leftSuffix ↔
              tested ∈ rightSuffix) := by
    intro rightPrefix rightSuffix separator cut
    have wordCut :
        UniqueSeparatorFourExactCut
          rightWord.toList rightPrefix separator rightSuffix := by
      rwa [rightRendered]
    obtain
      ⟨leftPrefix, leftSuffix, targetCut,
        prefixSupport, suffixSupport⟩ :=
      uniqueSeparatorFourEqualEval_transportExactCut
        rightWord leftWord
        (fun valuation => (equalEval valuation).symm) wordCut
    rw [leftRendered] at targetCut
    exact
      ⟨leftPrefix, leftSuffix, targetCut,
        prefixSupport, suffixSupport⟩
  exact ⟨supportEq, forward, backward⟩

/-- Public injectivity theorem used by the final normalizer: two canonical
segment lists rendering nonempty words and defining the same `S4_69` term
function are equal. -/
theorem uniqueSeparatorCanonical_eq_of_equalEval
    {left right : List UniqueSeparatorCanonicalSegment}
    (leftCanonical : UniqueSeparatorCanonical left)
    (rightCanonical : UniqueSeparatorCanonical right)
    (leftWord rightWord : Word Nat)
    (leftRendered :
      leftWord.toList = uniqueSeparatorCanonicalRender left)
    (rightRendered :
      rightWord.toList = uniqueSeparatorCanonicalRender right)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        uniqueSeparatorFour.semigroup.eval valuation leftWord =
          uniqueSeparatorFour.semigroup.eval valuation rightWord) :
    left = right :=
  uniqueSeparatorCanonical_eq_of_sameSignature
    leftCanonical rightCanonical <|
      uniqueSeparatorCanonicalSameSignature_of_equalEval
        leftWord rightWord leftRendered rightRendered equalEval

theorem uniqueSeparatorCanonical_render_eq_of_equalEval
    {left right : List UniqueSeparatorCanonicalSegment}
    (leftCanonical : UniqueSeparatorCanonical left)
    (rightCanonical : UniqueSeparatorCanonical right)
    (leftWord rightWord : Word Nat)
    (leftRendered :
      leftWord.toList = uniqueSeparatorCanonicalRender left)
    (rightRendered :
      rightWord.toList = uniqueSeparatorCanonicalRender right)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        uniqueSeparatorFour.semigroup.eval valuation leftWord =
          uniqueSeparatorFour.semigroup.eval valuation rightWord) :
    uniqueSeparatorCanonicalRender left =
      uniqueSeparatorCanonicalRender right := by
  rw [uniqueSeparatorCanonical_eq_of_equalEval
    leftCanonical rightCanonical leftWord rightWord
    leftRendered rightRendered equalEval]

/-- Head/tail form of the semantic bridge for callers that have proved their
canonical renders nonempty by displaying the first letter. -/
theorem uniqueSeparatorCanonicalSameSignature_of_consEqualEval
    {left right : List UniqueSeparatorCanonicalSegment}
    {leftHead rightHead : Nat} {leftTail rightTail : List Nat}
    (leftRendered :
      uniqueSeparatorCanonicalRender left = leftHead :: leftTail)
    (rightRendered :
      uniqueSeparatorCanonicalRender right = rightHead :: rightTail)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        uniqueSeparatorFour.semigroup.eval valuation
            (uniqueSeparatorWordOfCons leftHead leftTail) =
          uniqueSeparatorFour.semigroup.eval valuation
            (uniqueSeparatorWordOfCons rightHead rightTail)) :
    UniqueSeparatorCanonicalSameSignature left right := by
  apply uniqueSeparatorCanonicalSameSignature_of_equalEval
    (uniqueSeparatorWordOfCons leftHead leftTail)
    (uniqueSeparatorWordOfCons rightHead rightTail)
  · simpa [uniqueSeparatorWordOfCons] using leftRendered.symm
  · simpa [uniqueSeparatorWordOfCons] using rightRendered.symm
  · exact equalEval

/-- Explicit nonempty-render form of canonical injectivity. -/
theorem uniqueSeparatorCanonical_eq_of_consEqualEval
    {left right : List UniqueSeparatorCanonicalSegment}
    (leftCanonical : UniqueSeparatorCanonical left)
    (rightCanonical : UniqueSeparatorCanonical right)
    {leftHead rightHead : Nat} {leftTail rightTail : List Nat}
    (leftRendered :
      uniqueSeparatorCanonicalRender left = leftHead :: leftTail)
    (rightRendered :
      uniqueSeparatorCanonicalRender right = rightHead :: rightTail)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        uniqueSeparatorFour.semigroup.eval valuation
            (uniqueSeparatorWordOfCons leftHead leftTail) =
          uniqueSeparatorFour.semigroup.eval valuation
            (uniqueSeparatorWordOfCons rightHead rightTail)) :
    left = right :=
  uniqueSeparatorCanonical_eq_of_sameSignature
    leftCanonical rightCanonical <|
      uniqueSeparatorCanonicalSameSignature_of_consEqualEval
        leftRendered rightRendered equalEval

end SemigroupBasis.Examples
