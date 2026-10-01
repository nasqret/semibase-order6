import SemigroupBasis.Examples.UniqueSeparatorFourCanonical
import SemigroupBasis.Examples.UniqueSeparatorFourSaturation
import SemigroupBasis.Examples.UniqueSeparatorFourSortDerives

namespace SemigroupBasis.Examples

/-- Collapse adjacent pairs in a sorted quadratic occurrence list. The
fallback clauses make the operation total; the normalization proof shows
that they are unreachable on the concrete saturated pipeline. -/
def uniqueSeparatorCollapseQuadratic : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
      if x = y then
        x :: uniqueSeparatorCollapseQuadratic rest
      else
        x :: y :: rest

theorem uniqueSeparatorCollapseQuadratic_sublist :
    ∀ letters,
      (uniqueSeparatorCollapseQuadratic letters).Sublist letters
  | [] => List.Sublist.slnil
  | [x] => List.Sublist.cons₂ x List.Sublist.slnil
  | x :: y :: rest => by
      rw [uniqueSeparatorCollapseQuadratic]
      split
      · exact List.Sublist.cons₂ x
          (List.Sublist.cons y
            (uniqueSeparatorCollapseQuadratic_sublist rest))
      · exact List.Sublist.refl (x :: y :: rest)

/-- A sorted list in which every occurring label has multiplicity two is
exactly a concatenation of adjacent equal pairs. -/
theorem uniqueSeparatorCollapseQuadratic_spec :
    ∀ letters,
      letters.Pairwise (· ≤ ·) →
      (∀ label, label ∈ letters → letters.count label = 2) →
      uniqueSeparatorCanonicalRenderDoubles
          (uniqueSeparatorCollapseQuadratic letters) = letters ∧
        (uniqueSeparatorCollapseQuadratic letters).Nodup ∧
        (uniqueSeparatorCollapseQuadratic letters).Pairwise (· ≤ ·)
  | [] => by
      intro _ _
      simp [uniqueSeparatorCollapseQuadratic]
  | [x] => by
      intro _ paired
      have impossible := paired x (by simp)
      simp at impossible
  | x :: y :: rest => by
      intro sorted paired
      have xCount :
          (x :: y :: rest).count x = 2 :=
        paired x (by simp)
      have xInTail : x ∈ y :: rest := by
        apply List.count_pos_iff.mp
        simp only [List.count_cons_self] at xCount
        omega
      have headsEqual : x = y := by
        rcases List.mem_cons.mp xInTail with equal | xInRest
        · exact equal
        · have xLeY :
              x ≤ y :=
            List.rel_of_pairwise_cons sorted (by simp)
          have yLeX :
              y ≤ x :=
            List.rel_of_pairwise_cons sorted.tail xInRest
          omega
      subst y
      have xNotRest : x ∉ rest := by
        intro xInRest
        have positive : 1 ≤ rest.count x :=
          List.one_le_count_iff.mpr xInRest
        simp only [List.count_cons_self] at xCount
        omega
      have restPaired :
          ∀ label, label ∈ rest → rest.count label = 2 := by
        intro label labelInRest
        have totalCount :=
          paired label (by simp [labelInRest])
        have different : label ≠ x := by
          intro equal
          subst label
          exact xNotRest labelInRest
        simpa [different, Ne.symm different] using totalCount
      have restSpec :=
        uniqueSeparatorCollapseQuadratic_spec
          rest sorted.tail.tail restPaired
      have xNotCollapsed :
          x ∉ uniqueSeparatorCollapseQuadratic rest := by
        intro member
        exact xNotRest
          (List.Sublist.mem member
            (uniqueSeparatorCollapseQuadratic_sublist rest))
      have headLe :
          ∀ label,
            label ∈ uniqueSeparatorCollapseQuadratic rest →
              x ≤ label := by
        intro label member
        have labelInRest :=
          List.Sublist.mem member
            (uniqueSeparatorCollapseQuadratic_sublist rest)
        exact
          List.rel_of_pairwise_cons sorted
            (by simp [labelInRest])
      simp only [uniqueSeparatorCollapseQuadratic]
      refine ⟨by simp [restSpec.1], ?_, ?_⟩
      · exact List.nodup_cons.mpr ⟨xNotCollapsed, restSpec.2.1⟩
      · exact List.pairwise_cons.mpr ⟨headLe, restSpec.2.2⟩

/-- Convert one raw square segment by retaining one representative of each
adjacent quadratic pair. -/
def uniqueSeparatorCanonicalizeSegment
    (segment : UniqueSeparatorSquareSegment) :
    UniqueSeparatorCanonicalSegment :=
  ⟨uniqueSeparatorCollapseQuadratic segment.quadratic,
    segment.separator⟩

/-- Empty separator-free raw segments render nothing and are discarded.
All other raw segments are converted in place. -/
def uniqueSeparatorCanonicalizeSegments :
    List UniqueSeparatorSquareSegment →
      List UniqueSeparatorCanonicalSegment
  | [] => []
  | segment :: rest =>
      if segment.quadratic = [] ∧ segment.separator = none then
        uniqueSeparatorCanonicalizeSegments rest
      else
        uniqueSeparatorCanonicalizeSegment segment ::
          uniqueSeparatorCanonicalizeSegments rest

/-- Shape invariant of the raw splitter: every nonterminal segment carries
a separator, while the final segment carries none. -/
def UniqueSeparatorRawShape :
    List UniqueSeparatorSquareSegment → Prop
  | [] => False
  | [segment] => segment.separator = none
  | segment :: next :: rest =>
      segment.separator.isSome ∧
        UniqueSeparatorRawShape (next :: rest)

private theorem uniqueSeparatorRawShape_prependQuadratic
    (x : Nat) :
    ∀ segments,
      UniqueSeparatorRawShape segments →
      UniqueSeparatorRawShape
        (match segments with
        | [] => [⟨[x], none⟩]
        | segment :: rest =>
            ⟨x :: segment.quadratic, segment.separator⟩ :: rest)
  | [], impossible => False.elim impossible
  | [segment], shape => by
      simpa [UniqueSeparatorRawShape] using shape
  | segment :: next :: rest, shape => by
      simpa [UniqueSeparatorRawShape] using shape

theorem uniqueSeparatorSplitLinearAux_rawShape
    (whole : List Nat) :
    ∀ letters,
      UniqueSeparatorRawShape
        (uniqueSeparatorSplitLinearAux whole letters)
  | [] => by
      simp [uniqueSeparatorSplitLinearAux, UniqueSeparatorRawShape]
  | x :: rest => by
      rw [uniqueSeparatorSplitLinearAux]
      split
      · have tailShape :=
          uniqueSeparatorSplitLinearAux_rawShape whole rest
        cases tail :
            uniqueSeparatorSplitLinearAux whole rest with
        | nil =>
            rw [tail] at tailShape
            exact False.elim tailShape
        | cons segment segments =>
            rw [tail] at tailShape
            cases segments with
            | nil =>
                exact ⟨by simp, tailShape⟩
            | cons next more =>
                exact ⟨by simp, tailShape⟩
      · have tailShape :=
          uniqueSeparatorSplitLinearAux_rawShape whole rest
        generalize tail :
            uniqueSeparatorSplitLinearAux whole rest = segments
          at tailShape ⊢
        cases segments with
        | nil =>
            simp [UniqueSeparatorRawShape] at tailShape
        | cons segment segments =>
            cases segments with
            | nil =>
                change
                  UniqueSeparatorRawShape
                    [⟨x :: segment.quadratic,
                      segment.separator⟩]
                exact
                  uniqueSeparatorRawShape_prependQuadratic
                    x [segment] tailShape
            | cons next more =>
                change
                  UniqueSeparatorRawShape
                    (⟨x :: segment.quadratic,
                        segment.separator⟩ ::
                      next :: more)
                exact
                  uniqueSeparatorRawShape_prependQuadratic
                    x (segment :: next :: more) tailShape

theorem uniqueSeparatorSplitLinear_rawShape
    (letters : List Nat) :
    UniqueSeparatorRawShape (uniqueSeparatorSplitLinear letters) :=
  uniqueSeparatorSplitLinearAux_rawShape letters letters

theorem UniqueSeparatorRawShape.tail
    {segment : UniqueSeparatorSquareSegment}
    {rest : List UniqueSeparatorSquareSegment}
    (shape : UniqueSeparatorRawShape (segment :: rest)) :
    rest = [] ∨ UniqueSeparatorRawShape rest := by
  cases rest with
  | nil => exact Or.inl rfl
  | cons next more =>
      exact Or.inr shape.2

theorem UniqueSeparatorRawShape.head_none_rest
    {segment : UniqueSeparatorSquareSegment}
    {rest : List UniqueSeparatorSquareSegment}
    (shape : UniqueSeparatorRawShape (segment :: rest))
    (separatorNone : segment.separator = none) :
    rest = [] := by
  cases rest with
  | nil => rfl
  | cons next more =>
      have separatorSome := shape.1
      simp [separatorNone] at separatorSome

theorem UniqueSeparatorRawShape.head_some
    {segment : UniqueSeparatorSquareSegment}
    {next : UniqueSeparatorSquareSegment}
    {rest : List UniqueSeparatorSquareSegment}
    (shape : UniqueSeparatorRawShape (segment :: next :: rest)) :
    ∃ separator, segment.separator = some separator := by
  cases separatorShape : segment.separator with
  | none =>
      have impossible := shape.1
      simp [separatorShape] at impossible
  | some separator =>
      exact ⟨separator, rfl⟩

theorem uniqueSeparatorCanonicalizeSegment_labels_mem_render
    (segment : UniqueSeparatorSquareSegment) (label : Nat) :
    label ∈ (uniqueSeparatorCanonicalizeSegment segment).labels →
      label ∈ segment.render := by
  intro member
  cases segment with
  | mk quadratic separator =>
      cases separator with
      | none =>
          have collapsedMember :
              label ∈ uniqueSeparatorCollapseQuadratic quadratic := by
            simpa [uniqueSeparatorCanonicalizeSegment,
              UniqueSeparatorCanonicalSegment.labels] using member
          have quadraticMember :=
            List.Sublist.mem collapsedMember
              (uniqueSeparatorCollapseQuadratic_sublist quadratic)
          simpa [UniqueSeparatorSquareSegment.render] using
            quadraticMember
      | some separator =>
          have split :
              label ∈ uniqueSeparatorCollapseQuadratic quadratic ∨
                label = separator := by
            simpa [uniqueSeparatorCanonicalizeSegment,
              UniqueSeparatorCanonicalSegment.labels] using member
          rcases split with collapsedMember | rfl
          · have quadraticMember :=
              List.Sublist.mem collapsedMember
                (uniqueSeparatorCollapseQuadratic_sublist quadratic)
            simp [UniqueSeparatorSquareSegment.render, quadraticMember]
          · simp [UniqueSeparatorSquareSegment.render]

theorem uniqueSeparatorCanonicalizeSegments_labels_mem_render :
    ∀ (segments : List UniqueSeparatorSquareSegment) (label : Nat),
      label ∈
          uniqueSeparatorCanonicalLabels
            (uniqueSeparatorCanonicalizeSegments segments) →
        label ∈ uniqueSeparatorRenderSquareSegments segments
  | [], label => by
      simp [uniqueSeparatorCanonicalizeSegments,
        uniqueSeparatorCanonicalLabels,
        uniqueSeparatorRenderSquareSegments]
  | segment :: rest, label => by
      intro member
      by_cases empty :
          segment.quadratic = [] ∧ segment.separator = none
      · rw [uniqueSeparatorCanonicalizeSegments, if_pos empty] at member
        have tailMember :=
          uniqueSeparatorCanonicalizeSegments_labels_mem_render
            rest label member
        rw [show
          uniqueSeparatorRenderSquareSegments (segment :: rest) =
            segment.render ++
              uniqueSeparatorRenderSquareSegments rest by rfl]
        exact List.mem_append_right segment.render tailMember
      · rw [uniqueSeparatorCanonicalizeSegments, if_neg empty] at member
        have split :
            label ∈
                (uniqueSeparatorCanonicalizeSegment segment).labels ∨
              label ∈
                uniqueSeparatorCanonicalLabels
                  (uniqueSeparatorCanonicalizeSegments rest) := by
          simpa [uniqueSeparatorCanonicalLabels] using member
        rcases split with headMember | tailMember
        · have renderedMember :=
            uniqueSeparatorCanonicalizeSegment_labels_mem_render
              segment label headMember
          simp [uniqueSeparatorRenderSquareSegments, renderedMember]
        · have renderedMember :=
            uniqueSeparatorCanonicalizeSegments_labels_mem_render
              rest label tailMember
          rw [show
            uniqueSeparatorRenderSquareSegments (segment :: rest) =
              segment.render ++
                uniqueSeparatorRenderSquareSegments rest by rfl]
          exact List.mem_append_right segment.render renderedMember

theorem uniqueSeparatorCanonicalizeSegment_render_eq
    (segment : UniqueSeparatorSquareSegment)
    (reconstruct :
      uniqueSeparatorCanonicalRenderDoubles
          (uniqueSeparatorCollapseQuadratic segment.quadratic) =
        segment.quadratic) :
    (uniqueSeparatorCanonicalizeSegment segment).render =
      segment.render := by
  cases segment
  simp [uniqueSeparatorCanonicalizeSegment,
    UniqueSeparatorCanonicalSegment.render,
    UniqueSeparatorSquareSegment.render, reconstruct]

theorem uniqueSeparatorCanonicalizeSegments_render_eq
    (segments : List UniqueSeparatorSquareSegment)
    (reconstruct :
      ∀ segment, segment ∈ segments →
        uniqueSeparatorCanonicalRenderDoubles
            (uniqueSeparatorCollapseQuadratic segment.quadratic) =
          segment.quadratic) :
    uniqueSeparatorCanonicalRender
        (uniqueSeparatorCanonicalizeSegments segments) =
      uniqueSeparatorRenderSquareSegments segments := by
  induction segments with
  | nil =>
      simp [uniqueSeparatorCanonicalizeSegments,
        uniqueSeparatorCanonicalRender,
        uniqueSeparatorRenderSquareSegments]
  | cons segment rest ih =>
      have headReconstruct :=
        reconstruct segment (List.Mem.head rest)
      have tailReconstruct :
          ∀ candidate, candidate ∈ rest →
            uniqueSeparatorCanonicalRenderDoubles
                (uniqueSeparatorCollapseQuadratic
                  candidate.quadratic) =
              candidate.quadratic :=
        fun candidate member =>
          reconstruct candidate (List.Mem.tail segment member)
      have tailEq := ih tailReconstruct
      have tailEq' :
          List.flatMap UniqueSeparatorCanonicalSegment.render
              (uniqueSeparatorCanonicalizeSegments rest) =
            List.flatMap UniqueSeparatorSquareSegment.render rest := by
        simpa [uniqueSeparatorCanonicalRender,
          uniqueSeparatorRenderSquareSegments] using tailEq
      by_cases empty :
          segment.quadratic = [] ∧ segment.separator = none
      · rcases empty with ⟨quadraticEmpty, separatorNone⟩
        simpa [uniqueSeparatorCanonicalizeSegments, quadraticEmpty,
          separatorNone, uniqueSeparatorCanonicalRender,
          uniqueSeparatorRenderSquareSegments,
          UniqueSeparatorSquareSegment.render] using tailEq'
      · rw [uniqueSeparatorCanonicalizeSegments, if_neg empty]
        simp only [uniqueSeparatorCanonicalRender, List.flatMap_cons,
          uniqueSeparatorRenderSquareSegments, List.flatMap_cons]
        rw [uniqueSeparatorCanonicalizeSegment_render_eq
          segment headReconstruct]
        exact congrArg (segment.render ++ ·) tailEq'

private theorem uniqueSeparatorRaw_head_render_disjoint
    {segment : UniqueSeparatorSquareSegment}
    {rest : List UniqueSeparatorSquareSegment}
    (shape : UniqueSeparatorRawShape (segment :: rest))
    (rawSaturated :
      UniqueSeparatorRawSaturated (segment :: rest))
    (separatorCount :
      ∀ separator,
        segment.separator = some separator →
          (uniqueSeparatorRenderSquareSegments
            (segment :: rest)).count separator = 1) :
    UniqueSeparatorFourSupportsDisjoint
      segment.render
      (uniqueSeparatorRenderSquareSegments rest) := by
  intro label headMember
  cases rest with
  | nil =>
      simp [uniqueSeparatorRenderSquareSegments]
  | cons next more =>
      obtain ⟨separator, separatorShape⟩ :=
        shape.head_some
      have quadraticDisjoint :=
        rawSaturated [] segment (next :: more) separator
          (by rfl) separatorShape
      intro tailMember
      have headSplit :
          label ∈ segment.quadratic ∨
            label ∈ segment.separator.toList := by
        simpa [UniqueSeparatorSquareSegment.render] using headMember
      rcases headSplit with quadraticMember | separatorMember
      · exact
          quadraticDisjoint label
            (by simpa [uniqueSeparatorRenderSquareSegments] using
              quadraticMember)
            tailMember
      · rw [separatorShape] at separatorMember
        have labelEq : label = separator := by
          simpa using separatorMember
        subst label
        have countOne :=
          separatorCount separator separatorShape
        have headPositive :
            1 ≤ segment.render.count separator :=
          List.one_le_count_iff.mpr headMember
        have tailPositive :
            1 ≤
              (uniqueSeparatorRenderSquareSegments
                (next :: more)).count separator :=
          List.one_le_count_iff.mpr tailMember
        rw [show
          uniqueSeparatorRenderSquareSegments
              (segment :: next :: more) =
            segment.render ++
              uniqueSeparatorRenderSquareSegments
                (next :: more) by rfl,
          List.count_append] at countOne
        omega

private theorem uniqueSeparatorSortedHead_collapseSpec
    {segment : UniqueSeparatorSquareSegment}
    {rest : List UniqueSeparatorSquareSegment}
    (headDisjoint :
      UniqueSeparatorFourSupportsDisjoint
        segment.render
        (uniqueSeparatorRenderSquareSegments rest))
    (quadraticCount :
      ∀ label, label ∈ segment.quadratic →
        (uniqueSeparatorRenderSquareSegments
          (segment :: rest)).count label = 2)
    (separatorCount :
      ∀ separator,
        segment.separator = some separator →
          (uniqueSeparatorRenderSquareSegments
            (segment :: rest)).count separator = 1) :
    let sorted := uniqueSeparatorSortSquareSegment segment
    uniqueSeparatorCanonicalRenderDoubles
        (uniqueSeparatorCollapseQuadratic sorted.quadratic) =
      sorted.quadratic ∧
      (uniqueSeparatorCollapseQuadratic
        sorted.quadratic).Nodup ∧
      (uniqueSeparatorCollapseQuadratic
        sorted.quadratic).Pairwise (· ≤ ·) := by
  let sorted := uniqueSeparatorSortSquareSegment segment
  have sortedOrder : sorted.quadratic.Pairwise (· ≤ ·) :=
    uniqueSeparatorSortSquareSegment_sorted segment
  have sortedPaired :
      ∀ label, label ∈ sorted.quadratic →
        sorted.quadratic.count label = 2 := by
    intro label sortedMember
    have sourceMember : label ∈ segment.quadratic :=
      (uniqueSeparatorSortQuadratic_perm
        segment.quadratic).mem_iff.mp sortedMember
    have totalCount := quadraticCount label sourceMember
    have headMember : label ∈ segment.render := by
      simp [UniqueSeparatorSquareSegment.render, sourceMember]
    have notTail :
        label ∉ uniqueSeparatorRenderSquareSegments rest :=
      headDisjoint label headMember
    have tailCountZero :
        (uniqueSeparatorRenderSquareSegments rest).count label = 0 :=
      List.count_eq_zero.mpr notTail
    have notSeparator :
        label ∉ segment.separator.toList := by
      cases separatorShape : segment.separator with
      | none => simp
      | some separator =>
          intro member
          have labelEq : label = separator := by
            simpa [separatorShape] using member
          subst label
          have countOne :=
            separatorCount separator separatorShape
          omega
    have separatorCountZero :
        segment.separator.toList.count label = 0 :=
      List.count_eq_zero.mpr notSeparator
    have sourceBlockCount :
        segment.quadratic.count label = 2 := by
      rw [show
        uniqueSeparatorRenderSquareSegments (segment :: rest) =
          segment.render ++
            uniqueSeparatorRenderSquareSegments rest by rfl,
        List.count_append,
        UniqueSeparatorSquareSegment.render,
        List.count_append, tailCountZero,
        separatorCountZero] at totalCount
      omega
    exact
      (uniqueSeparatorSortQuadratic_perm
        segment.quadratic).count label |>.trans sourceBlockCount
  exact
    uniqueSeparatorCollapseQuadratic_spec
      sorted.quadratic sortedOrder sortedPaired

private theorem uniqueSeparatorCanonical_cons
    {segment : UniqueSeparatorCanonicalSegment}
    {rest : List UniqueSeparatorCanonicalSegment}
    (segmentLabelsNodup : segment.labels.Nodup)
    (restCanonical : UniqueSeparatorCanonical rest)
    (labelsDisjoint :
      ∀ label, label ∈ segment.labels →
        label ∉ uniqueSeparatorCanonicalLabels rest)
    (segmentSorted : segment.quadratic.Pairwise (· ≤ ·))
    (terminal :
      segment.separator = none → rest = [])
    (nonempty :
      segment.quadratic = [] → segment.separator.isSome) :
    UniqueSeparatorCanonical (segment :: rest) := by
  have labelsNodup :
      (segment.labels ++
        uniqueSeparatorCanonicalLabels rest).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨segmentLabelsNodup, restCanonical.1, ?_⟩
    intro left leftMember right rightMember equal
    subst right
    exact labelsDisjoint left leftMember rightMember
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [uniqueSeparatorCanonicalLabels] using labelsNodup
  · intro candidate member
    rcases List.mem_cons.mp member with rfl | tailMember
    · exact segmentSorted
    · exact restCanonical.2.1 candidate tailMember
  · intro before candidate after split separatorNone
    cases before with
    | nil =>
        change segment :: rest = candidate :: after at split
        have parts := List.cons.inj split
        have segmentNone : segment.separator = none := by
          rw [parts.1]
          exact separatorNone
        have restEmpty := terminal segmentNone
        rw [← parts.2]
        exact restEmpty
    | cons first before =>
        change
          segment :: rest =
            first :: (before ++ candidate :: after) at split
        have tailSplit := (List.cons.inj split).2
        exact
          restCanonical.2.2.1 before candidate after
            tailSplit separatorNone
  · intro candidate member quadraticEmpty
    rcases List.mem_cons.mp member with rfl | tailMember
    · exact nonempty quadraticEmpty
    · exact
        restCanonical.2.2.2 candidate tailMember quadraticEmpty

/-- Canonicalize a sorted copy of a raw saturated segment list. The count
hypotheses are stated against the current raw render so that the proof can
recurse after peeling off one support-disjoint segment. -/
theorem uniqueSeparatorCanonicalizeSorted_spec :
    ∀ segments : List UniqueSeparatorSquareSegment,
      UniqueSeparatorRawShape segments →
      UniqueSeparatorRawSaturated segments →
      (∀ segment, segment ∈ segments →
        ∀ label, label ∈ segment.quadratic →
          (uniqueSeparatorRenderSquareSegments segments).count label = 2) →
      (∀ segment, segment ∈ segments →
        ∀ separator, segment.separator = some separator →
          (uniqueSeparatorRenderSquareSegments segments).count
            separator = 1) →
      uniqueSeparatorCanonicalRender
          (uniqueSeparatorCanonicalizeSegments
            (uniqueSeparatorSortSquareSegments segments)) =
        uniqueSeparatorRenderSquareSegments
          (uniqueSeparatorSortSquareSegments segments) ∧
      UniqueSeparatorCanonical
        (uniqueSeparatorCanonicalizeSegments
          (uniqueSeparatorSortSquareSegments segments))
  | [], shape, _, _, _ => False.elim shape
  | segment :: rest, shape, rawSaturated,
      quadraticCount, separatorCount => by
      let sortedSegment := uniqueSeparatorSortSquareSegment segment
      let canonicalSegment :=
        uniqueSeparatorCanonicalizeSegment sortedSegment
      have headQuadraticCount :
          ∀ label, label ∈ segment.quadratic →
            (uniqueSeparatorRenderSquareSegments
              (segment :: rest)).count label = 2 :=
        fun label member =>
          quadraticCount segment (List.Mem.head rest)
            label member
      have headSeparatorCount :
          ∀ separator, segment.separator = some separator →
            (uniqueSeparatorRenderSquareSegments
              (segment :: rest)).count separator = 1 :=
        fun separator separatorShape =>
          separatorCount segment (List.Mem.head rest)
            separator separatorShape
      have headDisjoint :
          UniqueSeparatorFourSupportsDisjoint
            segment.render
            (uniqueSeparatorRenderSquareSegments rest) :=
        uniqueSeparatorRaw_head_render_disjoint
          shape rawSaturated headSeparatorCount
      have headSpec :
          uniqueSeparatorCanonicalRenderDoubles
              (uniqueSeparatorCollapseQuadratic
                sortedSegment.quadratic) =
            sortedSegment.quadratic ∧
          (uniqueSeparatorCollapseQuadratic
            sortedSegment.quadratic).Nodup ∧
          (uniqueSeparatorCollapseQuadratic
            sortedSegment.quadratic).Pairwise (· ≤ ·) := by
        simpa [sortedSegment] using
          uniqueSeparatorSortedHead_collapseSpec
            headDisjoint headQuadraticCount headSeparatorCount
      cases rest with
      | nil =>
          have separatorNone : segment.separator = none := shape
          have sortedSeparatorNone :
              sortedSegment.separator = none := by
            simpa [sortedSegment] using separatorNone
          have renderEq :
              uniqueSeparatorCanonicalRender
                  (uniqueSeparatorCanonicalizeSegments
                    [sortedSegment]) =
                uniqueSeparatorRenderSquareSegments
                  [sortedSegment] := by
            apply uniqueSeparatorCanonicalizeSegments_render_eq
            intro candidate member
            have candidateEq : candidate = sortedSegment := by
              simpa using member
            subst candidate
            exact headSpec.1
          have canonical :
              UniqueSeparatorCanonical
                (uniqueSeparatorCanonicalizeSegments
                  [sortedSegment]) := by
            by_cases empty :
                sortedSegment.quadratic = [] ∧
                  sortedSegment.separator = none
            · simp [uniqueSeparatorCanonicalizeSegments, empty,
                UniqueSeparatorCanonical,
                uniqueSeparatorCanonicalLabels]
            · have emptyCanonical :
                  UniqueSeparatorCanonical [] := by
                simp [UniqueSeparatorCanonical,
                  uniqueSeparatorCanonicalLabels]
              have labelsNodup :
                  canonicalSegment.labels.Nodup := by
                simpa [canonicalSegment,
                  uniqueSeparatorCanonicalizeSegment,
                  UniqueSeparatorCanonicalSegment.labels,
                  sortedSeparatorNone] using headSpec.2.1
              have labelsDisjoint :
                  ∀ label, label ∈ canonicalSegment.labels →
                    label ∉ uniqueSeparatorCanonicalLabels [] := by
                simp [uniqueSeparatorCanonicalLabels]
              have terminal :
                  canonicalSegment.separator = none → ([] :
                    List UniqueSeparatorCanonicalSegment) = [] :=
                fun _ => rfl
              have nonempty :
                  canonicalSegment.quadratic = [] →
                    canonicalSegment.separator.isSome := by
                intro quadraticEmpty
                exfalso
                apply empty
                constructor
                · rw [← headSpec.1]
                  have collapsedEmpty :
                      uniqueSeparatorCollapseQuadratic
                          sortedSegment.quadratic = [] := by
                    simpa [canonicalSegment,
                      uniqueSeparatorCanonicalizeSegment] using
                        quadraticEmpty
                  rw [collapsedEmpty]
                  rfl
                · simpa [canonicalSegment,
                    uniqueSeparatorCanonicalizeSegment] using
                    sortedSeparatorNone
              have singletonCanonical :=
                uniqueSeparatorCanonical_cons
                  labelsNodup emptyCanonical labelsDisjoint
                  headSpec.2.2 terminal nonempty
              simpa [uniqueSeparatorCanonicalizeSegments, empty,
                canonicalSegment] using singletonCanonical
          simpa [uniqueSeparatorSortSquareSegments, sortedSegment]
            using And.intro renderEq canonical
      | cons next more =>
          have tailShape :
              UniqueSeparatorRawShape (next :: more) :=
            shape.2
          obtain ⟨separator, separatorShape⟩ :=
            shape.head_some
          have sortedSeparatorShape :
              sortedSegment.separator = some separator := by
            simpa [sortedSegment] using separatorShape
          have tailRawSaturated :
              UniqueSeparatorRawSaturated (next :: more) := by
            intro before candidate after tested
              segmentsShape candidateSeparator
            intro label leftMember rightMember
            apply
              rawSaturated (segment :: before) candidate after
                tested
            · simp [segmentsShape]
            · exact candidateSeparator
            · have enlarged :
                  label ∈
                    segment.render ++
                      (uniqueSeparatorRenderSquareSegments before ++
                        candidate.quadratic) :=
                List.mem_append_right segment.render leftMember
              simpa [uniqueSeparatorRenderSquareSegments,
                List.append_assoc] using enlarged
            · exact rightMember
          have tailCountEq :
              ∀ label,
                label ∈
                    uniqueSeparatorRenderSquareSegments
                      (next :: more) →
                  (uniqueSeparatorRenderSquareSegments
                    (next :: more)).count label =
                    (uniqueSeparatorRenderSquareSegments
                      (segment :: next :: more)).count label := by
            intro label tailMember
            have notHead : label ∉ segment.render := by
              intro headMember
              exact headDisjoint label headMember tailMember
            rw [show
              uniqueSeparatorRenderSquareSegments
                  (segment :: next :: more) =
                segment.render ++
                  uniqueSeparatorRenderSquareSegments
                    (next :: more) by rfl,
              List.count_append,
              List.count_eq_zero.mpr notHead,
              Nat.zero_add]
          have tailQuadraticCount :
              ∀ candidate, candidate ∈ next :: more →
                ∀ label, label ∈ candidate.quadratic →
                  (uniqueSeparatorRenderSquareSegments
                    (next :: more)).count label = 2 := by
            intro candidate candidateMember label labelMember
            have tailMember :
                label ∈
                  uniqueSeparatorRenderSquareSegments
                    (next :: more) := by
              simp only [uniqueSeparatorRenderSquareSegments,
                List.mem_flatMap]
              exact
                ⟨candidate, candidateMember,
                  by simp [UniqueSeparatorSquareSegment.render,
                    labelMember]⟩
            exact
              (tailCountEq label tailMember).trans
                (quadraticCount candidate
                  (List.Mem.tail segment candidateMember)
                  label labelMember)
          have tailSeparatorCount :
              ∀ candidate, candidate ∈ next :: more →
                ∀ tested, candidate.separator = some tested →
                  (uniqueSeparatorRenderSquareSegments
                    (next :: more)).count tested = 1 := by
            intro candidate candidateMember tested testedShape
            have tailMember :
                tested ∈
                  uniqueSeparatorRenderSquareSegments
                    (next :: more) := by
              simp only [uniqueSeparatorRenderSquareSegments,
                List.mem_flatMap]
              exact
                ⟨candidate, candidateMember,
                  by simp [UniqueSeparatorSquareSegment.render,
                    testedShape]⟩
            exact
              (tailCountEq tested tailMember).trans
                (separatorCount candidate
                  (List.Mem.tail segment candidateMember)
                  tested testedShape)
          have tailResult :=
            uniqueSeparatorCanonicalizeSorted_spec
              (next :: more) tailShape tailRawSaturated
              tailQuadraticCount tailSeparatorCount
          have keep :
              ¬(sortedSegment.quadratic = [] ∧
                sortedSegment.separator = none) := by
            rintro ⟨_, impossible⟩
            rw [sortedSeparatorShape] at impossible
            contradiction
          have renderEq :
              uniqueSeparatorCanonicalRender
                  (uniqueSeparatorCanonicalizeSegments
                    (uniqueSeparatorSortSquareSegments
                      (segment :: next :: more))) =
                uniqueSeparatorRenderSquareSegments
                  (uniqueSeparatorSortSquareSegments
                    (segment :: next :: more)) := by
            rw [show
              uniqueSeparatorSortSquareSegments
                  (segment :: next :: more) =
                sortedSegment ::
                  uniqueSeparatorSortSquareSegments
                    (next :: more) by rfl,
              uniqueSeparatorCanonicalizeSegments, if_neg keep]
            change
              canonicalSegment.render ++
                  uniqueSeparatorCanonicalRender
                    (uniqueSeparatorCanonicalizeSegments
                      (uniqueSeparatorSortSquareSegments
                        (next :: more))) =
                sortedSegment.render ++
                  uniqueSeparatorRenderSquareSegments
                    (uniqueSeparatorSortSquareSegments
                      (next :: more))
            rw [uniqueSeparatorCanonicalizeSegment_render_eq
              sortedSegment headSpec.1, tailResult.1]
          have separatorNotQuadratic :
              separator ∉ canonicalSegment.quadratic := by
            intro collapsedMember
            have sortedMember :
                separator ∈ sortedSegment.quadratic :=
              List.Sublist.mem collapsedMember
                (uniqueSeparatorCollapseQuadratic_sublist
                  sortedSegment.quadratic)
            have sourceMember :
                separator ∈ segment.quadratic :=
              (uniqueSeparatorSortQuadratic_perm
                segment.quadratic).mem_iff.mp <| by
                  simpa [sortedSegment] using sortedMember
            have countTwo :=
              headQuadraticCount separator sourceMember
            have countOne :=
              headSeparatorCount separator separatorShape
            omega
          have segmentLabelsNodup :
              canonicalSegment.labels.Nodup := by
            simpa [canonicalSegment,
              uniqueSeparatorCanonicalizeSegment,
              UniqueSeparatorCanonicalSegment.labels,
              sortedSeparatorShape] using
                List.nodup_append.mpr
                  ⟨headSpec.2.1, by simp, by
                    intro left leftMember right rightMember equal
                    have rightEq : right = separator := by
                      simpa using rightMember
                    subst right
                    subst left
                    exact separatorNotQuadratic leftMember⟩
          have labelsDisjoint :
              ∀ label, label ∈ canonicalSegment.labels →
                label ∉
                  uniqueSeparatorCanonicalLabels
                    (uniqueSeparatorCanonicalizeSegments
                      (uniqueSeparatorSortSquareSegments
                        (next :: more))) := by
            intro label headLabel tailLabel
            have sortedHeadMember :
                label ∈ sortedSegment.render :=
              uniqueSeparatorCanonicalizeSegment_labels_mem_render
                sortedSegment label headLabel
            have sourceHeadMember : label ∈ segment.render :=
              (uniqueSeparatorSortSquareSegment_render_perm
                segment).mem_iff.mp <| by
                  simpa [sortedSegment] using sortedHeadMember
            have sortedTailMember :
                label ∈
                  uniqueSeparatorRenderSquareSegments
                    (uniqueSeparatorSortSquareSegments
                      (next :: more)) :=
              uniqueSeparatorCanonicalizeSegments_labels_mem_render
                (uniqueSeparatorSortSquareSegments
                  (next :: more)) label tailLabel
            have sourceTailMember :
                label ∈
                  uniqueSeparatorRenderSquareSegments
                    (next :: more) :=
              (uniqueSeparatorSortSquareSegments_render_perm
                (next :: more)).mem_iff.mp sortedTailMember
            exact
              headDisjoint label sourceHeadMember sourceTailMember
          have terminal :
              canonicalSegment.separator = none →
                uniqueSeparatorCanonicalizeSegments
                    (uniqueSeparatorSortSquareSegments
                      (next :: more)) = [] := by
            intro impossible
            have sortedNone :
                sortedSegment.separator = none := by
              simpa [canonicalSegment,
                uniqueSeparatorCanonicalizeSegment] using
                  impossible
            rw [sortedSeparatorShape] at sortedNone
            contradiction
          have nonempty :
              canonicalSegment.quadratic = [] →
                canonicalSegment.separator.isSome := by
            intro _
            simp [canonicalSegment,
              uniqueSeparatorCanonicalizeSegment,
              sortedSeparatorShape]
          have canonical :=
            uniqueSeparatorCanonical_cons
              segmentLabelsNodup tailResult.2 labelsDisjoint
              headSpec.2.2 terminal nonempty
          have canonicalEq :
              UniqueSeparatorCanonical
                (uniqueSeparatorCanonicalizeSegments
                  (uniqueSeparatorSortSquareSegments
                    (segment :: next :: more))) := by
            rw [show
              uniqueSeparatorSortSquareSegments
                  (segment :: next :: more) =
                sortedSegment ::
                  uniqueSeparatorSortSquareSegments
                    (next :: more) by rfl,
              uniqueSeparatorCanonicalizeSegments, if_neg keep]
            simpa [canonicalSegment] using canonical
          exact ⟨renderEq, canonicalEq⟩

/-- The deterministic sorted raw normal form of a word. -/
def uniqueSeparatorSortedRawSegments (letters : List Nat) :
    List UniqueSeparatorSquareSegment :=
  uniqueSeparatorSortSquareSegments
    (uniqueSeparatorSplitLinear
      (uniqueSeparatorSaturate
        (uniqueSeparatorEndpointCap letters)))

/-- The canonical adjacent-square segments obtained from the deterministic
raw normalization pipeline. -/
def uniqueSeparatorCanonicalSegments (letters : List Nat) :
    List UniqueSeparatorCanonicalSegment :=
  uniqueSeparatorCanonicalizeSegments
    (uniqueSeparatorSortedRawSegments letters)

/-- The sorted raw pipeline renders exactly as adjacent canonical squares,
and the converted segment list satisfies the full canonical predicate. -/
theorem uniqueSeparatorEndpointCapSaturateSort_canonicalization
    (letters : List Nat) :
    uniqueSeparatorRenderSquareSegments
        (uniqueSeparatorSortedRawSegments letters) =
      uniqueSeparatorCanonicalRender
        (uniqueSeparatorCanonicalSegments letters) ∧
    UniqueSeparatorCanonical
      (uniqueSeparatorCanonicalSegments letters) := by
  let capped := uniqueSeparatorEndpointCap letters
  let saturated := uniqueSeparatorSaturate capped
  let raw := uniqueSeparatorSplitLinear saturated
  have limited : UniqueSeparatorTwoLimited saturated := by
    exact
      uniqueSeparatorSaturate_twoLimited capped
        (uniqueSeparatorEndpointCap_twoLimited letters)
  have shape : UniqueSeparatorRawShape raw := by
    simpa [raw] using
      uniqueSeparatorSplitLinear_rawShape saturated
  have rawSaturated : UniqueSeparatorRawSaturated raw := by
    simpa [raw, saturated, capped] using
      uniqueSeparatorSplitLinear_saturate_rawSaturated capped
  have quadraticCount :
      ∀ segment, segment ∈ raw →
        ∀ label, label ∈ segment.quadratic →
          (uniqueSeparatorRenderSquareSegments raw).count label = 2 := by
    intro segment segmentMember label labelMember
    rw [show
      uniqueSeparatorRenderSquareSegments raw = saturated by
        simpa [raw] using
          uniqueSeparatorRender_splitLinear saturated]
    exact
      uniqueSeparatorSplitLinear_quadratic_count_two
        saturated limited segment segmentMember label labelMember
  have separatorCount :
      ∀ segment, segment ∈ raw →
        ∀ separator, segment.separator = some separator →
          (uniqueSeparatorRenderSquareSegments raw).count separator = 1 := by
    intro segment segmentMember separator separatorShape
    rw [show
      uniqueSeparatorRenderSquareSegments raw = saturated by
        simpa [raw] using
          uniqueSeparatorRender_splitLinear saturated]
    exact
      uniqueSeparatorSplitLinear_separator_count_one
        saturated segment segmentMember separator separatorShape
  have result :=
    uniqueSeparatorCanonicalizeSorted_spec
      raw shape rawSaturated quadraticCount separatorCount
  exact
    ⟨by
      simpa [uniqueSeparatorSortedRawSegments,
        uniqueSeparatorCanonicalSegments, raw, saturated, capped] using
          result.1.symm,
    by
      simpa [uniqueSeparatorSortedRawSegments,
        uniqueSeparatorCanonicalSegments, raw, saturated, capped] using
          result.2⟩

theorem uniqueSeparatorEndpointCapSaturateSort_eq_canonicalRender
    (letters : List Nat) :
    uniqueSeparatorRenderSquareSegments
        (uniqueSeparatorSortedRawSegments letters) =
      uniqueSeparatorCanonicalRender
        (uniqueSeparatorCanonicalSegments letters) :=
  (uniqueSeparatorEndpointCapSaturateSort_canonicalization letters).1

theorem uniqueSeparatorCanonicalSegments_canonical
    (letters : List Nat) :
    UniqueSeparatorCanonical
      (uniqueSeparatorCanonicalSegments letters) :=
  (uniqueSeparatorEndpointCapSaturateSort_canonicalization letters).2

end SemigroupBasis.Examples
