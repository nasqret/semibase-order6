import SemigroupBasis.Examples.AffineShiftThreeInvariant

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- A marker followed by the modulo-three correction block that precedes the
next marker. In the final segment, `padding` is the total-residue tail. -/
structure AffineShiftThreeSegment where
  marker : Nat
  padding : List Nat
deriving Repr, DecidableEq

def affineShiftThreeSegmentMarkers :
    List AffineShiftThreeSegment → List Nat
  | [] => []
  | segment :: rest =>
      segment.marker :: affineShiftThreeSegmentMarkers rest

/-- Marker-first rendering gives
`sigma_1 D_2 sigma_2 ... D_k sigma_k E`. -/
def affineShiftThreeRenderSegments :
    List AffineShiftThreeSegment → List Nat
  | [] => []
  | segment :: rest =>
      segment.marker ::
        (segment.padding ++ affineShiftThreeRenderSegments rest)

/-- Render a nonempty segment list as a semigroup word. -/
def affineShiftThreeRenderWord
    (segment : AffineShiftThreeSegment)
    (rest : List AffineShiftThreeSegment) : Word Nat :=
  ⟨segment.marker,
    segment.padding ++ affineShiftThreeRenderSegments rest⟩

@[simp]
theorem affineShiftThreeRenderWord_toList
    (segment : AffineShiftThreeSegment)
    (rest : List AffineShiftThreeSegment) :
    (affineShiftThreeRenderWord segment rest).toList =
      affineShiftThreeRenderSegments (segment :: rest) :=
  rfl

theorem affineShiftThreeMarker_mem_render
    {segments : List AffineShiftThreeSegment} {marker : Nat}
    (member : marker ∈ affineShiftThreeSegmentMarkers segments) :
    marker ∈ affineShiftThreeRenderSegments segments := by
  induction segments with
  | nil => simp [affineShiftThreeSegmentMarkers] at member
  | cons segment rest inductionHypothesis =>
      simp only [affineShiftThreeSegmentMarkers, List.mem_cons] at member
      simp only [affineShiftThreeRenderSegments, List.mem_cons,
        List.mem_append]
      rcases member with rfl | member
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (inductionHypothesis member))

/-- Add zero, one, or two copies of `letter` to move one residue to another. -/
def affineShiftThreeCorrectionBlock
    (letter : Nat) (current target : Fin 3) : List Nat :=
  if current = target then []
  else if current + 1 = target then [letter]
  else [letter, letter]

private theorem affineShiftThreeAddTwo_of_ne
    (current target : Fin 3)
    (notZero : current ≠ target)
    (notOne : current + 1 ≠ target) :
    current + 2 = target := by
  decide +revert

theorem affineShiftThreeCorrectionBlock_reaches
    (letter : Nat) (current target : Fin 3) :
    current + affineShiftThreeCountResidue letter
        (affineShiftThreeCorrectionBlock letter current target) = target := by
  by_cases zero : current = target
  · simp [affineShiftThreeCorrectionBlock, zero]
  · by_cases one : current + 1 = target
    · simp [affineShiftThreeCorrectionBlock, zero, one,
        affineShiftThreeCountResidue,
        affineShiftThreeResidueSum]
    · simpa [affineShiftThreeCorrectionBlock, zero, one,
        affineShiftThreeCountResidue,
        affineShiftThreeResidueSum] using
          affineShiftThreeAddTwo_of_ne current target zero one

theorem affineShiftThreeCorrectionBlock_mem
    {letter current target tested}
    (member : tested ∈
      affineShiftThreeCorrectionBlock letter current target) :
    tested = letter := by
  by_cases zero : current = target
  · simp [affineShiftThreeCorrectionBlock, zero] at member
  · by_cases one : current + 1 = target
    · simpa [affineShiftThreeCorrectionBlock, zero, one] using member
    · simpa [affineShiftThreeCorrectionBlock, zero, one] using member

theorem affineShiftThreeCorrectionBlock_count_lt_three
    (letter : Nat) (current target : Fin 3) :
    (affineShiftThreeCorrectionBlock letter current target).count letter < 3 := by
  by_cases zero : current = target
  · simp [affineShiftThreeCorrectionBlock, zero]
  · by_cases one : current + 1 = target
    · simp [affineShiftThreeCorrectionBlock, zero, one]
    · simp [affineShiftThreeCorrectionBlock, zero, one]

theorem affineShiftThreeCorrectionBlock_count_of_ne
    {letter tested : Nat} (different : tested ≠ letter)
    (current target : Fin 3) :
    (affineShiftThreeCorrectionBlock letter current target).count tested = 0 := by
  apply List.count_eq_zero.mpr
  intro member
  exact different (affineShiftThreeCorrectionBlock_mem member)

theorem affineShiftThreeCorrectionBlock_residue_of_ne
    {letter tested : Nat} (different : tested ≠ letter)
    (current target : Fin 3) :
    affineShiftThreeCountResidue tested
        (affineShiftThreeCorrectionBlock letter current target) = 0 := by
  apply affineShiftThreeCountResidue_eq_zero_of_not_mem
  intro member
  exact different (affineShiftThreeCorrectionBlock_mem member)

private theorem affineShiftThreeFinAdd_zero (residue : Fin 3) :
    residue + 0 = residue := by
  decide +revert

private theorem affineShiftThreeFinZero_add (residue : Fin 3) :
    0 + residue = residue := by
  decide +revert

/-- Emit independent correction blocks in the fixed order `available`. -/
def affineShiftThreeResidueBlock
    (available : List Nat)
    (current target : Nat → Fin 3) : List Nat :=
  available.flatMap fun letter =>
    affineShiftThreeCorrectionBlock letter
      (current letter) (target letter)

theorem affineShiftThreeResidueBlock_mem
    {available : List Nat} {current target : Nat → Fin 3}
    {tested : Nat}
    (member : tested ∈
      affineShiftThreeResidueBlock available current target) :
    tested ∈ available := by
  induction available with
  | nil => simp [affineShiftThreeResidueBlock] at member
  | cons letter rest inductionHypothesis =>
      simp only [affineShiftThreeResidueBlock, List.flatMap_cons,
        List.mem_append] at member
      rcases member with member | member
      · have equal := affineShiftThreeCorrectionBlock_mem member
        subst tested
        exact List.Mem.head rest
      · exact List.Mem.tail letter (inductionHypothesis member)

theorem affineShiftThreeResidueBlock_residue_eq_zero_of_not_mem
    {available : List Nat} {current target : Nat → Fin 3}
    {tested : Nat} (absent : tested ∉ available) :
    affineShiftThreeCountResidue tested
        (affineShiftThreeResidueBlock available current target) = 0 := by
  apply affineShiftThreeCountResidue_eq_zero_of_not_mem
  intro member
  exact absent (affineShiftThreeResidueBlock_mem member)

theorem affineShiftThreeResidueBlock_count_lt_three
    {available : List Nat} (availableNodup : available.Nodup)
    (current target : Nat → Fin 3) (tested : Nat) :
    (affineShiftThreeResidueBlock available current target).count tested < 3 := by
  induction available with
  | nil => simp [affineShiftThreeResidueBlock]
  | cons letter rest inductionHypothesis =>
      have letterAbsent := (List.nodup_cons.mp availableNodup).1
      have restNodup := (List.nodup_cons.mp availableNodup).2
      simp only [affineShiftThreeResidueBlock, List.flatMap_cons,
        List.count_append]
      change
        (affineShiftThreeCorrectionBlock letter
            (current letter) (target letter)).count tested +
          (affineShiftThreeResidueBlock rest current target).count tested < 3
      by_cases same : tested = letter
      · subst tested
        have tailZero :
            (affineShiftThreeResidueBlock rest current target).count letter = 0 := by
          apply List.count_eq_zero.mpr
          intro member
          exact letterAbsent (affineShiftThreeResidueBlock_mem member)
        rw [tailZero, Nat.add_zero]
        exact affineShiftThreeCorrectionBlock_count_lt_three
          letter (current letter) (target letter)
      · rw [affineShiftThreeCorrectionBlock_count_of_ne same]
        simpa using inductionHypothesis restNodup

theorem affineShiftThreeResidueBlock_reaches
    {available : List Nat} (availableNodup : available.Nodup)
    (current target : Nat → Fin 3) {tested : Nat}
    (member : tested ∈ available) :
    current tested + affineShiftThreeCountResidue tested
        (affineShiftThreeResidueBlock available current target) =
      target tested := by
  induction available with
  | nil => simp at member
  | cons letter rest inductionHypothesis =>
      have letterAbsent := (List.nodup_cons.mp availableNodup).1
      have restNodup := (List.nodup_cons.mp availableNodup).2
      rw [affineShiftThreeResidueBlock, List.flatMap_cons,
        affineShiftThreeCountResidue_append]
      change
        current tested +
            (affineShiftThreeCountResidue tested
                (affineShiftThreeCorrectionBlock letter
                  (current letter) (target letter)) +
              affineShiftThreeCountResidue tested
                (affineShiftThreeResidueBlock rest current target)) =
          target tested
      rcases List.mem_cons.mp member with rfl | member
      · rw [affineShiftThreeResidueBlock_residue_eq_zero_of_not_mem
          letterAbsent, affineShiftThreeFinAdd_zero]
        simpa using affineShiftThreeCorrectionBlock_reaches
          tested (current tested) (target tested)
      · have different : tested ≠ letter := by
          intro equal
          subst tested
          exact letterAbsent member
        rw [affineShiftThreeCorrectionBlock_residue_of_ne different,
          affineShiftThreeFinZero_add]
        exact inductionHypothesis restNodup member

/-- Segment normality relative to the markers already rendered. Every new
marker is fresh, and each correction block uses only available markers with
each multiplicity strictly below three. -/
inductive AffineShiftThreeSegmentsNormalFrom :
    List Nat → List AffineShiftThreeSegment → Prop
  | nil (seen : List Nat) :
      AffineShiftThreeSegmentsNormalFrom seen []
  | cons {seen padding : List Nat} {marker : Nat}
      {rest : List AffineShiftThreeSegment} :
      marker ∉ seen →
      (∀ tested, tested ∈ padding → tested ∈ seen ++ [marker]) →
      (∀ tested, padding.count tested < 3) →
      AffineShiftThreeSegmentsNormalFrom (seen ++ [marker]) rest →
      AffineShiftThreeSegmentsNormalFrom seen
        (⟨marker, padding⟩ :: rest)

abbrev AffineShiftThreeSegmentsNormal
    (segments : List AffineShiftThreeSegment) : Prop :=
  AffineShiftThreeSegmentsNormalFrom [] segments

theorem AffineShiftThreeSegmentsNormalFrom.markers_nodup
    {seen : List Nat} {segments : List AffineShiftThreeSegment}
    (normal : AffineShiftThreeSegmentsNormalFrom seen segments)
    (seenNodup : seen.Nodup) :
    (seen ++ affineShiftThreeSegmentMarkers segments).Nodup := by
  induction normal with
  | nil => simpa [affineShiftThreeSegmentMarkers] using seenNodup
  | @cons seen padding marker rest markerFresh blockGuard blockBounded
      restNormal inductionHypothesis =>
      have availableNodup : (seen ++ [marker]).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨seenNodup, by simp, ?_⟩
        intro left leftSeen right rightSeen equal
        have rightEqual : right = marker :=
          List.mem_singleton.mp rightSeen
        have leftEqual : left = marker := equal.trans rightEqual
        exact markerFresh (leftEqual ▸ leftSeen)
      simpa [affineShiftThreeSegmentMarkers, List.append_assoc] using
        inductionHypothesis availableNodup

theorem AffineShiftThreeSegmentsNormalFrom.render_support
    {seen : List Nat} {segments : List AffineShiftThreeSegment}
    (normal : AffineShiftThreeSegmentsNormalFrom seen segments) :
    ∀ {tested}, tested ∈ affineShiftThreeRenderSegments segments →
      tested ∈ seen ++ affineShiftThreeSegmentMarkers segments := by
  induction normal with
  | nil => simp [affineShiftThreeRenderSegments]
  | @cons seen padding marker rest markerFresh blockGuard blockBounded
      restNormal inductionHypothesis =>
      intro tested member
      simp only [affineShiftThreeRenderSegments, List.mem_cons,
        List.mem_append] at member
      simp only [affineShiftThreeSegmentMarkers, List.mem_append,
        List.mem_cons]
      rcases member with rfl | member | member
      · exact Or.inr (Or.inl rfl)
      · have guarded := blockGuard tested member
        rcases List.mem_append.mp guarded with old | current
        · exact Or.inl old
        · exact Or.inr (Or.inl (List.mem_singleton.mp current))
      · have supported := inductionHypothesis member
        simpa [List.append_assoc] using supported

theorem AffineShiftThreeSegmentsNormal.mem_render_iff_marker
    {segments : List AffineShiftThreeSegment}
    (normal : AffineShiftThreeSegmentsNormal segments)
    (tested : Nat) :
    tested ∈ affineShiftThreeRenderSegments segments ↔
      tested ∈ affineShiftThreeSegmentMarkers segments := by
  constructor
  · intro member
    simpa using normal.render_support member
  · exact affineShiftThreeMarker_mem_render

theorem AffineShiftThreeSegmentsNormalFrom.firstOccurrences_render
    {seen : List Nat} {segments : List AffineShiftThreeSegment}
    (normal : AffineShiftThreeSegmentsNormalFrom seen segments) :
    affineShiftThreeFirstOccurrencesFrom seen
        (affineShiftThreeRenderSegments segments) =
      affineShiftThreeSegmentMarkers segments := by
  induction normal with
  | nil => rfl
  | @cons seen padding marker rest markerFresh blockGuard blockBounded
      restNormal inductionHypothesis =>
      rw [affineShiftThreeRenderSegments,
        affineShiftThreeFirstOccurrencesFrom, if_neg markerFresh]
      rw [affineShiftThreeFirstOccurrencesFrom_skip
        (seen ++ [marker]) padding
        (affineShiftThreeRenderSegments rest) blockGuard]
      exact congrArg (List.cons marker) inductionHypothesis

theorem AffineShiftThreeSegmentsNormal.firstOccurrenceOrder_render
    {segments : List AffineShiftThreeSegment}
    (normal : AffineShiftThreeSegmentsNormal segments) :
    affineShiftThreeFirstOccurrenceOrderList
        (affineShiftThreeRenderSegments segments) =
      affineShiftThreeSegmentMarkers segments := by
  exact normal.firstOccurrences_render

/-- The boundary reached after a segment is either the prefix profile before
the next marker or, for the final segment, the total profile. -/
def affineShiftThreeBoundaryTarget
    (source : Word Nat) : List Nat → Nat → Fin 3
  | [], tested => affineShiftThreeWordTotalResidue tested source
  | next :: _, tested =>
      affineShiftThreeWordPrefixResidue next tested source

/-- Build canonical correction blocks while carrying the already-rendered
prefix. The marker list is supplied separately to make the recursion visibly
structural. -/
def affineShiftThreeBuildSegments
    (source : Word Nat) (seen rendered : List Nat) :
    List Nat → List AffineShiftThreeSegment
  | [] => []
  | marker :: rest =>
      let available := seen ++ [marker]
      let beforeBlock := rendered ++ [marker]
      let target := affineShiftThreeBoundaryTarget source rest
      let padding := affineShiftThreeResidueBlock available
        (fun tested =>
          affineShiftThreeCountResidue tested beforeBlock)
        target
      ⟨marker, padding⟩ ::
        affineShiftThreeBuildSegments source available
          (beforeBlock ++ padding) rest

/-- Canonical segments for a word, using its first-occurrence marker order. -/
def affineShiftThreeNormalSegments
    (source : Word Nat) : List AffineShiftThreeSegment :=
  affineShiftThreeBuildSegments source [] []
    (affineShiftThreeFirstOccurrenceOrder source)

private theorem affineShiftThreeBoundaryTarget_eq_zero_of_not_mem
    (source : Word Nat) (seen : List Nat) (marker : Nat)
    (rest : List Nat)
    (orderEq :
      affineShiftThreeFirstOccurrenceOrder source =
        seen ++ marker :: rest)
    (orderNodup : (seen ++ marker :: rest).Nodup)
    (tested : Nat) (absent : tested ∉ seen ++ [marker]) :
    affineShiftThreeBoundaryTarget source rest tested = 0 := by
  cases rest with
  | nil =>
      apply affineShiftThreeCountResidue_eq_zero_of_not_mem
      intro sourceMember
      have orderMember :
          tested ∈ affineShiftThreeFirstOccurrenceOrder source :=
        (affineShiftThreeFirstOccurrenceOrderList_mem_iff
          tested source.toList).mpr sourceMember
      rw [orderEq] at orderMember
      exact absent (by simpa using orderMember)
  | cons next tail =>
      have regroupedNodup :
          ((seen ++ [marker]) ++ next :: tail).Nodup := by
        simpa [List.append_assoc] using orderNodup
      have splitNodup := List.nodup_append.mp regroupedNodup
      have nextAbsent : next ∉ seen ++ [marker] := by
        intro member
        exact splitNodup.2.2 next member next
          (List.Mem.head tail) rfl
      have nextOrderMember :
          next ∈ affineShiftThreeFirstOccurrenceOrder source := by
        rw [orderEq]
        simp
      have nextSourceMember : next ∈ source.toList :=
        (affineShiftThreeFirstOccurrenceOrderList_mem_iff
          next source.toList).mp nextOrderMember
      apply affineShiftThreeCountResidue_eq_zero_of_not_mem
      intro prefixMember
      have orderPrefixMember :
          tested ∈ affineShiftThreePrefixBeforeFirst next
            (affineShiftThreeFirstOccurrenceOrder source) :=
        (affineShiftThreePrefixBeforeFirst_order_mem_iff
          next tested nextSourceMember).mpr prefixMember
      rw [orderEq] at orderPrefixMember
      have groupedOrderPrefixMember :
          tested ∈ affineShiftThreePrefixBeforeFirst next
            ((seen ++ [marker]) ++ next :: tail) := by
        simpa [List.append_assoc] using orderPrefixMember
      rw [affineShiftThreePrefixBeforeFirst_append_hit
        next (seen ++ [marker]) tail nextAbsent] at groupedOrderPrefixMember
      exact absent groupedOrderPrefixMember

/-- The complete recursive contract of the segment builder. -/
structure AffineShiftThreeBuildSpec
    (source : Word Nat) (seen rendered remaining : List Nat)
    (segments : List AffineShiftThreeSegment) : Prop where
  normal : AffineShiftThreeSegmentsNormalFrom seen segments
  markers : affineShiftThreeSegmentMarkers segments = remaining
  renderSupport :
    ∀ {tested}, tested ∈ affineShiftThreeRenderSegments segments →
      tested ∈ seen ++ remaining
  prefixFaithful :
    ∀ {selected}, selected ∈ remaining → ∀ tested,
      affineShiftThreeCountResidue tested
          (affineShiftThreePrefixBeforeFirst selected
            (rendered ++ affineShiftThreeRenderSegments segments)) =
        affineShiftThreeWordPrefixResidue selected tested source
  totalFaithful :
    ∀ tested,
      affineShiftThreeCountResidue tested
          (rendered ++ affineShiftThreeRenderSegments segments) =
        affineShiftThreeWordTotalResidue tested source

private theorem affineShiftThreeBuildSegments_spec
    (source : Word Nat) :
    ∀ (remaining seen rendered : List Nat),
      (seen ++ remaining).Nodup →
      affineShiftThreeFirstOccurrenceOrder source = seen ++ remaining →
      (∀ {tested}, tested ∈ rendered → tested ∈ seen) →
      (match remaining with
        | [] => ∀ tested,
            affineShiftThreeCountResidue tested rendered =
              affineShiftThreeWordTotalResidue tested source
        | marker :: _ => ∀ tested,
            affineShiftThreeCountResidue tested rendered =
              affineShiftThreeWordPrefixResidue marker tested source) →
      AffineShiftThreeBuildSpec source seen rendered remaining
        (affineShiftThreeBuildSegments source seen rendered remaining)
  | [], seen, rendered, orderNodup, orderEq, renderedSupport,
      currentProfile => by
      refine
        { normal := AffineShiftThreeSegmentsNormalFrom.nil seen
          markers := rfl
          renderSupport := ?_
          prefixFaithful := ?_
          totalFaithful := ?_ }
      · intro tested member
        simp [affineShiftThreeBuildSegments,
          affineShiftThreeRenderSegments] at member
      · intro selected member
        simp at member
      · intro tested
        simpa [affineShiftThreeBuildSegments,
          affineShiftThreeRenderSegments] using currentProfile tested
  | marker :: rest, seen, rendered, orderNodup, orderEq,
      renderedSupport, currentProfile => by
      let available := seen ++ [marker]
      let beforeBlock := rendered ++ [marker]
      let target := affineShiftThreeBoundaryTarget source rest
      let padding := affineShiftThreeResidueBlock available
        (fun tested => affineShiftThreeCountResidue tested beforeBlock)
        target
      let nextRendered := beforeBlock ++ padding
      have regroupedNodup : (available ++ rest).Nodup := by
        simpa [available, List.append_assoc] using orderNodup
      have availableNodup : available.Nodup :=
        (List.nodup_append.mp regroupedNodup).1
      have markerFresh : marker ∉ seen := by
        intro member
        have splitNodup := List.nodup_append.mp orderNodup
        exact splitNodup.2.2 marker member marker
          (List.Mem.head rest) rfl
      have beforeBlockSupport :
          ∀ {tested}, tested ∈ beforeBlock → tested ∈ available := by
        intro tested member
        rcases List.mem_append.mp member with old | current
        · exact List.mem_append_left [marker] (renderedSupport old)
        · have equal : tested = marker := List.mem_singleton.mp current
          subst tested
          exact List.mem_append_right seen (List.Mem.head [])
      have paddingSupport :
          ∀ {tested}, tested ∈ padding → tested ∈ available := by
        intro tested member
        exact affineShiftThreeResidueBlock_mem member
      have nextRenderedSupport :
          ∀ {tested}, tested ∈ nextRendered → tested ∈ available := by
        intro tested member
        rcases List.mem_append.mp member with before | block
        · exact beforeBlockSupport before
        · exact paddingSupport block
      have targetZero :
          ∀ tested, tested ∉ available → target tested = 0 := by
        intro tested absent
        exact affineShiftThreeBoundaryTarget_eq_zero_of_not_mem
          source seen marker rest orderEq orderNodup tested <| by
            simpa [available] using absent
      have nextProfile :
          ∀ tested,
            affineShiftThreeCountResidue tested nextRendered =
              target tested := by
        intro tested
        simp only [nextRendered, affineShiftThreeCountResidue_append]
        by_cases member : tested ∈ available
        · simpa [padding, beforeBlock] using
            affineShiftThreeResidueBlock_reaches availableNodup
              (fun tested =>
                affineShiftThreeCountResidue tested beforeBlock)
              target member
        · have beforeAbsent : tested ∉ beforeBlock := by
            intro beforeMember
            exact member (beforeBlockSupport beforeMember)
          rw [affineShiftThreeCountResidue_eq_zero_of_not_mem
              tested beforeBlock beforeAbsent,
            affineShiftThreeResidueBlock_residue_eq_zero_of_not_mem
              member,
            affineShiftThreeFinZero_add, targetZero tested member]
      have recursiveOrderEq :
          affineShiftThreeFirstOccurrenceOrder source =
            available ++ rest := by
        simpa [available, List.append_assoc] using orderEq
      have recursiveSpec :=
        affineShiftThreeBuildSegments_spec source rest available
          nextRendered regroupedNodup recursiveOrderEq
          nextRenderedSupport (by
            cases rest with
            | nil => simpa [target, affineShiftThreeBoundaryTarget] using
                nextProfile
            | cons next tail =>
                simpa [target, affineShiftThreeBoundaryTarget] using
                  nextProfile)
      have markerPrefix :
          affineShiftThreePrefixBeforeFirst marker
              (rendered ++
                affineShiftThreeRenderSegments
                  (⟨marker, padding⟩ ::
                    affineShiftThreeBuildSegments source available
                      nextRendered rest)) =
            rendered := by
        have markerAbsentRendered : marker ∉ rendered := by
          intro member
          exact markerFresh (renderedSupport member)
        simpa [affineShiftThreeRenderSegments, List.append_assoc] using
          affineShiftThreePrefixBeforeFirst_append_hit marker rendered
            (padding ++ affineShiftThreeRenderSegments
              (affineShiftThreeBuildSegments source available
                nextRendered rest)) markerAbsentRendered
      refine
        { normal := ?_
          markers := ?_
          renderSupport := ?_
          prefixFaithful := ?_
          totalFaithful := ?_ }
      · apply AffineShiftThreeSegmentsNormalFrom.cons markerFresh
        · intro tested member
          simpa [available] using paddingSupport member
        · intro tested
          exact affineShiftThreeResidueBlock_count_lt_three
            availableNodup
            (fun tested =>
              affineShiftThreeCountResidue tested beforeBlock)
            target tested
        · exact recursiveSpec.normal
      · simp only [affineShiftThreeBuildSegments,
          affineShiftThreeSegmentMarkers]
        exact congrArg (List.cons marker) recursiveSpec.markers
      · intro tested member
        simp only [affineShiftThreeBuildSegments,
          affineShiftThreeRenderSegments, List.mem_cons,
          List.mem_append] at member
        rcases member with rfl | blockMember | restMember
        · simp
        · have supported := paddingSupport blockMember
          simpa [available, List.append_assoc] using
            List.mem_append_left rest supported
        · have supported := recursiveSpec.renderSupport restMember
          simpa [available, List.append_assoc] using supported
      · intro selected member tested
        rcases List.mem_cons.mp member with rfl | restMember
        · rw [affineShiftThreeBuildSegments, markerPrefix]
          exact currentProfile tested
        · have recursive := recursiveSpec.prefixFaithful restMember tested
          simpa [affineShiftThreeBuildSegments,
            affineShiftThreeRenderSegments, nextRendered,
            beforeBlock, List.append_assoc] using recursive
      · intro tested
        have recursive := recursiveSpec.totalFaithful tested
        simpa [affineShiftThreeBuildSegments,
          affineShiftThreeRenderSegments, nextRendered,
          beforeBlock, List.append_assoc] using recursive

private theorem affineShiftThreeFirstMarker_prefix_zero
    (source : Word Nat) (marker : Nat) (rest : List Nat)
    (orderEq :
      affineShiftThreeFirstOccurrenceOrder source = marker :: rest)
    (tested : Nat) :
    affineShiftThreeWordPrefixResidue marker tested source = 0 := by
  apply affineShiftThreeCountResidue_eq_zero_of_not_mem
  intro prefixMember
  have markerOrderMember :
      marker ∈ affineShiftThreeFirstOccurrenceOrder source := by
    rw [orderEq]
    exact List.Mem.head rest
  have markerSourceMember : marker ∈ source.toList :=
    (affineShiftThreeFirstOccurrenceOrderList_mem_iff
      marker source.toList).mp markerOrderMember
  have orderPrefixMember :
      tested ∈ affineShiftThreePrefixBeforeFirst marker
        (affineShiftThreeFirstOccurrenceOrder source) :=
    (affineShiftThreePrefixBeforeFirst_order_mem_iff
      marker tested markerSourceMember).mpr prefixMember
  rw [orderEq] at orderPrefixMember
  simp [affineShiftThreePrefixBeforeFirst] at orderPrefixMember

/-- The canonical builder is normal and realizes every source prefix and total
residue coordinate. -/
theorem affineShiftThreeNormalSegments_spec (source : Word Nat) :
    AffineShiftThreeBuildSpec source [] []
      (affineShiftThreeFirstOccurrenceOrder source)
      (affineShiftThreeNormalSegments source) := by
  unfold affineShiftThreeNormalSegments
  let order := affineShiftThreeFirstOccurrenceOrder source
  change AffineShiftThreeBuildSpec source [] [] order
    (affineShiftThreeBuildSegments source [] [] order)
  have orderNodup : order.Nodup :=
    affineShiftThreeFirstOccurrenceOrderList_nodup source.toList
  have renderedSupport :
      ∀ {tested}, tested ∈ ([] : List Nat) → tested ∈ ([] : List Nat) := by
    simp
  cases orderEq : order with
  | nil =>
      have headOrderMember : source.head ∈ order := by
        exact (affineShiftThreeFirstOccurrenceOrderList_mem_iff
          source.head source.toList).mpr (List.Mem.head source.tail)
      rw [orderEq] at headOrderMember
      simp at headOrderMember
  | cons marker rest =>
      apply affineShiftThreeBuildSegments_spec source
        (marker :: rest) [] []
      · simpa [orderEq] using orderNodup
      · simp [order, orderEq]
      · exact renderedSupport
      · intro tested
        have prefixZero :=
          affineShiftThreeFirstMarker_prefix_zero
            source marker rest (by simp [order, orderEq]) tested
        simpa using prefixZero.symm

theorem affineShiftThreeNormalSegments_normal (source : Word Nat) :
    AffineShiftThreeSegmentsNormal
      (affineShiftThreeNormalSegments source) :=
  (affineShiftThreeNormalSegments_spec source).normal

theorem affineShiftThreeNormalSegments_markers (source : Word Nat) :
    affineShiftThreeSegmentMarkers
        (affineShiftThreeNormalSegments source) =
      affineShiftThreeFirstOccurrenceOrder source :=
  (affineShiftThreeNormalSegments_spec source).markers

theorem affineShiftThreeNormalSegments_render_support
    (source : Word Nat) {tested : Nat}
    (member : tested ∈ affineShiftThreeRenderSegments
      (affineShiftThreeNormalSegments source)) :
    tested ∈ affineShiftThreeFirstOccurrenceOrder source := by
  simpa using
    (affineShiftThreeNormalSegments_spec source).renderSupport member

theorem affineShiftThreeNormalSegments_firstOccurrenceOrder
    (source : Word Nat) :
    affineShiftThreeFirstOccurrenceOrderList
        (affineShiftThreeRenderSegments
          (affineShiftThreeNormalSegments source)) =
      affineShiftThreeFirstOccurrenceOrder source := by
  calc
    affineShiftThreeFirstOccurrenceOrderList
        (affineShiftThreeRenderSegments
          (affineShiftThreeNormalSegments source)) =
        affineShiftThreeSegmentMarkers
          (affineShiftThreeNormalSegments source) :=
      AffineShiftThreeSegmentsNormal.firstOccurrenceOrder_render
        (affineShiftThreeNormalSegments_normal source)
    _ = affineShiftThreeFirstOccurrenceOrder source :=
      affineShiftThreeNormalSegments_markers source

theorem affineShiftThreeNormalSegments_totalResidue
    (source : Word Nat) (tested : Nat) :
    affineShiftThreeCountResidue tested
        (affineShiftThreeRenderSegments
          (affineShiftThreeNormalSegments source)) =
      affineShiftThreeWordTotalResidue tested source := by
  simpa using
    (affineShiftThreeNormalSegments_spec source).totalFaithful tested

theorem affineShiftThreeNormalSegments_prefixResidue
    (source : Word Nat) (selected tested : Nat) :
    affineShiftThreeCountResidue tested
        (affineShiftThreePrefixBeforeFirst selected
          (affineShiftThreeRenderSegments
            (affineShiftThreeNormalSegments source))) =
      affineShiftThreeWordPrefixResidue selected tested source := by
  by_cases sourceMember : selected ∈ source.toList
  · have orderMember :
        selected ∈ affineShiftThreeFirstOccurrenceOrder source :=
      (affineShiftThreeFirstOccurrenceOrderList_mem_iff
        selected source.toList).mpr sourceMember
    simpa using
      (affineShiftThreeNormalSegments_spec source).prefixFaithful
        orderMember tested
  · have orderAbsent :
        selected ∉ affineShiftThreeFirstOccurrenceOrder source := by
      intro member
      exact sourceMember <|
        (affineShiftThreeFirstOccurrenceOrderList_mem_iff
          selected source.toList).mp member
    have renderAbsent :
        selected ∉ affineShiftThreeRenderSegments
          (affineShiftThreeNormalSegments source) := by
      intro member
      exact orderAbsent <|
        affineShiftThreeNormalSegments_render_support source member
    unfold affineShiftThreeWordPrefixResidue
    rw [affineShiftThreePrefixBeforeFirst_eq_self_of_not_mem
        selected source.toList sourceMember,
      affineShiftThreePrefixBeforeFirst_eq_self_of_not_mem
        selected
        (affineShiftThreeRenderSegments
          (affineShiftThreeNormalSegments source)) renderAbsent]
    exact affineShiftThreeNormalSegments_totalResidue source tested

theorem affineShiftThreeNormalSegments_ne_nil (source : Word Nat) :
    affineShiftThreeNormalSegments source ≠ [] := by
  intro empty
  have markers := affineShiftThreeNormalSegments_markers source
  rw [empty] at markers
  have headMember :
      source.head ∈ affineShiftThreeFirstOccurrenceOrder source :=
    (affineShiftThreeFirstOccurrenceOrderList_mem_iff
      source.head source.toList).mpr (List.Mem.head source.tail)
  rw [← markers] at headMember
  simp [affineShiftThreeSegmentMarkers] at headMember

/-- The canonical nonempty word rendered from `affineShiftThreeNormalSegments`. -/
def affineShiftThreeNormalWord (source : Word Nat) : Word Nat :=
  match affineShiftThreeNormalSegments source with
  | [] => source
  | segment :: rest => affineShiftThreeRenderWord segment rest

@[simp]
theorem affineShiftThreeNormalWord_toList (source : Word Nat) :
    (affineShiftThreeNormalWord source).toList =
      affineShiftThreeRenderSegments
        (affineShiftThreeNormalSegments source) := by
  cases segmentsEq : affineShiftThreeNormalSegments source with
  | nil =>
      exact False.elim
        (affineShiftThreeNormalSegments_ne_nil source segmentsEq)
  | cons segment rest =>
      simp [affineShiftThreeNormalWord, segmentsEq]

theorem affineShiftThreeNormalWord_firstOccurrenceOrder
    (source : Word Nat) :
    affineShiftThreeFirstOccurrenceOrder
        (affineShiftThreeNormalWord source) =
      affineShiftThreeFirstOccurrenceOrder source := by
  rw [affineShiftThreeFirstOccurrenceOrder,
    affineShiftThreeNormalWord_toList,
    affineShiftThreeNormalSegments_firstOccurrenceOrder]

theorem affineShiftThreeNormalWord_totalResidue
    (source : Word Nat) (tested : Nat) :
    affineShiftThreeWordTotalResidue tested
        (affineShiftThreeNormalWord source) =
      affineShiftThreeWordTotalResidue tested source := by
  rw [affineShiftThreeWordTotalResidue,
    affineShiftThreeNormalWord_toList]
  exact affineShiftThreeNormalSegments_totalResidue source tested

theorem affineShiftThreeNormalWord_prefixResidue
    (source : Word Nat) (selected tested : Nat) :
    affineShiftThreeWordPrefixResidue selected tested
        (affineShiftThreeNormalWord source) =
      affineShiftThreeWordPrefixResidue selected tested source := by
  rw [affineShiftThreeWordPrefixResidue,
    affineShiftThreeNormalWord_toList]
  exact affineShiftThreeNormalSegments_prefixResidue
    source selected tested

/-- Canonical rendering is semantics-faithful for every valuation. -/
theorem affineShiftThreeNormalWord_eval
    (source : Word Nat) (valuation : Nat → Fin 6) :
    affineShiftThree.semigroup.eval valuation
        (affineShiftThreeNormalWord source) =
      affineShiftThree.semigroup.eval valuation source := by
  apply affineShiftThreeEval_eq_of_invariants
  · exact affineShiftThreeNormalWord_firstOccurrenceOrder source
  · exact affineShiftThreeNormalWord_totalResidue source
  · exact affineShiftThreeNormalWord_prefixResidue source

theorem affineShiftThreeNormalSegments_evalList
    (source : Word Nat) (valuation : Nat → Fin 6) :
    affineShiftThreeEvalList valuation
        (affineShiftThreeRenderSegments
          (affineShiftThreeNormalSegments source)) =
      affineShiftThreeEvalList valuation source.toList := by
  rw [← affineShiftThreeNormalWord_toList source,
    ← affineShiftThreeEval_eq_evalList valuation
      (affineShiftThreeNormalWord source),
    ← affineShiftThreeEval_eq_evalList valuation source]
  exact affineShiftThreeNormalWord_eval source valuation

private theorem affineShiftThreeBuildSegments_eq_of_invariants
    (left right : Word Nat)
    (samePrefix : ∀ selected tested,
      affineShiftThreeWordPrefixResidue selected tested left =
        affineShiftThreeWordPrefixResidue selected tested right)
    (sameTotal : ∀ tested,
      affineShiftThreeWordTotalResidue tested left =
        affineShiftThreeWordTotalResidue tested right) :
    ∀ (remaining seen rendered : List Nat),
      affineShiftThreeBuildSegments left seen rendered remaining =
        affineShiftThreeBuildSegments right seen rendered remaining
  | [], seen, rendered => rfl
  | marker :: rest, seen, rendered => by
      let available := seen ++ [marker]
      let beforeBlock := rendered ++ [marker]
      let current := fun tested =>
        affineShiftThreeCountResidue tested beforeBlock
      have targetEq :
          affineShiftThreeBoundaryTarget left rest =
            affineShiftThreeBoundaryTarget right rest := by
        funext tested
        cases rest with
        | nil =>
            exact sameTotal tested
        | cons next tail =>
            exact samePrefix next tested
      change
        (⟨marker,
            affineShiftThreeResidueBlock available current
              (affineShiftThreeBoundaryTarget left rest)⟩ ::
          affineShiftThreeBuildSegments left available
            (beforeBlock ++
              affineShiftThreeResidueBlock available current
                (affineShiftThreeBoundaryTarget left rest)) rest) =
        (⟨marker,
            affineShiftThreeResidueBlock available current
              (affineShiftThreeBoundaryTarget right rest)⟩ ::
          affineShiftThreeBuildSegments right available
            (beforeBlock ++
              affineShiftThreeResidueBlock available current
                (affineShiftThreeBoundaryTarget right rest)) rest)
      rw [targetEq]
      exact congrArg (List.cons
        ⟨marker,
          affineShiftThreeResidueBlock available current
            (affineShiftThreeBoundaryTarget right rest)⟩)
        (affineShiftThreeBuildSegments_eq_of_invariants
          left right samePrefix sameTotal rest available
          (beforeBlock ++
            affineShiftThreeResidueBlock available current
              (affineShiftThreeBoundaryTarget right rest)))

/-- The canonical segment data depends only on the contract invariant. -/
theorem affineShiftThreeNormalSegments_eq_of_invariants
    (left right : Word Nat)
    (sameOrder :
      affineShiftThreeFirstOccurrenceOrder left =
        affineShiftThreeFirstOccurrenceOrder right)
    (sameTotal : ∀ tested,
      affineShiftThreeWordTotalResidue tested left =
        affineShiftThreeWordTotalResidue tested right)
    (samePrefix : ∀ selected tested,
      affineShiftThreeWordPrefixResidue selected tested left =
        affineShiftThreeWordPrefixResidue selected tested right) :
    affineShiftThreeNormalSegments left =
      affineShiftThreeNormalSegments right := by
  unfold affineShiftThreeNormalSegments
  rw [sameOrder]
  exact affineShiftThreeBuildSegments_eq_of_invariants
    left right samePrefix sameTotal _ [] []

/-- Invariant-equivalent words have literally equal canonical renders. -/
theorem affineShiftThreeNormalWord_eq_of_invariants
    (left right : Word Nat)
    (sameOrder :
      affineShiftThreeFirstOccurrenceOrder left =
        affineShiftThreeFirstOccurrenceOrder right)
    (sameTotal : ∀ tested,
      affineShiftThreeWordTotalResidue tested left =
        affineShiftThreeWordTotalResidue tested right)
    (samePrefix : ∀ selected tested,
      affineShiftThreeWordPrefixResidue selected tested left =
        affineShiftThreeWordPrefixResidue selected tested right) :
    affineShiftThreeNormalWord left =
      affineShiftThreeNormalWord right := by
  have segmentsEq :=
    affineShiftThreeNormalSegments_eq_of_invariants
      left right sameOrder sameTotal samePrefix
  cases leftSegmentsEq : affineShiftThreeNormalSegments left with
  | nil =>
      exact False.elim <|
        affineShiftThreeNormalSegments_ne_nil left leftSegmentsEq
  | cons segment rest =>
      have rightSegmentsEq :
          affineShiftThreeNormalSegments right = segment :: rest := by
        rw [← segmentsEq, leftSegmentsEq]
      simp [affineShiftThreeNormalWord, leftSegmentsEq, rightSegmentsEq]

/-- Canonicalization is idempotent as a literal word operation. -/
theorem affineShiftThreeNormalWord_idempotent (source : Word Nat) :
    affineShiftThreeNormalWord (affineShiftThreeNormalWord source) =
      affineShiftThreeNormalWord source := by
  apply affineShiftThreeNormalWord_eq_of_invariants
  · exact affineShiftThreeNormalWord_firstOccurrenceOrder source
  · exact affineShiftThreeNormalWord_totalResidue source
  · exact affineShiftThreeNormalWord_prefixResidue source

end SemigroupBasis.Examples
