import SemigroupBasis.Examples.EdmundsPeriodTwoBlocksSyntax

namespace SemigroupBasis.CoRoots.S5_443Family.CanonicalSyntax

open SemigroupBasis
open SemigroupBasis.Examples

/-- Parse a flattened normal list into its first-occurrence blocks.  The
function is total, but its intended inverse law is stated under
`EdmundsPeriodTwoBlocksNormal`. -/
def edmundsPeriodTwoBlocksOfNormalList :
    List Nat → List EdmundsPeriodTwoBlock
  | [] => []
  | [x] => [.single x]
  | [x, y] =>
      if x = y then [.double x]
      else [.single x, .single y]
  | x :: y :: z :: xs =>
      if x = y then
        if y = z then
          .triple x :: edmundsPeriodTwoBlocksOfNormalList xs
        else
          .double x ::
            edmundsPeriodTwoBlocksOfNormalList (z :: xs)
      else
        .single x ::
          edmundsPeriodTwoBlocksOfNormalList (y :: z :: xs)
termination_by xs => xs.length

@[simp]
theorem edmundsPeriodTwoBlocksOfNormalList_nil :
    edmundsPeriodTwoBlocksOfNormalList [] = [] :=
  by simp [edmundsPeriodTwoBlocksOfNormalList]

private theorem blocksOfNormalList_single
    {x : Nat} {xs : List Nat}
    (xNotMem : x ∉ xs) :
    edmundsPeriodTwoBlocksOfNormalList (x :: xs) =
      .single x :: edmundsPeriodTwoBlocksOfNormalList xs := by
  cases xs with
  | nil => simp [edmundsPeriodTwoBlocksOfNormalList]
  | cons y ys =>
      have hxy : x ≠ y := by
        intro h
        subst y
        exact xNotMem (List.Mem.head ys)
      cases ys with
      | nil => simp [edmundsPeriodTwoBlocksOfNormalList, hxy]
      | cons z zs =>
          simp [edmundsPeriodTwoBlocksOfNormalList, hxy]

private theorem blocksOfNormalList_double
    {x : Nat} {xs : List Nat}
    (xNotMem : x ∉ xs) :
    edmundsPeriodTwoBlocksOfNormalList (x :: x :: xs) =
      .double x :: edmundsPeriodTwoBlocksOfNormalList xs := by
  cases xs with
  | nil => simp [edmundsPeriodTwoBlocksOfNormalList]
  | cons y ys =>
      have hxy : x ≠ y := by
        intro h
        subst y
        exact xNotMem (List.Mem.head ys)
      simp [edmundsPeriodTwoBlocksOfNormalList, hxy]

private theorem blocksOfNormalList_triple
    {x : Nat} {xs : List Nat}
    (xNotMem : x ∉ xs) :
    edmundsPeriodTwoBlocksOfNormalList (x :: x :: x :: xs) =
      .triple x :: edmundsPeriodTwoBlocksOfNormalList xs := by
  cases xs with
  | nil => simp [edmundsPeriodTwoBlocksOfNormalList]
  | cons y ys =>
      simp [edmundsPeriodTwoBlocksOfNormalList]

/-- Rendering the parsed blocks recovers the original flattened list whenever
the latter is a first-occurrence block normal form. -/
theorem render_edmundsPeriodTwoBlocksOfNormalList
    {xs : List Nat} (normal : EdmundsPeriodTwoBlocksNormal xs) :
    renderEdmundsPeriodTwoBlocks
        (edmundsPeriodTwoBlocksOfNormalList xs) = xs := by
  induction normal with
  | nil =>
      simp [renderEdmundsPeriodTwoBlocks]
  | single x xs _ xNotMem ih =>
      rw [blocksOfNormalList_single xNotMem]
      simp only [renderEdmundsPeriodTwoBlocks, List.flatMap_cons,
        EdmundsPeriodTwoBlock.render]
      change [x] ++
          renderEdmundsPeriodTwoBlocks
            (edmundsPeriodTwoBlocksOfNormalList xs) =
        x :: xs
      rw [ih]
      rfl
  | double x xs _ xNotMem ih =>
      rw [blocksOfNormalList_double xNotMem]
      simp only [renderEdmundsPeriodTwoBlocks, List.flatMap_cons,
        EdmundsPeriodTwoBlock.render]
      change [x, x] ++
          renderEdmundsPeriodTwoBlocks
            (edmundsPeriodTwoBlocksOfNormalList xs) =
        x :: x :: xs
      rw [ih]
      rfl
  | triple x xs _ xNotMem ih =>
      rw [blocksOfNormalList_triple xNotMem]
      simp only [renderEdmundsPeriodTwoBlocks, List.flatMap_cons,
        EdmundsPeriodTwoBlock.render]
      change [x, x, x] ++
          renderEdmundsPeriodTwoBlocks
            (edmundsPeriodTwoBlocksOfNormalList xs) =
        x :: x :: x :: xs
      rw [ih]
      rfl

private theorem normal_blocks_labels_nodup
    {xs : List Nat} (normal : EdmundsPeriodTwoBlocksNormal xs) :
    ((edmundsPeriodTwoBlocksOfNormalList xs).map
      EdmundsPeriodTwoBlock.label).Nodup := by
  induction normal with
  | nil =>
      simp
  | single x xs normal xNotMem ih =>
      rw [blocksOfNormalList_single xNotMem]
      simp only [List.map_cons, EdmundsPeriodTwoBlock.label,
        List.nodup_cons]
      refine ⟨?_, ih⟩
      intro labelMem
      rcases List.mem_map.mp labelMem with
        ⟨block, blockMem, labelEq⟩
      have blockLabelMem : block.label ∈ block.render := by
        cases block <;>
          simp [EdmundsPeriodTwoBlock.label,
            EdmundsPeriodTwoBlock.render]
      rw [labelEq] at blockLabelMem
      have renderedMem :
          x ∈ renderEdmundsPeriodTwoBlocks
            (edmundsPeriodTwoBlocksOfNormalList xs) :=
        List.mem_flatMap.mpr ⟨block, blockMem, blockLabelMem⟩
      rw [render_edmundsPeriodTwoBlocksOfNormalList normal] at renderedMem
      exact xNotMem renderedMem
  | double x xs normal xNotMem ih =>
      rw [blocksOfNormalList_double xNotMem]
      simp only [List.map_cons, EdmundsPeriodTwoBlock.label,
        List.nodup_cons]
      refine ⟨?_, ih⟩
      intro labelMem
      rcases List.mem_map.mp labelMem with
        ⟨block, blockMem, labelEq⟩
      have blockLabelMem : block.label ∈ block.render := by
        cases block <;>
          simp [EdmundsPeriodTwoBlock.label,
            EdmundsPeriodTwoBlock.render]
      rw [labelEq] at blockLabelMem
      have renderedMem :
          x ∈ renderEdmundsPeriodTwoBlocks
            (edmundsPeriodTwoBlocksOfNormalList xs) :=
        List.mem_flatMap.mpr ⟨block, blockMem, blockLabelMem⟩
      rw [render_edmundsPeriodTwoBlocksOfNormalList normal] at renderedMem
      exact xNotMem renderedMem
  | triple x xs normal xNotMem ih =>
      rw [blocksOfNormalList_triple xNotMem]
      simp only [List.map_cons, EdmundsPeriodTwoBlock.label,
        List.nodup_cons]
      refine ⟨?_, ih⟩
      intro labelMem
      rcases List.mem_map.mp labelMem with
        ⟨block, blockMem, labelEq⟩
      have blockLabelMem : block.label ∈ block.render := by
        cases block <;>
          simp [EdmundsPeriodTwoBlock.label,
            EdmundsPeriodTwoBlock.render]
      rw [labelEq] at blockLabelMem
      have renderedMem :
          x ∈ renderEdmundsPeriodTwoBlocks
            (edmundsPeriodTwoBlocksOfNormalList xs) :=
        List.mem_flatMap.mpr ⟨block, blockMem, blockLabelMem⟩
      rw [render_edmundsPeriodTwoBlocksOfNormalList normal] at renderedMem
      exact xNotMem renderedMem

/-- Parsing a first-occurrence normal list produces pairwise distinct block
labels. This is the public parser invariant consumed by later trace adapters. -/
theorem edmundsPeriodTwoBlocksOfNormalList_labels_nodup
    {xs : List Nat} (normal : EdmundsPeriodTwoBlocksNormal xs) :
    ((edmundsPeriodTwoBlocksOfNormalList xs).map
      EdmundsPeriodTwoBlock.label).Nodup :=
  normal_blocks_labels_nodup normal

/-- A maximal run of repeated blocks, followed by an optional singleton
separator.  A segment with `singleton = none` is necessarily terminal in a
canonical segmentation. -/
structure EdmundsPeriodTwoSegment where
  repeated : List EdmundsPeriodTwoRepeatedBlock
  singleton : Option Nat
deriving DecidableEq, Repr

namespace EdmundsPeriodTwoSegment

def toBlocks (segment : EdmundsPeriodTwoSegment) :
    List EdmundsPeriodTwoBlock :=
  segment.repeated.map EdmundsPeriodTwoRepeatedBlock.toBlock ++
    segment.singleton.toList.map EdmundsPeriodTwoBlock.single

def render (segment : EdmundsPeriodTwoSegment) : List Nat :=
  renderEdmundsPeriodTwoRepeatedBlocks segment.repeated ++
    segment.singleton.toList

def labels (segment : EdmundsPeriodTwoSegment) : List Nat :=
  segment.repeated.map EdmundsPeriodTwoRepeatedBlock.label ++
    segment.singleton.toList

end EdmundsPeriodTwoSegment

def renderEdmundsPeriodTwoSegments
    (segments : List EdmundsPeriodTwoSegment) : List Nat :=
  segments.flatMap EdmundsPeriodTwoSegment.render

def allEdmundsPeriodTwoSegmentLabels
    (segments : List EdmundsPeriodTwoSegment) : List Nat :=
  segments.flatMap EdmundsPeriodTwoSegment.labels

def allEdmundsPeriodTwoRepeatedBlocks
    (segments : List EdmundsPeriodTwoSegment) :
    List EdmundsPeriodTwoRepeatedBlock :=
  segments.flatMap EdmundsPeriodTwoSegment.repeated

def edmundsPeriodTwoSingletonLabels
    (segments : List EdmundsPeriodTwoSegment) : List Nat :=
  segments.filterMap EdmundsPeriodTwoSegment.singleton

private def doubleLabelsOfRepeated
    (blocks : List EdmundsPeriodTwoRepeatedBlock) : List Nat :=
  blocks.filterMap
    (fun block =>
      match block with
      | .double x => some x
      | .triple _ => none)

private def tripleLabelsOfRepeated
    (blocks : List EdmundsPeriodTwoRepeatedBlock) : List Nat :=
  blocks.filterMap
    (fun block =>
      match block with
      | .double _ => none
      | .triple x => some x)

def edmundsPeriodTwoDoubleLabels
    (segments : List EdmundsPeriodTwoSegment) : List Nat :=
  doubleLabelsOfRepeated
    (allEdmundsPeriodTwoRepeatedBlocks segments)

def edmundsPeriodTwoTripleLabels
    (segments : List EdmundsPeriodTwoSegment) : List Nat :=
  tripleLabelsOfRepeated
    (allEdmundsPeriodTwoRepeatedBlocks segments)

def edmundsPeriodTwoBlocksToSegments :
    List EdmundsPeriodTwoBlock → List EdmundsPeriodTwoSegment
  | [] => []
  | .single x :: blocks =>
      ⟨[], some x⟩ :: edmundsPeriodTwoBlocksToSegments blocks
  | .double x :: blocks =>
      match edmundsPeriodTwoBlocksToSegments blocks with
      | [] => [⟨[.double x], none⟩]
      | segment :: rest =>
          ⟨.double x :: segment.repeated, segment.singleton⟩ :: rest
  | .triple x :: blocks =>
      match edmundsPeriodTwoBlocksToSegments blocks with
      | [] => [⟨[.triple x], none⟩]
      | segment :: rest =>
          ⟨.triple x :: segment.repeated, segment.singleton⟩ :: rest

def edmundsPeriodTwoSegmentToBlocks
    (segment : EdmundsPeriodTwoSegment) :
    List EdmundsPeriodTwoBlock :=
  segment.toBlocks

def edmundsPeriodTwoSegmentsToBlocks
    (segments : List EdmundsPeriodTwoSegment) :
    List EdmundsPeriodTwoBlock :=
  segments.flatMap edmundsPeriodTwoSegmentToBlocks

/-- Segmenting a block list and flattening it back loses no information,
including the double/triple tag on every repeated block. -/
theorem edmundsPeriodTwoSegments_blocks_roundtrip :
    ∀ blocks : List EdmundsPeriodTwoBlock,
      edmundsPeriodTwoSegmentsToBlocks
        (edmundsPeriodTwoBlocksToSegments blocks) = blocks
  | [] => rfl
  | .single x :: blocks => by
      simp only [edmundsPeriodTwoBlocksToSegments,
        edmundsPeriodTwoSegmentsToBlocks, List.flatMap_cons,
        edmundsPeriodTwoSegmentToBlocks,
        EdmundsPeriodTwoSegment.toBlocks, List.map_nil,
        List.nil_append, Option.toList_some, List.map_cons,
        List.map_nil]
      change EdmundsPeriodTwoBlock.single x ::
          edmundsPeriodTwoSegmentsToBlocks
            (edmundsPeriodTwoBlocksToSegments blocks) =
        EdmundsPeriodTwoBlock.single x :: blocks
      rw [edmundsPeriodTwoSegments_blocks_roundtrip blocks]
  | .double x :: blocks => by
      cases h : edmundsPeriodTwoBlocksToSegments blocks with
      | nil =>
          have blocksEmpty : blocks = [] := by
            have roundtrip :=
              edmundsPeriodTwoSegments_blocks_roundtrip blocks
            rw [h] at roundtrip
            simpa [edmundsPeriodTwoSegmentsToBlocks] using
              roundtrip.symm
          subst blocks
          rfl
      | cons segment rest =>
          have roundtrip :=
            edmundsPeriodTwoSegments_blocks_roundtrip blocks
          rw [h] at roundtrip
          simp only [edmundsPeriodTwoSegmentsToBlocks,
            List.flatMap_cons] at roundtrip
          simp only [edmundsPeriodTwoBlocksToSegments, h,
            edmundsPeriodTwoSegmentsToBlocks, List.flatMap_cons,
            edmundsPeriodTwoSegmentToBlocks,
            EdmundsPeriodTwoSegment.toBlocks, List.map_cons,
            EdmundsPeriodTwoRepeatedBlock.toBlock]
          change EdmundsPeriodTwoBlock.double x ::
              (edmundsPeriodTwoSegmentToBlocks segment ++
                edmundsPeriodTwoSegmentsToBlocks rest) =
            EdmundsPeriodTwoBlock.double x :: blocks
          simpa [edmundsPeriodTwoSegmentsToBlocks] using
            congrArg (List.cons (EdmundsPeriodTwoBlock.double x))
              roundtrip
  | .triple x :: blocks => by
      cases h : edmundsPeriodTwoBlocksToSegments blocks with
      | nil =>
          have blocksEmpty : blocks = [] := by
            have roundtrip :=
              edmundsPeriodTwoSegments_blocks_roundtrip blocks
            rw [h] at roundtrip
            simpa [edmundsPeriodTwoSegmentsToBlocks] using
              roundtrip.symm
          subst blocks
          rfl
      | cons segment rest =>
          have roundtrip :=
            edmundsPeriodTwoSegments_blocks_roundtrip blocks
          rw [h] at roundtrip
          simp only [edmundsPeriodTwoSegmentsToBlocks,
            List.flatMap_cons] at roundtrip
          simp only [edmundsPeriodTwoBlocksToSegments, h,
            edmundsPeriodTwoSegmentsToBlocks, List.flatMap_cons,
            edmundsPeriodTwoSegmentToBlocks,
            EdmundsPeriodTwoSegment.toBlocks, List.map_cons,
            EdmundsPeriodTwoRepeatedBlock.toBlock]
          change EdmundsPeriodTwoBlock.triple x ::
              (edmundsPeriodTwoSegmentToBlocks segment ++
                edmundsPeriodTwoSegmentsToBlocks rest) =
            EdmundsPeriodTwoBlock.triple x :: blocks
          simpa [edmundsPeriodTwoSegmentsToBlocks] using
            congrArg (List.cons (EdmundsPeriodTwoBlock.triple x))
              roundtrip

def edmundsPeriodTwoSortRepeated
    (blocks : List EdmundsPeriodTwoRepeatedBlock) :
    List EdmundsPeriodTwoRepeatedBlock :=
  blocks.mergeSort
    (fun left right =>
      decide (left.label ≤ right.label))

def edmundsPeriodTwoSortSegment
    (segment : EdmundsPeriodTwoSegment) :
    EdmundsPeriodTwoSegment :=
  ⟨edmundsPeriodTwoSortRepeated segment.repeated, segment.singleton⟩

def edmundsPeriodTwoCanonicalSegments
    (blocks : List EdmundsPeriodTwoBlock) :
    List EdmundsPeriodTwoSegment :=
  (edmundsPeriodTwoBlocksToSegments blocks).map
    edmundsPeriodTwoSortSegment

def edmundsPeriodTwoCanonicalBlocks
    (blocks : List EdmundsPeriodTwoBlock) :
    List EdmundsPeriodTwoBlock :=
  edmundsPeriodTwoSegmentsToBlocks
    (edmundsPeriodTwoCanonicalSegments blocks)

def edmundsPeriodTwoCanonicalSegmentsOfNormalList
    (xs : List Nat) : List EdmundsPeriodTwoSegment :=
  edmundsPeriodTwoCanonicalSegments
    (edmundsPeriodTwoBlocksOfNormalList xs)

def edmundsPeriodTwoCanonicalRender
    (xs : List Nat) : List Nat :=
  renderEdmundsPeriodTwoSegments
    (edmundsPeriodTwoCanonicalSegmentsOfNormalList xs)

theorem edmundsPeriodTwoSortRepeated_perm
    (blocks : List EdmundsPeriodTwoRepeatedBlock) :
    (edmundsPeriodTwoSortRepeated blocks).Perm blocks := by
  exact List.mergeSort_perm _ _

theorem edmundsPeriodTwoSortRepeated_sorted
    (blocks : List EdmundsPeriodTwoRepeatedBlock) :
    ((edmundsPeriodTwoSortRepeated blocks).map
      EdmundsPeriodTwoRepeatedBlock.label).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ a b c : EdmundsPeriodTwoRepeatedBlock,
        decide (a.label ≤ b.label) = true →
        decide (b.label ≤ c.label) = true →
        decide (a.label ≤ c.label) = true := by
    intro a b c hab hbc
    exact decide_eq_true
      (Nat.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  have total :
      ∀ a b : EdmundsPeriodTwoRepeatedBlock,
        (decide (a.label ≤ b.label) ||
          decide (b.label ≤ a.label)) = true := by
    intro a b
    rcases Nat.le_total a.label b.label with hab | hba
    · simp [hab]
    · simp [hba]
  have sortedBlocks :=
    List.pairwise_mergeSort transitive total blocks
  simpa [edmundsPeriodTwoSortRepeated, List.pairwise_map] using
    (sortedBlocks.imp fun relation => of_decide_eq_true relation)

private theorem render_blocks_append
    (left right : List EdmundsPeriodTwoBlock) :
    renderEdmundsPeriodTwoBlocks (left ++ right) =
      renderEdmundsPeriodTwoBlocks left ++
        renderEdmundsPeriodTwoBlocks right := by
  simp [renderEdmundsPeriodTwoBlocks, List.flatMap_append]

private theorem render_repeated_toBlocks
    (blocks : List EdmundsPeriodTwoRepeatedBlock) :
    renderEdmundsPeriodTwoBlocks
        (blocks.map EdmundsPeriodTwoRepeatedBlock.toBlock) =
      renderEdmundsPeriodTwoRepeatedBlocks blocks := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      cases block <;>
        simpa [renderEdmundsPeriodTwoBlocks,
          renderEdmundsPeriodTwoRepeatedBlocks,
          EdmundsPeriodTwoRepeatedBlock.render,
          EdmundsPeriodTwoRepeatedBlock.toBlock] using ih

theorem render_edmundsPeriodTwoSegmentToBlocks
    (segment : EdmundsPeriodTwoSegment) :
    renderEdmundsPeriodTwoBlocks
        (edmundsPeriodTwoSegmentToBlocks segment) =
      segment.render := by
  cases segment with
  | mk repeated singleton =>
      cases singleton with
      | none =>
          simpa [edmundsPeriodTwoSegmentToBlocks,
            EdmundsPeriodTwoSegment.toBlocks,
            EdmundsPeriodTwoSegment.render] using
              render_repeated_toBlocks repeated
      | some x =>
          rw [show
            edmundsPeriodTwoSegmentToBlocks
                { repeated := repeated, singleton := some x } =
              repeated.map EdmundsPeriodTwoRepeatedBlock.toBlock ++
                [EdmundsPeriodTwoBlock.single x] by
              rfl]
          rw [render_blocks_append, render_repeated_toBlocks]
          rfl

theorem render_edmundsPeriodTwoSegmentsToBlocks
    (segments : List EdmundsPeriodTwoSegment) :
    renderEdmundsPeriodTwoBlocks
        (edmundsPeriodTwoSegmentsToBlocks segments) =
      renderEdmundsPeriodTwoSegments segments := by
  induction segments with
  | nil => rfl
  | cons segment rest ih =>
      simp only [edmundsPeriodTwoSegmentsToBlocks,
        List.flatMap_cons, renderEdmundsPeriodTwoSegments,
        List.flatMap_cons]
      rw [render_blocks_append,
        render_edmundsPeriodTwoSegmentToBlocks]
      simpa [edmundsPeriodTwoSegmentsToBlocks,
        renderEdmundsPeriodTwoSegments] using
          congrArg (List.append segment.render) ih

theorem renderEdmundsPeriodTwoSegments_append
    (left right : List EdmundsPeriodTwoSegment) :
    renderEdmundsPeriodTwoSegments (left ++ right) =
      renderEdmundsPeriodTwoSegments left ++
        renderEdmundsPeriodTwoSegments right := by
  simp [renderEdmundsPeriodTwoSegments, List.flatMap_append]

theorem edmundsPeriodTwoCanonicalSegmentsDerive :
    ∀ segments : List EdmundsPeriodTwoSegment,
      EdmundsPeriodTwoBlocksListDerives
        (renderEdmundsPeriodTwoSegments segments)
        (renderEdmundsPeriodTwoSegments
          (segments.map edmundsPeriodTwoSortSegment))
  | [] => .empty
  | segment :: rest => by
      have runDerives :
          EdmundsPeriodTwoBlocksListDerives
            (renderEdmundsPeriodTwoRepeatedBlocks segment.repeated)
            (renderEdmundsPeriodTwoRepeatedBlocks
              (edmundsPeriodTwoSortRepeated segment.repeated)) :=
        edmundsPeriodTwoBlocksDerivesRepeatedBlockPermutation
          (edmundsPeriodTwoSortRepeated_perm segment.repeated).symm
      have segmentDerives :
          EdmundsPeriodTwoBlocksListDerives segment.render
            (edmundsPeriodTwoSortSegment segment).render := by
        simpa [EdmundsPeriodTwoSegment.render,
          edmundsPeriodTwoSortSegment] using
            runDerives.append segment.singleton.toList
      have firstStep :=
        segmentDerives.append
          (renderEdmundsPeriodTwoSegments rest)
      have restStep :=
        (edmundsPeriodTwoCanonicalSegmentsDerive rest).prepend
          (edmundsPeriodTwoSortSegment segment).render
      simpa only [renderEdmundsPeriodTwoSegments,
        List.flatMap_cons, List.map_cons] using
          firstStep.trans restStep

theorem edmundsPeriodTwoCanonicalBlocksDerive
    (blocks : List EdmundsPeriodTwoBlock) :
    EdmundsPeriodTwoBlocksListDerives
      (renderEdmundsPeriodTwoBlocks blocks)
      (renderEdmundsPeriodTwoBlocks
        (edmundsPeriodTwoCanonicalBlocks blocks)) := by
  have derivation :=
    edmundsPeriodTwoCanonicalSegmentsDerive
      (edmundsPeriodTwoBlocksToSegments blocks)
  rw [← render_edmundsPeriodTwoSegmentsToBlocks,
    ← render_edmundsPeriodTwoSegmentsToBlocks] at derivation
  simpa [edmundsPeriodTwoCanonicalBlocks,
    edmundsPeriodTwoCanonicalSegments,
    edmundsPeriodTwoSegments_blocks_roundtrip] using derivation

/-- Structural canonicalization of a normal flat list is an actual
derivation in the Edmunds basis, not merely a permutation calculation. -/
theorem edmundsPeriodTwoCanonicalDerivation
    {xs : List Nat} (normal : EdmundsPeriodTwoBlocksNormal xs) :
    EdmundsPeriodTwoBlocksListDerives xs
      (edmundsPeriodTwoCanonicalRender xs) := by
  have derivation :=
    edmundsPeriodTwoCanonicalSegmentsDerive
      (edmundsPeriodTwoBlocksToSegments
        (edmundsPeriodTwoBlocksOfNormalList xs))
  have sourceRender :=
    render_edmundsPeriodTwoBlocksOfNormalList normal
  rw [← render_edmundsPeriodTwoSegmentsToBlocks] at derivation
  rw [edmundsPeriodTwoSegments_blocks_roundtrip,
    sourceRender] at derivation
  simpa [edmundsPeriodTwoCanonicalRender,
    edmundsPeriodTwoCanonicalSegmentsOfNormalList,
    edmundsPeriodTwoCanonicalSegments] using derivation

/-- Structural invariants of the deterministic segmented normal form. -/
def SegmentsCanonical
    (segments : List EdmundsPeriodTwoSegment) : Prop :=
  (allEdmundsPeriodTwoSegmentLabels segments).Nodup ∧
    (∀ segment, segment ∈ segments →
      (segment.repeated.map
        EdmundsPeriodTwoRepeatedBlock.label).Pairwise (· ≤ ·)) ∧
    (∀ before segment rest,
      segments = before ++ segment :: rest →
      segment.singleton = none → rest = []) ∧
    (∀ segment, segment ∈ segments →
      segment.repeated = [] → segment.singleton.isSome)

private theorem labels_segments_roundtrip
    (blocks : List EdmundsPeriodTwoBlock) :
    allEdmundsPeriodTwoSegmentLabels
        (edmundsPeriodTwoBlocksToSegments blocks) =
      blocks.map EdmundsPeriodTwoBlock.label := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
      cases block with
      | single x =>
          simp only [edmundsPeriodTwoBlocksToSegments,
            allEdmundsPeriodTwoSegmentLabels, List.flatMap_cons,
            EdmundsPeriodTwoSegment.labels, List.map_nil,
            List.nil_append, Option.toList_some,
            List.singleton_append, List.map_cons,
            EdmundsPeriodTwoBlock.label]
          simpa using congrArg (List.cons x) ih
      | double x =>
          cases h : edmundsPeriodTwoBlocksToSegments blocks with
          | nil =>
              have blocksEmpty : blocks = [] := by
                have roundtrip :=
                  edmundsPeriodTwoSegments_blocks_roundtrip blocks
                rw [h] at roundtrip
                simpa [edmundsPeriodTwoSegmentsToBlocks] using
                  roundtrip.symm
              subst blocks
              rfl
          | cons segment rest =>
              have ih' := ih
              rw [h] at ih'
              simp [edmundsPeriodTwoBlocksToSegments, h,
                allEdmundsPeriodTwoSegmentLabels,
                EdmundsPeriodTwoSegment.labels,
                EdmundsPeriodTwoRepeatedBlock.label,
                EdmundsPeriodTwoRepeatedBlock.toBlock,
                EdmundsPeriodTwoBlock.label] at ih' ⊢
              exact ih'
      | triple x =>
          cases h : edmundsPeriodTwoBlocksToSegments blocks with
          | nil =>
              have blocksEmpty : blocks = [] := by
                have roundtrip :=
                  edmundsPeriodTwoSegments_blocks_roundtrip blocks
                rw [h] at roundtrip
                simpa [edmundsPeriodTwoSegmentsToBlocks] using
                  roundtrip.symm
              subst blocks
              rfl
          | cons segment rest =>
              have ih' := ih
              rw [h] at ih'
              simp [edmundsPeriodTwoBlocksToSegments, h,
                allEdmundsPeriodTwoSegmentLabels,
                EdmundsPeriodTwoSegment.labels,
                EdmundsPeriodTwoRepeatedBlock.label,
                EdmundsPeriodTwoRepeatedBlock.toBlock,
                EdmundsPeriodTwoBlock.label] at ih' ⊢
              exact ih'

private theorem sorted_segment_labels_perm
    (segment : EdmundsPeriodTwoSegment) :
    (edmundsPeriodTwoSortSegment segment).labels.Perm
      segment.labels := by
  apply List.Perm.append
  · exact
      (edmundsPeriodTwoSortRepeated_perm segment.repeated).map
        EdmundsPeriodTwoRepeatedBlock.label
  · exact List.Perm.refl _

private theorem sorted_all_labels_perm :
    ∀ segments : List EdmundsPeriodTwoSegment,
      (allEdmundsPeriodTwoSegmentLabels
          (segments.map edmundsPeriodTwoSortSegment)).Perm
        (allEdmundsPeriodTwoSegmentLabels segments)
  | [] => List.Perm.nil
  | segment :: rest => by
      simp only [List.map_cons,
        allEdmundsPeriodTwoSegmentLabels, List.flatMap_cons]
      exact List.Perm.append
        (sorted_segment_labels_perm segment)
        (sorted_all_labels_perm rest)

private theorem blocksToSegments_first_none_tail :
    ∀ (blocks : List EdmundsPeriodTwoBlock)
      (segment : EdmundsPeriodTwoSegment)
      (rest : List EdmundsPeriodTwoSegment),
      edmundsPeriodTwoBlocksToSegments blocks = segment :: rest →
      segment.singleton = none →
      rest = []
  | [], _, _, h, _ => by
      simp [edmundsPeriodTwoBlocksToSegments] at h
  | .single x :: blocks, segment, rest, h, hnone => by
      simp only [edmundsPeriodTwoBlocksToSegments] at h
      injection h with headEq
      subst segment
      simp at hnone
  | .double x :: blocks, segment, rest, h, hnone => by
      cases ht : edmundsPeriodTwoBlocksToSegments blocks with
      | nil =>
          simp [edmundsPeriodTwoBlocksToSegments, ht] at h
          exact h.2
      | cons next more =>
          simp only [edmundsPeriodTwoBlocksToSegments, ht] at h
          injection h with headEq tailEq
          subst segment rest
          exact blocksToSegments_first_none_tail
            blocks next more ht hnone
  | .triple x :: blocks, segment, rest, h, hnone => by
      cases ht : edmundsPeriodTwoBlocksToSegments blocks with
      | nil =>
          simp [edmundsPeriodTwoBlocksToSegments, ht] at h
          exact h.2
      | cons next more =>
          simp only [edmundsPeriodTwoBlocksToSegments, ht] at h
          injection h with headEq tailEq
          subst segment rest
          exact blocksToSegments_first_none_tail
            blocks next more ht hnone

private theorem blocksToSegments_none_terminal :
    ∀ (blocks : List EdmundsPeriodTwoBlock)
      (before : List EdmundsPeriodTwoSegment)
      (segment : EdmundsPeriodTwoSegment)
      (rest : List EdmundsPeriodTwoSegment),
      edmundsPeriodTwoBlocksToSegments blocks =
        before ++ segment :: rest →
      segment.singleton = none →
      rest = []
  | [], _, _, _, h, _ => by
      simp [edmundsPeriodTwoBlocksToSegments] at h
  | .single x :: blocks, before, segment, rest, h, hnone => by
      cases before with
      | nil =>
          simp only [edmundsPeriodTwoBlocksToSegments,
            List.nil_append] at h
          injection h with headEq
          subst segment
          simp at hnone
      | cons first more =>
          simp only [edmundsPeriodTwoBlocksToSegments,
            List.cons_append] at h
          injection h with _ tailEq
          exact blocksToSegments_none_terminal
            blocks more segment rest tailEq hnone
  | .double x :: blocks, before, segment, rest, h, hnone => by
      cases ht : edmundsPeriodTwoBlocksToSegments blocks with
      | nil =>
          have blocksEmpty : blocks = [] := by
            have roundtrip :=
              edmundsPeriodTwoSegments_blocks_roundtrip blocks
            rw [ht] at roundtrip
            simpa [edmundsPeriodTwoSegmentsToBlocks] using
              roundtrip.symm
          subst blocks
          simp only [edmundsPeriodTwoBlocksToSegments] at h
          cases before with
          | nil =>
              simpa using congrArg List.tail h
          | cons first more =>
              simp at h
      | cons next more =>
          cases before with
          | nil =>
              simp only [edmundsPeriodTwoBlocksToSegments, ht,
                List.nil_append] at h
              injection h with headEq tailEq
              subst segment rest
              exact blocksToSegments_first_none_tail
                blocks next more ht hnone
          | cons first beforeTail =>
              simp only [edmundsPeriodTwoBlocksToSegments, ht,
                List.cons_append] at h
              injection h with _ tailEq
              exact blocksToSegments_none_terminal
                blocks (next :: beforeTail) segment rest
                  (by
                    simpa [ht] using
                      congrArg (List.cons next) tailEq)
                  hnone
  | .triple x :: blocks, before, segment, rest, h, hnone => by
      cases ht : edmundsPeriodTwoBlocksToSegments blocks with
      | nil =>
          have blocksEmpty : blocks = [] := by
            have roundtrip :=
              edmundsPeriodTwoSegments_blocks_roundtrip blocks
            rw [ht] at roundtrip
            simpa [edmundsPeriodTwoSegmentsToBlocks] using
              roundtrip.symm
          subst blocks
          simp only [edmundsPeriodTwoBlocksToSegments] at h
          cases before with
          | nil =>
              simpa using congrArg List.tail h
          | cons first more =>
              simp at h
      | cons next more =>
          cases before with
          | nil =>
              simp only [edmundsPeriodTwoBlocksToSegments, ht,
                List.nil_append] at h
              injection h with headEq tailEq
              subst segment rest
              exact blocksToSegments_first_none_tail
                blocks next more ht hnone
          | cons first beforeTail =>
              simp only [edmundsPeriodTwoBlocksToSegments, ht,
                List.cons_append] at h
              injection h with _ tailEq
              exact blocksToSegments_none_terminal
                blocks (next :: beforeTail) segment rest
                  (by
                    simpa [ht] using
                      congrArg (List.cons next) tailEq)
                  hnone

private theorem blocksToSegments_empty_run_some :
    ∀ (blocks : List EdmundsPeriodTwoBlock)
      (segment : EdmundsPeriodTwoSegment),
      segment ∈ edmundsPeriodTwoBlocksToSegments blocks →
      segment.repeated = [] →
      segment.singleton.isSome
  | [], _, h, _ => by
      simp [edmundsPeriodTwoBlocksToSegments] at h
  | .single x :: blocks, segment, h, hempty => by
      simp only [edmundsPeriodTwoBlocksToSegments,
        List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact blocksToSegments_empty_run_some
          blocks segment h hempty
  | .double x :: blocks, segment, h, hempty => by
      cases ht : edmundsPeriodTwoBlocksToSegments blocks with
      | nil =>
          simp [edmundsPeriodTwoBlocksToSegments, ht] at h
          subst segment
          contradiction
      | cons next more =>
          simp only [edmundsPeriodTwoBlocksToSegments, ht,
            List.mem_cons] at h
          rcases h with rfl | h
          · contradiction
          · exact blocksToSegments_empty_run_some
              blocks segment
                (by
                  rw [ht]
                  exact List.Mem.tail next h)
                hempty
  | .triple x :: blocks, segment, h, hempty => by
      cases ht : edmundsPeriodTwoBlocksToSegments blocks with
      | nil =>
          simp [edmundsPeriodTwoBlocksToSegments, ht] at h
          subst segment
          contradiction
      | cons next more =>
          simp only [edmundsPeriodTwoBlocksToSegments, ht,
            List.mem_cons] at h
          rcases h with rfl | h
          · contradiction
          · exact blocksToSegments_empty_run_some
              blocks segment
                (by
                  rw [ht]
                  exact List.Mem.tail next h)
                hempty

/-- Canonical segments obtained from any normal list satisfy the public
structural invariant. -/
theorem edmundsPeriodTwoCanonicalSegments_canonical
    {xs : List Nat} (normal : EdmundsPeriodTwoBlocksNormal xs) :
    SegmentsCanonical
      (edmundsPeriodTwoCanonicalSegmentsOfNormalList xs) := by
  let blocks := edmundsPeriodTwoBlocksOfNormalList xs
  let segments := edmundsPeriodTwoBlocksToSegments blocks
  have labelsNodup :
      (blocks.map EdmundsPeriodTwoBlock.label).Nodup :=
    normal_blocks_labels_nodup normal
  have segmentLabelsNodup :
      (allEdmundsPeriodTwoSegmentLabels segments).Nodup := by
    rw [labels_segments_roundtrip]
    exact labelsNodup
  change SegmentsCanonical
    (segments.map edmundsPeriodTwoSortSegment)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (sorted_all_labels_perm segments).symm.nodup
      segmentLabelsNodup
  · intro segment hsegment
    rcases List.mem_map.mp hsegment with ⟨source, _, rfl⟩
    exact edmundsPeriodTwoSortRepeated_sorted source.repeated
  · intro before segment rest heq hnone
    have beforeSources :
        ∃ sourceBefore source sourceRest,
          before =
              sourceBefore.map edmundsPeriodTwoSortSegment ∧
          segment = edmundsPeriodTwoSortSegment source ∧
          rest = sourceRest.map edmundsPeriodTwoSortSegment ∧
          segments = sourceBefore ++ source :: sourceRest := by
      have split := List.map_eq_append_iff.mp heq
      rcases split with ⟨sourceBefore, sourceTail,
        sourceBeforeEq, sourceTailEq⟩
      rcases sourceTailEq with ⟨beforeEq, tailMapEq⟩
      cases sourceTail with
      | nil =>
          simp at tailMapEq
      | cons source sourceRest =>
          simp only [List.map_cons] at tailMapEq
          injection tailMapEq with segmentEq restEq
          exact ⟨sourceBefore, source, sourceRest,
            beforeEq.symm, segmentEq.symm, restEq.symm,
            by simpa using sourceBeforeEq⟩
    rcases beforeSources with
      ⟨sourceBefore, source, sourceRest, rfl, rfl, rfl,
        sourceSplit⟩
    have sourceNone : source.singleton = none := by
      simpa [edmundsPeriodTwoSortSegment] using hnone
    have sourceRestEmpty :=
      blocksToSegments_none_terminal
        blocks sourceBefore source sourceRest sourceSplit sourceNone
    subst sourceRest
    rfl
  · intro segment hsegment hrepeated
    rcases List.mem_map.mp hsegment with ⟨source, sourceMem, rfl⟩
    have sourceRepeatedEmpty : source.repeated = [] := by
      have permutation :=
        edmundsPeriodTwoSortRepeated_perm source.repeated
      have sortedEmpty :
          edmundsPeriodTwoSortRepeated source.repeated = [] :=
        hrepeated
      rw [sortedEmpty] at permutation
      exact permutation.nil_eq.symm
    simpa [edmundsPeriodTwoSortSegment] using
      blocksToSegments_empty_run_some blocks source
        sourceMem sourceRepeatedEmpty

theorem edmundsPeriodTwoTailCanonical
    {segment : EdmundsPeriodTwoSegment}
    {rest : List EdmundsPeriodTwoSegment}
    (canonical : SegmentsCanonical (segment :: rest)) :
    SegmentsCanonical rest := by
  have nodupAppend :
      (segment.labels ++
        allEdmundsPeriodTwoSegmentLabels rest).Nodup := by
    simpa [allEdmundsPeriodTwoSegmentLabels] using canonical.1
  refine ⟨(List.nodup_append.mp nodupAppend).2.1, ?_, ?_, ?_⟩
  · intro candidate hcandidate
    exact canonical.2.1 candidate
      (List.Mem.tail segment hcandidate)
  · intro before candidate tail heq hnone
    exact canonical.2.2.1
      (segment :: before) candidate tail
      (by simp [heq]) hnone
  · intro candidate hcandidate hempty
    exact canonical.2.2.2 candidate
      (List.Mem.tail segment hcandidate) hempty

theorem edmundsPeriodTwoFirstSegmentDisjoint
    {segment : EdmundsPeriodTwoSegment}
    {rest : List EdmundsPeriodTwoSegment}
    (canonical : SegmentsCanonical (segment :: rest)) :
    ∀ z, z ∈ segment.labels →
      z ∉ allEdmundsPeriodTwoSegmentLabels rest := by
  have nodupAppend :
      (segment.labels ++
        allEdmundsPeriodTwoSegmentLabels rest).Nodup := by
    simpa [allEdmundsPeriodTwoSegmentLabels] using canonical.1
  exact fun z hz hrest =>
    (List.nodup_append.mp nodupAppend).2.2 z hz z hrest rfl

theorem mem_renderEdmundsPeriodTwoSegments_allLabels
    (z : Nat) :
    ∀ {segments : List EdmundsPeriodTwoSegment},
      z ∈ renderEdmundsPeriodTwoSegments segments →
      z ∈ allEdmundsPeriodTwoSegmentLabels segments
  | [], h => by
      simp [renderEdmundsPeriodTwoSegments] at h
  | segment :: rest, h => by
      simp only [renderEdmundsPeriodTwoSegments,
        List.flatMap_cons, allEdmundsPeriodTwoSegmentLabels,
        List.mem_append] at h ⊢
      rcases h with h | h
      · left
        cases segment with
        | mk repeated singleton =>
            simp only [EdmundsPeriodTwoSegment.render,
              EdmundsPeriodTwoSegment.labels,
              List.mem_append] at h ⊢
            rcases h with h | h
            · left
              rcases List.mem_flatMap.mp h with
                ⟨block, blockMem, labelMem⟩
              have labelEq :
                  z = block.label := by
                cases block with
                | double x =>
                    simpa [EdmundsPeriodTwoRepeatedBlock.render,
                      EdmundsPeriodTwoRepeatedBlock.toBlock,
                      EdmundsPeriodTwoBlock.render,
                      EdmundsPeriodTwoRepeatedBlock.label,
                      EdmundsPeriodTwoBlock.label] using labelMem
                | triple x =>
                    simpa [EdmundsPeriodTwoRepeatedBlock.render,
                      EdmundsPeriodTwoRepeatedBlock.toBlock,
                      EdmundsPeriodTwoBlock.render,
                      EdmundsPeriodTwoRepeatedBlock.label,
                      EdmundsPeriodTwoBlock.label] using labelMem
              exact List.mem_map.mpr
                ⟨block, blockMem, labelEq.symm⟩
            · exact Or.inr h
      · exact Or.inr
          (mem_renderEdmundsPeriodTwoSegments_allLabels z h)

private theorem count_renderEdmundsPeriodTwoRepeatedBlocks
    (z : Nat) :
    ∀ blocks : List EdmundsPeriodTwoRepeatedBlock,
      (renderEdmundsPeriodTwoRepeatedBlocks blocks).count z =
        2 * (doubleLabelsOfRepeated blocks).count z +
          3 * (tripleLabelsOfRepeated blocks).count z
  | [] => by
      simp [renderEdmundsPeriodTwoRepeatedBlocks,
        doubleLabelsOfRepeated, tripleLabelsOfRepeated]
  | .double x :: rest => by
      rw [show
        renderEdmundsPeriodTwoRepeatedBlocks (.double x :: rest) =
          [x, x] ++ renderEdmundsPeriodTwoRepeatedBlocks rest by
            rfl]
      rw [List.count_append,
        count_renderEdmundsPeriodTwoRepeatedBlocks z rest]
      by_cases hx : x = z
      · subst x
        simp [doubleLabelsOfRepeated, tripleLabelsOfRepeated]
        omega
      · simp [doubleLabelsOfRepeated, tripleLabelsOfRepeated, hx]
  | .triple x :: rest => by
      rw [show
        renderEdmundsPeriodTwoRepeatedBlocks (.triple x :: rest) =
          [x, x, x] ++ renderEdmundsPeriodTwoRepeatedBlocks rest by
            rfl]
      rw [List.count_append,
        count_renderEdmundsPeriodTwoRepeatedBlocks z rest]
      by_cases hx : x = z
      · subst x
        simp [doubleLabelsOfRepeated, tripleLabelsOfRepeated]
        omega
      · simp [doubleLabelsOfRepeated, tripleLabelsOfRepeated, hx]

private theorem count_repeated_labels
    (z : Nat) :
    ∀ blocks : List EdmundsPeriodTwoRepeatedBlock,
      (blocks.map EdmundsPeriodTwoRepeatedBlock.label).count z =
        (doubleLabelsOfRepeated blocks).count z +
          (tripleLabelsOfRepeated blocks).count z
  | [] => by
      simp [doubleLabelsOfRepeated, tripleLabelsOfRepeated]
  | .double x :: rest => by
      rw [show
        ((EdmundsPeriodTwoRepeatedBlock.double x :: rest).map
          EdmundsPeriodTwoRepeatedBlock.label).count z =
            (x :: rest.map
              EdmundsPeriodTwoRepeatedBlock.label).count z by
                rfl]
      rw [List.count_cons, count_repeated_labels z rest]
      by_cases hx : x = z
      · subst x
        simp [doubleLabelsOfRepeated, tripleLabelsOfRepeated]
        omega
      · simp [doubleLabelsOfRepeated, tripleLabelsOfRepeated, hx]
  | .triple x :: rest => by
      rw [show
        ((EdmundsPeriodTwoRepeatedBlock.triple x :: rest).map
          EdmundsPeriodTwoRepeatedBlock.label).count z =
            (x :: rest.map
              EdmundsPeriodTwoRepeatedBlock.label).count z by
                rfl]
      rw [List.count_cons, count_repeated_labels z rest]
      by_cases hx : x = z
      · subst x
        simp [doubleLabelsOfRepeated, tripleLabelsOfRepeated]
        omega
      · simp [doubleLabelsOfRepeated, tripleLabelsOfRepeated, hx]

/-- Exact count decomposition of a rendered segmented word into double,
triple, and singleton labels. -/
theorem count_renderEdmundsPeriodTwoSegments
    (z : Nat) :
    ∀ segments : List EdmundsPeriodTwoSegment,
      (renderEdmundsPeriodTwoSegments segments).count z =
        2 * (edmundsPeriodTwoDoubleLabels segments).count z +
          3 * (edmundsPeriodTwoTripleLabels segments).count z +
            (edmundsPeriodTwoSingletonLabels segments).count z
  | [] => by
      simp [renderEdmundsPeriodTwoSegments,
        edmundsPeriodTwoDoubleLabels,
        edmundsPeriodTwoTripleLabels,
        edmundsPeriodTwoSingletonLabels,
        allEdmundsPeriodTwoRepeatedBlocks,
        doubleLabelsOfRepeated, tripleLabelsOfRepeated]
  | segment :: rest => by
      rw [show
        renderEdmundsPeriodTwoSegments (segment :: rest) =
          segment.render ++
            renderEdmundsPeriodTwoSegments rest by
              rfl]
      rw [List.count_append,
        count_renderEdmundsPeriodTwoSegments z rest]
      cases segment with
      | mk repeated singleton =>
          cases singleton with
          | none =>
              rw [show
                ({ repeated := repeated, singleton := none } :
                  EdmundsPeriodTwoSegment).render =
                    renderEdmundsPeriodTwoRepeatedBlocks repeated by
                      simp [EdmundsPeriodTwoSegment.render]]
              rw [count_renderEdmundsPeriodTwoRepeatedBlocks]
              simp [edmundsPeriodTwoDoubleLabels,
                edmundsPeriodTwoTripleLabels,
                edmundsPeriodTwoSingletonLabels,
                allEdmundsPeriodTwoRepeatedBlocks,
                doubleLabelsOfRepeated, tripleLabelsOfRepeated,
                List.count_append]
              omega
          | some x =>
              rw [show
                ({ repeated := repeated, singleton := some x } :
                  EdmundsPeriodTwoSegment).render =
                    renderEdmundsPeriodTwoRepeatedBlocks repeated ++
                      [x] by
                        rfl]
              rw [List.count_append,
                count_renderEdmundsPeriodTwoRepeatedBlocks]
              simp [edmundsPeriodTwoDoubleLabels,
                edmundsPeriodTwoTripleLabels,
                edmundsPeriodTwoSingletonLabels,
                allEdmundsPeriodTwoRepeatedBlocks,
                doubleLabelsOfRepeated, tripleLabelsOfRepeated,
                List.count_append]
              simp only [List.count_cons, List.count_nil, Nat.zero_add]
              omega

private theorem count_allEdmundsPeriodTwoSegmentLabels
    (z : Nat) :
    ∀ segments : List EdmundsPeriodTwoSegment,
      (allEdmundsPeriodTwoSegmentLabels segments).count z =
        (edmundsPeriodTwoDoubleLabels segments).count z +
          (edmundsPeriodTwoTripleLabels segments).count z +
            (edmundsPeriodTwoSingletonLabels segments).count z
  | [] => by
      simp [allEdmundsPeriodTwoSegmentLabels,
        edmundsPeriodTwoDoubleLabels,
        edmundsPeriodTwoTripleLabels,
        edmundsPeriodTwoSingletonLabels,
        allEdmundsPeriodTwoRepeatedBlocks,
        doubleLabelsOfRepeated, tripleLabelsOfRepeated]
  | segment :: rest => by
      rw [show
        allEdmundsPeriodTwoSegmentLabels (segment :: rest) =
          segment.labels ++
            allEdmundsPeriodTwoSegmentLabels rest by
              rfl]
      rw [List.count_append,
        count_allEdmundsPeriodTwoSegmentLabels z rest]
      cases segment with
      | mk repeated singleton =>
          cases singleton with
          | none =>
              rw [show
                ({ repeated := repeated, singleton := none } :
                  EdmundsPeriodTwoSegment).labels =
                    repeated.map
                      EdmundsPeriodTwoRepeatedBlock.label by
                        simp [EdmundsPeriodTwoSegment.labels]]
              rw [count_repeated_labels]
              simp [edmundsPeriodTwoDoubleLabels,
                edmundsPeriodTwoTripleLabels,
                edmundsPeriodTwoSingletonLabels,
                allEdmundsPeriodTwoRepeatedBlocks,
                doubleLabelsOfRepeated, tripleLabelsOfRepeated,
                List.count_append]
              omega
          | some x =>
              rw [show
                ({ repeated := repeated, singleton := some x } :
                  EdmundsPeriodTwoSegment).labels =
                    repeated.map
                      EdmundsPeriodTwoRepeatedBlock.label ++ [x] by
                        rfl]
              rw [List.count_append, count_repeated_labels]
              simp [edmundsPeriodTwoDoubleLabels,
                edmundsPeriodTwoTripleLabels,
                edmundsPeriodTwoSingletonLabels,
                allEdmundsPeriodTwoRepeatedBlocks,
                doubleLabelsOfRepeated, tripleLabelsOfRepeated,
                List.count_append]
              simp only [List.count_cons, List.count_nil, Nat.zero_add]
              omega

/-- In a canonical segmented word, a label contributes exactly two, three,
one, or zero letters according as it is a double-block label, a triple-block
label, a singleton label, or absent. -/
theorem renderEdmundsPeriodTwoSegments_count_classification
    {segments : List EdmundsPeriodTwoSegment}
    (canonical : SegmentsCanonical segments) (z : Nat) :
    (renderEdmundsPeriodTwoSegments segments).count z =
      if z ∈ edmundsPeriodTwoDoubleLabels segments then 2
      else if z ∈ edmundsPeriodTwoTripleLabels segments then 3
      else if z ∈ edmundsPeriodTwoSingletonLabels segments then 1
      else 0 := by
  let doubleLabels := edmundsPeriodTwoDoubleLabels segments
  let tripleLabels := edmundsPeriodTwoTripleLabels segments
  let singletonLabels := edmundsPeriodTwoSingletonLabels segments
  have renderCount :
      (renderEdmundsPeriodTwoSegments segments).count z =
        2 * doubleLabels.count z +
          3 * tripleLabels.count z + singletonLabels.count z := by
    simpa [doubleLabels, tripleLabels, singletonLabels] using
      count_renderEdmundsPeriodTwoSegments z segments
  have labelCount :
      (allEdmundsPeriodTwoSegmentLabels segments).count z =
        doubleLabels.count z + tripleLabels.count z +
          singletonLabels.count z := by
    simpa [doubleLabels, tripleLabels, singletonLabels] using
      count_allEdmundsPeriodTwoSegmentLabels z segments
  have atMostOne :
      doubleLabels.count z + tripleLabels.count z +
          singletonLabels.count z ≤ 1 := by
    rw [← labelCount, canonical.1.count]
    split <;> omega
  by_cases hd : z ∈ doubleLabels
  · have hdpos : 0 < doubleLabels.count z :=
      List.count_pos_iff.mpr hd
    have hd1 : doubleLabels.count z = 1 := by omega
    have ht0 : tripleLabels.count z = 0 := by omega
    have hs0 : singletonLabels.count z = 0 := by omega
    rw [renderCount]
    simp [doubleLabels, tripleLabels, singletonLabels, hd,
      hd1, ht0, hs0]
  · have hd0 : doubleLabels.count z = 0 :=
      List.count_eq_zero.mpr hd
    by_cases ht : z ∈ tripleLabels
    · have htpos : 0 < tripleLabels.count z :=
        List.count_pos_iff.mpr ht
      have ht1 : tripleLabels.count z = 1 := by omega
      have hs0 : singletonLabels.count z = 0 := by omega
      rw [renderCount]
      simp [doubleLabels, tripleLabels, singletonLabels, hd, ht,
        hd0, ht1, hs0]
    · have ht0 : tripleLabels.count z = 0 :=
        List.count_eq_zero.mpr ht
      by_cases hs : z ∈ singletonLabels
      · have hspos : 0 < singletonLabels.count z :=
          List.count_pos_iff.mpr hs
        have hs1 : singletonLabels.count z = 1 := by omega
        rw [renderCount]
        simp [doubleLabels, tripleLabels, singletonLabels, hd, ht, hs,
          hd0, ht0, hs1]
      · have hs0 : singletonLabels.count z = 0 :=
          List.count_eq_zero.mpr hs
        rw [renderCount]
        simp [doubleLabels, tripleLabels, singletonLabels, hd, ht, hs,
          hd0, ht0, hs0]

/-- Every label occurs at most three times in a canonical rendering. -/
theorem renderEdmundsPeriodTwoSegments_count_le_three
    {segments : List EdmundsPeriodTwoSegment}
    (canonical : SegmentsCanonical segments) (z : Nat) :
    (renderEdmundsPeriodTwoSegments segments).count z ≤ 3 := by
  rw [renderEdmundsPeriodTwoSegments_count_classification canonical z]
  by_cases hd : z ∈ edmundsPeriodTwoDoubleLabels segments
  · simp [hd]
  · by_cases ht : z ∈ edmundsPeriodTwoTripleLabels segments
    · simp [hd, ht]
    · by_cases hs : z ∈ edmundsPeriodTwoSingletonLabels segments
      · simp [hd, ht, hs]
      · simp [hd, ht, hs]

/-- Singleton labels are exactly the labels of rendered multiplicity one. -/
theorem mem_edmundsPeriodTwoSingletonLabels_iff_count_one
    {segments : List EdmundsPeriodTwoSegment}
    (canonical : SegmentsCanonical segments) (z : Nat) :
    z ∈ edmundsPeriodTwoSingletonLabels segments ↔
      (renderEdmundsPeriodTwoSegments segments).count z = 1 := by
  rw [renderEdmundsPeriodTwoSegments_count_classification canonical z]
  by_cases hd : z ∈ edmundsPeriodTwoDoubleLabels segments
  · have hs :
        z ∉ edmundsPeriodTwoSingletonLabels segments := by
      intro hs
      have hdpos :
          0 < (edmundsPeriodTwoDoubleLabels segments).count z :=
        List.count_pos_iff.mpr hd
      have hspos :
          0 < (edmundsPeriodTwoSingletonLabels segments).count z :=
        List.count_pos_iff.mpr hs
      have labelCount :=
        count_allEdmundsPeriodTwoSegmentLabels z segments
      have atMostOne :
          (allEdmundsPeriodTwoSegmentLabels segments).count z ≤ 1 := by
        rw [canonical.1.count]
        split <;> omega
      rw [labelCount] at atMostOne
      omega
    simp [hd, hs]
  · by_cases ht : z ∈ edmundsPeriodTwoTripleLabels segments
    · have hs :
          z ∉ edmundsPeriodTwoSingletonLabels segments := by
        intro hs
        have htpos :
            0 < (edmundsPeriodTwoTripleLabels segments).count z :=
          List.count_pos_iff.mpr ht
        have hspos :
            0 < (edmundsPeriodTwoSingletonLabels segments).count z :=
          List.count_pos_iff.mpr hs
        have labelCount :=
          count_allEdmundsPeriodTwoSegmentLabels z segments
        have atMostOne :
            (allEdmundsPeriodTwoSegmentLabels segments).count z ≤ 1 := by
          rw [canonical.1.count]
          split <;> omega
        rw [labelCount] at atMostOne
        omega
      simp [hd, ht, hs]
    · by_cases hs : z ∈ edmundsPeriodTwoSingletonLabels segments
      · simp [hd, ht, hs]
      · simp [hd, ht, hs]

/-- Double-block labels are exactly the labels of rendered multiplicity two. -/
theorem mem_edmundsPeriodTwoDoubleLabels_iff_count_two
    {segments : List EdmundsPeriodTwoSegment}
    (canonical : SegmentsCanonical segments) (z : Nat) :
    z ∈ edmundsPeriodTwoDoubleLabels segments ↔
      (renderEdmundsPeriodTwoSegments segments).count z = 2 := by
  rw [renderEdmundsPeriodTwoSegments_count_classification canonical z]
  by_cases hd : z ∈ edmundsPeriodTwoDoubleLabels segments
  · simp [hd]
  · by_cases ht : z ∈ edmundsPeriodTwoTripleLabels segments
    · simp [hd, ht]
    · by_cases hs : z ∈ edmundsPeriodTwoSingletonLabels segments
      · simp [hd, ht, hs]
      · simp [hd, ht, hs]

/-- Triple-block labels are exactly the labels of rendered multiplicity
three. -/
theorem mem_edmundsPeriodTwoTripleLabels_iff_count_three
    {segments : List EdmundsPeriodTwoSegment}
    (canonical : SegmentsCanonical segments) (z : Nat) :
    z ∈ edmundsPeriodTwoTripleLabels segments ↔
      (renderEdmundsPeriodTwoSegments segments).count z = 3 := by
  rw [renderEdmundsPeriodTwoSegments_count_classification canonical z]
  by_cases hd : z ∈ edmundsPeriodTwoDoubleLabels segments
  · have ht :
        z ∉ edmundsPeriodTwoTripleLabels segments := by
      intro ht
      have hdpos :
          0 < (edmundsPeriodTwoDoubleLabels segments).count z :=
        List.count_pos_iff.mpr hd
      have htpos :
          0 < (edmundsPeriodTwoTripleLabels segments).count z :=
        List.count_pos_iff.mpr ht
      have labelCount :=
        count_allEdmundsPeriodTwoSegmentLabels z segments
      have atMostOne :
          (allEdmundsPeriodTwoSegmentLabels segments).count z ≤ 1 := by
        rw [canonical.1.count]
        split <;> omega
      rw [labelCount] at atMostOne
      omega
    simp [hd, ht]
  · by_cases ht : z ∈ edmundsPeriodTwoTripleLabels segments
    · simp [hd, ht]
    · by_cases hs : z ∈ edmundsPeriodTwoSingletonLabels segments
      · simp [hd, ht, hs]
      · simp [hd, ht, hs]

theorem mem_edmundsPeriodTwoDoubleLabels_iff_block
    {segments : List EdmundsPeriodTwoSegment} (z : Nat) :
    z ∈ edmundsPeriodTwoDoubleLabels segments ↔
      EdmundsPeriodTwoRepeatedBlock.double z ∈
        allEdmundsPeriodTwoRepeatedBlocks segments := by
  unfold edmundsPeriodTwoDoubleLabels doubleLabelsOfRepeated
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨block, blockMem, mapped⟩
    cases block with
    | double x =>
        simp only [Option.some.injEq] at mapped
        subst x
        exact blockMem
    | triple x =>
        simp at mapped
  · intro blockMem
    exact ⟨.double z, blockMem, rfl⟩

theorem mem_edmundsPeriodTwoTripleLabels_iff_block
    {segments : List EdmundsPeriodTwoSegment} (z : Nat) :
    z ∈ edmundsPeriodTwoTripleLabels segments ↔
      EdmundsPeriodTwoRepeatedBlock.triple z ∈
        allEdmundsPeriodTwoRepeatedBlocks segments := by
  unfold edmundsPeriodTwoTripleLabels tripleLabelsOfRepeated
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨block, blockMem, mapped⟩
    cases block with
    | double x =>
        simp at mapped
    | triple x =>
        simp only [Option.some.injEq] at mapped
        subst x
        exact blockMem
  · intro blockMem
    exact ⟨.triple z, blockMem, rfl⟩

theorem mem_edmundsPeriodTwoDoubleBlock_iff_count_two
    {segments : List EdmundsPeriodTwoSegment}
    (canonical : SegmentsCanonical segments) (z : Nat) :
    EdmundsPeriodTwoRepeatedBlock.double z ∈
        allEdmundsPeriodTwoRepeatedBlocks segments ↔
      (renderEdmundsPeriodTwoSegments segments).count z = 2 := by
  rw [← mem_edmundsPeriodTwoDoubleLabels_iff_block]
  exact mem_edmundsPeriodTwoDoubleLabels_iff_count_two canonical z

theorem mem_edmundsPeriodTwoTripleBlock_iff_count_three
    {segments : List EdmundsPeriodTwoSegment}
    (canonical : SegmentsCanonical segments) (z : Nat) :
    EdmundsPeriodTwoRepeatedBlock.triple z ∈
        allEdmundsPeriodTwoRepeatedBlocks segments ↔
      (renderEdmundsPeriodTwoSegments segments).count z = 3 := by
  rw [← mem_edmundsPeriodTwoTripleLabels_iff_block]
  exact mem_edmundsPeriodTwoTripleLabels_iff_count_three canonical z

/-- A repeated block belongs to a canonical segmentation exactly when its
constructor tag agrees with the rendered multiplicity of its label. -/
theorem mem_edmundsPeriodTwoRepeatedBlock_iff_count_exponent
    {segments : List EdmundsPeriodTwoSegment}
    (canonical : SegmentsCanonical segments)
    (block : EdmundsPeriodTwoRepeatedBlock) :
    block ∈ allEdmundsPeriodTwoRepeatedBlocks segments ↔
      (renderEdmundsPeriodTwoSegments segments).count block.label =
        block.exponent := by
  cases block with
  | double z =>
      simpa [EdmundsPeriodTwoRepeatedBlock.label,
        EdmundsPeriodTwoRepeatedBlock.exponent,
        EdmundsPeriodTwoRepeatedBlock.toBlock,
        EdmundsPeriodTwoBlock.label,
        EdmundsPeriodTwoBlock.exponent] using
          mem_edmundsPeriodTwoDoubleBlock_iff_count_two canonical z
  | triple z =>
      simpa [EdmundsPeriodTwoRepeatedBlock.label,
        EdmundsPeriodTwoRepeatedBlock.exponent,
        EdmundsPeriodTwoRepeatedBlock.toBlock,
        EdmundsPeriodTwoBlock.label,
        EdmundsPeriodTwoBlock.exponent] using
          mem_edmundsPeriodTwoTripleBlock_iff_count_three canonical z

theorem edmundsPeriodTwoRepeatedBlock_eq_of_label_eq_exponent_eq
    {left right : EdmundsPeriodTwoRepeatedBlock}
    (labelEq : left.label = right.label)
    (exponentEq : left.exponent = right.exponent) :
    left = right := by
  cases left <;> cases right <;>
    simp_all [EdmundsPeriodTwoRepeatedBlock.label,
      EdmundsPeriodTwoRepeatedBlock.exponent,
      EdmundsPeriodTwoRepeatedBlock.toBlock,
      EdmundsPeriodTwoBlock.label,
      EdmundsPeriodTwoBlock.exponent]

private theorem sorted_nat_list_eq_of_mem_iff
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

/-- Sorted repeated runs are determined by their label set and by any pair of
count functions that recover each member's double/triple exponent.  This is
the form used with counts of the two full canonical renderings. -/
theorem edmundsPeriodTwoSortedRepeated_eq_of_label_mem_and_tag_counts
    {left right : List EdmundsPeriodTwoRepeatedBlock}
    (leftSorted :
      (left.map EdmundsPeriodTwoRepeatedBlock.label).Pairwise (· ≤ ·))
    (rightSorted :
      (right.map EdmundsPeriodTwoRepeatedBlock.label).Pairwise (· ≤ ·))
    (leftNodup :
      (left.map EdmundsPeriodTwoRepeatedBlock.label).Nodup)
    (rightNodup :
      (right.map EdmundsPeriodTwoRepeatedBlock.label).Nodup)
    (sameLabelMem :
      ∀ z,
        z ∈ left.map EdmundsPeriodTwoRepeatedBlock.label ↔
          z ∈ right.map EdmundsPeriodTwoRepeatedBlock.label)
    (leftCount rightCount : Nat → Nat)
    (sameCount : ∀ z, leftCount z = rightCount z)
    (leftTag :
      ∀ block ∈ left, leftCount block.label = block.exponent)
    (rightTag :
      ∀ block ∈ right, rightCount block.label = block.exponent) :
    left = right := by
  have labelListsEq :
      left.map EdmundsPeriodTwoRepeatedBlock.label =
        right.map EdmundsPeriodTwoRepeatedBlock.label :=
    sorted_nat_list_eq_of_mem_iff
      leftSorted rightSorted leftNodup rightNodup sameLabelMem
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons block rest =>
          simp at labelListsEq
  | cons leftHead leftTail ih =>
      cases right with
      | nil =>
          simp at labelListsEq
      | cons rightHead rightTail =>
          simp only [List.map_cons] at labelListsEq
          injection labelListsEq with headLabelEq tailLabelsEq
          have headExponentEq :
              leftHead.exponent = rightHead.exponent := by
            rw [← leftTag leftHead (List.Mem.head leftTail)]
            rw [sameCount leftHead.label]
            rw [headLabelEq]
            exact rightTag rightHead (List.Mem.head rightTail)
          have headEq :
              leftHead = rightHead :=
            edmundsPeriodTwoRepeatedBlock_eq_of_label_eq_exponent_eq
              headLabelEq headExponentEq
          subst rightHead
          congr 1
          apply ih
          · exact leftSorted.tail
          · exact rightSorted.tail
          · exact leftNodup.tail
          · exact rightNodup.tail
          · intro z
            rw [tailLabelsEq]
          · intro block blockMem
            exact leftTag block (List.Mem.tail leftHead blockMem)
          · intro block blockMem
            exact rightTag block (List.Mem.tail leftHead blockMem)
          · exact tailLabelsEq

private theorem single_repeated_segment_canonical
    {blocks : List EdmundsPeriodTwoRepeatedBlock}
    (sorted :
      (blocks.map EdmundsPeriodTwoRepeatedBlock.label).Pairwise (· ≤ ·))
    (nodup :
      (blocks.map EdmundsPeriodTwoRepeatedBlock.label).Nodup)
    (nonempty : blocks ≠ []) :
    SegmentsCanonical
      [{ repeated := blocks, singleton := none }] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [allEdmundsPeriodTwoSegmentLabels,
      EdmundsPeriodTwoSegment.labels] using nodup
  · intro segment member
    simp only [List.mem_singleton] at member
    subst segment
    exact sorted
  · intro before segment rest equality _
    cases before with
    | nil =>
        simpa using congrArg List.tail equality
    | cons first more =>
        simp at equality
  · intro segment member repeatedEmpty
    simp only [List.mem_singleton] at member
    subst segment
    exact (nonempty repeatedEmpty).elim

private theorem render_repeated_count_eq_exponent_of_mem
    {blocks : List EdmundsPeriodTwoRepeatedBlock}
    (sorted :
      (blocks.map EdmundsPeriodTwoRepeatedBlock.label).Pairwise (· ≤ ·))
    (nodup :
      (blocks.map EdmundsPeriodTwoRepeatedBlock.label).Nodup)
    {block : EdmundsPeriodTwoRepeatedBlock}
    (member : block ∈ blocks) :
    (renderEdmundsPeriodTwoRepeatedBlocks blocks).count block.label =
      block.exponent := by
  have nonempty : blocks ≠ [] := by
    intro empty
    subst blocks
    contradiction
  have canonical :=
    single_repeated_segment_canonical sorted nodup nonempty
  have blockMember :
      block ∈
        allEdmundsPeriodTwoRepeatedBlocks
          [{ repeated := blocks, singleton := none }] := by
    simpa [allEdmundsPeriodTwoRepeatedBlocks] using member
  have countEq :=
    (mem_edmundsPeriodTwoRepeatedBlock_iff_count_exponent
      canonical block).mp blockMember
  simpa [renderEdmundsPeriodTwoSegments,
    EdmundsPeriodTwoSegment.render] using countEq

/-- Convenience specialization of
`edmundsPeriodTwoSortedRepeated_eq_of_label_mem_and_tag_counts`: two sorted,
label-noduplicate repeated runs are equal when they have the same labels and
their rendered multiplicity functions agree. -/
theorem edmundsPeriodTwoSortedRepeated_eq_of_label_mem_and_render_count
    {left right : List EdmundsPeriodTwoRepeatedBlock}
    (leftSorted :
      (left.map EdmundsPeriodTwoRepeatedBlock.label).Pairwise (· ≤ ·))
    (rightSorted :
      (right.map EdmundsPeriodTwoRepeatedBlock.label).Pairwise (· ≤ ·))
    (leftNodup :
      (left.map EdmundsPeriodTwoRepeatedBlock.label).Nodup)
    (rightNodup :
      (right.map EdmundsPeriodTwoRepeatedBlock.label).Nodup)
    (sameLabelMem :
      ∀ z,
        z ∈ left.map EdmundsPeriodTwoRepeatedBlock.label ↔
          z ∈ right.map EdmundsPeriodTwoRepeatedBlock.label)
    (sameRenderedCount :
      ∀ z,
        (renderEdmundsPeriodTwoRepeatedBlocks left).count z =
          (renderEdmundsPeriodTwoRepeatedBlocks right).count z) :
    left = right := by
  apply edmundsPeriodTwoSortedRepeated_eq_of_label_mem_and_tag_counts
    leftSorted rightSorted leftNodup rightNodup sameLabelMem
    (fun z => (renderEdmundsPeriodTwoRepeatedBlocks left).count z)
    (fun z => (renderEdmundsPeriodTwoRepeatedBlocks right).count z)
    sameRenderedCount
  · intro block member
    exact render_repeated_count_eq_exponent_of_mem
      leftSorted leftNodup member
  · intro block member
    exact render_repeated_count_eq_exponent_of_mem
      rightSorted rightNodup member

end SemigroupBasis.CoRoots.S5_443Family.CanonicalSyntax
