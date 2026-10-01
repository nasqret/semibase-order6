import SemigroupBasis.CoRoots.S5_441CanonicalGapCongruence
import SemigroupBasis.CoRoots.S5_441ExactCutAlignment
import SemigroupBasis.CoRoots.S5_441GapCountLocalization
import SemigroupBasis.CoRoots.S5_441GapNormalization

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis
open SemigroupBasis.Examples

/-- Replace one scanner gap by its deterministic canonical gap while retaining
the exact-cut separator. -/
def canonicalExactCutSegment
    (segment : ExactCutSegment) : ExactCutSegment :=
  { gap := canonicalGap segment.gap
    separator := segment.separator }

/-- Canonicalize every gap in an exact-cut segment list. -/
def canonicalExactCutSegments
    (segments : List ExactCutSegment) : List ExactCutSegment :=
  segments.map canonicalExactCutSegment

/-- Render a segment list after canonicalizing each gap independently. -/
def canonicalExactCutRenderSegments
    (segments : List ExactCutSegment) : List Nat :=
  renderExactCutSegments (canonicalExactCutSegments segments)

/-- The global `S5_441` normal form: scan at all exact cuts, canonicalize every
separator-free gap, and preserve the scanner separators. -/
def canonicalExactCutRender (letters : List Nat) : List Nat :=
  canonicalExactCutRenderSegments (exactCutDecomposition letters)

private theorem renderExactCutSegments_derives_canonical
    (letters : List Nat) :
    ∀ segments : List ExactCutSegment,
      (∀ segment, segment ∈ segments →
        segment ∈ exactCutDecomposition letters) →
      ListDerives
        (renderExactCutSegments segments)
        (canonicalExactCutRenderSegments segments)
  | [], _ => ListDerives.refl []
  | segment :: remaining, allMembers => by
      have segmentMember :
          segment ∈ exactCutDecomposition letters :=
        allMembers segment (by simp)
      have remainingMembers :
          ∀ candidate, candidate ∈ remaining →
            candidate ∈ exactCutDecomposition letters := by
        intro candidate candidateMember
        exact allMembers candidate (by simp [candidateMember])
      have segmentDerivation :
          ListDerives
            segment.render
            (canonicalExactCutSegment segment).render := by
        simpa [ExactCutSegment.render, canonicalExactCutSegment] using
          ListDerives.append
            (exactCutDecomposition_gap_derives_canonicalGap
              segmentMember)
            segment.separator.toList
      have remainingDerivation :
          ListDerives
            (renderExactCutSegments remaining)
            (canonicalExactCutRenderSegments remaining) :=
        renderExactCutSegments_derives_canonical
          letters remaining remainingMembers
      have headStep :
          ListDerives
            (segment.render ++ renderExactCutSegments remaining)
            ((canonicalExactCutSegment segment).render ++
              renderExactCutSegments remaining) :=
        ListDerives.append segmentDerivation
          (renderExactCutSegments remaining)
      have tailStep :
          ListDerives
            ((canonicalExactCutSegment segment).render ++
              renderExactCutSegments remaining)
            ((canonicalExactCutSegment segment).render ++
              canonicalExactCutRenderSegments remaining) :=
        ListDerives.prepend
          (canonicalExactCutSegment segment).render
          remainingDerivation
      simpa [canonicalExactCutRenderSegments,
        canonicalExactCutSegments] using
        ListDerives.trans headStep tailStep

/-- Every list derives to its deterministic exact-cut canonical render. -/
theorem listDerivesCanonicalExactCutRender
    (letters : List Nat) :
    ListDerives letters (canonicalExactCutRender letters) := by
  have derivation :=
    renderExactCutSegments_derives_canonical
      letters
      (exactCutDecomposition letters)
      (fun _ segmentMember => segmentMember)
  rw [render_exactCutDecomposition] at derivation
  exact derivation

/-- A support skeleton segment is rendered using the global parity profile.
Count localization shows that this agrees with canonicalizing its source gap. -/
private def canonicalExactCutSupportSegmentRender
    (letters : List Nat)
    (segment : UniqueSeparatorCanonicalSegment) : List Nat :=
  canonicalGap
      (canonicalGapPayload letters segment.quadratic) ++
    segment.separator.toList

private def canonicalExactCutSupportRender
    (letters : List Nat)
    (segments : List UniqueSeparatorCanonicalSegment) : List Nat :=
  segments.flatMap
    (canonicalExactCutSupportSegmentRender letters)

private theorem canonicalGap_eq_supportParityRepresentative
    {letters : List Nat} {segment : ExactCutSegment}
    (segmentMember :
      segment ∈ exactCutDecomposition letters) :
    canonicalGap segment.gap =
      canonicalGap
        (canonicalGapPayload letters
          (connectedComponentSortedSupport segment.gap)) := by
  apply canonicalGap_eq_of_support_parity
  · intro tested
    rw [canonicalGapPayload_mem_iff,
      connectedComponentSortedSupport_mem_iff]
  · intro tested
    by_cases testedMember : tested ∈ segment.gap
    · have supportMember :
          tested ∈
            connectedComponentSortedSupport segment.gap :=
        (connectedComponentSortedSupport_mem_iff
          tested segment.gap).2 testedMember
      rw [canonicalGapPayload_count_of_mem
        (connectedComponentSortedSupport_nodup segment.gap)
        supportMember]
      have localized :=
        exactCutDecomposition_count_mod_two_eq_gap_count_mod_two
          segmentMember testedMember
      rw [← localized]
      split <;> omega
    · have supportNotMember :
          tested ∉
            connectedComponentSortedSupport segment.gap := by
        intro supportMember
        exact testedMember <|
          (connectedComponentSortedSupport_mem_iff
            tested segment.gap).1 supportMember
      rw [canonicalGapPayload_count_of_not_mem
        (connectedComponentSortedSupport_nodup segment.gap)
        supportNotMember]
      have gapCountZero :
          segment.gap.count tested = 0 :=
        List.count_eq_zero.mpr testedMember
      simp [gapCountZero]

private theorem canonicalExactCutSegment_render_eq_supportRender
    {letters : List Nat} {segment : ExactCutSegment}
    (segmentMember :
      segment ∈ exactCutDecomposition letters) :
    (canonicalExactCutSegment segment).render =
      canonicalExactCutSupportSegmentRender letters
        (exactCutSupportSegment segment) := by
  change
    canonicalGap segment.gap ++ segment.separator.toList =
      canonicalGap
          (canonicalGapPayload letters
            (connectedComponentSortedSupport segment.gap)) ++
        segment.separator.toList
  rw [canonicalGap_eq_supportParityRepresentative segmentMember]

private theorem canonicalExactCutRenderSegments_eq_supportRender
    {letters : List Nat} :
    ∀ segments : List ExactCutSegment,
      (∀ segment, segment ∈ segments →
        segment ∈ exactCutDecomposition letters) →
      canonicalExactCutRenderSegments segments =
        canonicalExactCutSupportRender letters
          (exactCutSupportSegments segments)
  | [], _ => rfl
  | segment :: remaining, allMembers => by
      have segmentMember :
          segment ∈ exactCutDecomposition letters :=
        allMembers segment (by simp)
      have remainingMembers :
          ∀ candidate, candidate ∈ remaining →
            candidate ∈ exactCutDecomposition letters := by
        intro candidate candidateMember
        exact allMembers candidate (by simp [candidateMember])
      have remainingEq :=
        canonicalExactCutRenderSegments_eq_supportRender
          remaining remainingMembers
      by_cases omitted :
          segment.gap = [] ∧ segment.separator = none
      · have segmentRenderEmpty :
            (canonicalExactCutSegment segment).render = [] := by
          simp [canonicalExactCutSegment, ExactCutSegment.render,
            omitted.1, omitted.2]
        calc
          canonicalExactCutRenderSegments (segment :: remaining) =
              (canonicalExactCutSegment segment).render ++
                canonicalExactCutRenderSegments remaining := rfl
          _ = canonicalExactCutRenderSegments remaining := by
            rw [segmentRenderEmpty]
            simp
          _ = canonicalExactCutSupportRender letters
                (exactCutSupportSegments remaining) :=
            remainingEq
          _ = canonicalExactCutSupportRender letters
                (exactCutSupportSegments
                  (segment :: remaining)) := by
            simp [exactCutSupportSegments,
              exactCutSupportSegment?, omitted]
      · have segmentRenderEq :
            (canonicalExactCutSegment segment).render =
              canonicalExactCutSupportSegmentRender letters
                (exactCutSupportSegment segment) :=
          canonicalExactCutSegment_render_eq_supportRender
            segmentMember
        calc
          canonicalExactCutRenderSegments (segment :: remaining) =
              (canonicalExactCutSegment segment).render ++
                canonicalExactCutRenderSegments remaining := rfl
          _ =
              canonicalExactCutSupportSegmentRender letters
                  (exactCutSupportSegment segment) ++
                canonicalExactCutSupportRender letters
                  (exactCutSupportSegments remaining) := by
            rw [segmentRenderEq, remainingEq]
          _ = canonicalExactCutSupportRender letters
                (exactCutSupportSegments
                  (segment :: remaining)) := by
            simp [canonicalExactCutSupportRender,
              exactCutSupportSegments,
              exactCutSupportSegment?, omitted]

private theorem canonicalExactCutRender_eq_supportRender
    (letters : List Nat) :
    canonicalExactCutRender letters =
      canonicalExactCutSupportRender letters
        (exactCutSupportSkeleton letters) := by
  simpa [canonicalExactCutRender, exactCutSupportSkeleton] using
    canonicalExactCutRenderSegments_eq_supportRender
      (letters := letters)
      (exactCutDecomposition letters)
      (fun _ segmentMember => segmentMember)

private theorem
    canonicalExactCutSupportSegmentRender_eq_of_parity
    {left right : List Nat}
    (parityEq :
      ∀ letter,
        left.count letter % 2 =
          right.count letter % 2)
    (segment : UniqueSeparatorCanonicalSegment) :
    canonicalExactCutSupportSegmentRender left segment =
      canonicalExactCutSupportSegmentRender right segment := by
  unfold canonicalExactCutSupportSegmentRender
  rw [canonicalGapPayload_eq_of_parity parityEq]

private theorem canonicalExactCutSupportRender_eq_of_parity
    {left right : List Nat}
    (parityEq :
      ∀ letter,
        left.count letter % 2 =
          right.count letter % 2) :
    ∀ segments : List UniqueSeparatorCanonicalSegment,
      canonicalExactCutSupportRender left segments =
        canonicalExactCutSupportRender right segments
  | [] => rfl
  | segment :: remaining => by
      calc
        canonicalExactCutSupportRender left
            (segment :: remaining) =
          canonicalExactCutSupportSegmentRender left segment ++
            canonicalExactCutSupportRender left remaining := rfl
        _ =
          canonicalExactCutSupportSegmentRender right segment ++
            canonicalExactCutSupportRender right remaining := by
          rw [
            canonicalExactCutSupportSegmentRender_eq_of_parity
              parityEq segment,
            canonicalExactCutSupportRender_eq_of_parity
              parityEq remaining
          ]
        _ = canonicalExactCutSupportRender right
            (segment :: remaining) := rfl

/-- The full parity-separator signature determines the global exact-cut
canonical render. Raw scanner decompositions need not be equal; their support
skeletons align, and localized gap parity determines each canonical gap. -/
theorem canonicalExactCutRender_eq_of_sameParitySeparatorSignature
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_441Invariant.SameParitySeparatorSignature
        left right) :
    canonicalExactCutRender left.toList =
      canonicalExactCutRender right.toList := by
  have skeletonEq :
      exactCutSupportSkeleton left.toList =
        exactCutSupportSkeleton right.toList :=
    exactCutSupportSkeleton_eq_of_sameParitySeparatorSignature
      same
  calc
    canonicalExactCutRender left.toList =
        canonicalExactCutSupportRender left.toList
          (exactCutSupportSkeleton left.toList) :=
      canonicalExactCutRender_eq_supportRender left.toList
    _ = canonicalExactCutSupportRender right.toList
          (exactCutSupportSkeleton left.toList) :=
      canonicalExactCutSupportRender_eq_of_parity
        same.parity (exactCutSupportSkeleton left.toList)
    _ = canonicalExactCutSupportRender right.toList
          (exactCutSupportSkeleton right.toList) := by
      rw [skeletonEq]
    _ = canonicalExactCutRender right.toList :=
      (canonicalExactCutRender_eq_supportRender right.toList).symm

/-- Words with the full parity-separator signature are list-derivable through
their common global canonical render. -/
theorem listDerives_of_sameParitySeparatorSignature
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_441Invariant.SameParitySeparatorSignature
        left right) :
    ListDerives left.toList right.toList := by
  have leftNormal :=
    listDerivesCanonicalExactCutRender left.toList
  have rightNormal :=
    listDerivesCanonicalExactCutRender right.toList
  have middle :
      ListDerives
        (canonicalExactCutRender left.toList)
        (canonicalExactCutRender right.toList) := by
    rw [
      canonicalExactCutRender_eq_of_sameParitySeparatorSignature
        same
    ]
    exact ListDerives.refl _
  exact ListDerives.trans leftNormal <|
    ListDerives.trans middle (ListDerives.symm rightNormal)

/-- Word-level completeness bridge for the parity-separator signature. -/
theorem derives_of_sameParitySeparatorSignature
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_441Invariant.SameParitySeparatorSignature
        left right) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [S5_107.listWordOfCons, Word.toList] using
            ListDerives.toWord
              (listDerives_of_sameParitySeparatorSignature same)

end SemigroupBasis.CoRoots.S5_441
