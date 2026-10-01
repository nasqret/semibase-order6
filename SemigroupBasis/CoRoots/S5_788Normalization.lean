import SemigroupBasis.CoRoots.S5_441ExactCutAlignment
import SemigroupBasis.CoRoots.S5_788Invariant
import SemigroupBasis.CoRoots.S5_788GapNormalization

namespace SemigroupBasis.CoRoots.S5_788

open SemigroupBasis
open SemigroupBasis.Examples

/-- Restrict the global first-occurrence order to one exact-cut gap. -/
def segmentInitialOrder
    (initials : List Nat)
    (segment : UniqueSeparatorCanonicalSegment) : List Nat :=
  initials.filter fun letter =>
    decide (letter ∈ segment.quadratic)

/-- Render only the normalized gap part of one support-skeleton segment. -/
def renderInitialGap
    (initials : List Nat)
    (segment : UniqueSeparatorCanonicalSegment) : List Nat :=
  match segmentInitialOrder initials segment with
  | [] => []
  | first :: rest => first :: rest ++ [first]

/-- Render a nonempty gap with initial part `p` as `p` followed by its
first letter, then retain the optional separator once. Empty gaps render
only their separator. -/
def renderInitialSegment
    (initials : List Nat)
    (segment : UniqueSeparatorCanonicalSegment) : List Nat :=
  renderInitialGap initials segment ++ segment.separator.toList

/-- The deterministic separator/initial normal-form candidate advertised
by the classification: exact separators are retained, and each gap is
ordered by its restricted first-occurrence sequence with the first letter
repeated at the end. -/
def separatorInitialNormalList (word : Word Nat) : List Nat :=
  let initials := firstOccurrenceSequence word.toList
  (S5_441.exactCutSupportSkeleton word.toList).flatMap
    (renderInitialSegment initials)

/-- The semantic separator/initial signature uniquely determines the
explicit normal-form candidate. This theorem does not assert derivability
of that form from the 24 laws. -/
theorem separatorInitialNormalList_eq_of_sameSignature
    {left right : Word Nat}
    (same :
      S5_788Invariant.SameSeparatorInitialSignature left right) :
    separatorInitialNormalList left =
      separatorInitialNormalList right := by
  have skeletonEq :
      S5_441.exactCutSupportSkeleton left.toList =
        S5_441.exactCutSupportSkeleton right.toList :=
    S5_441.exactCutSupportSkeleton_eq_of_sameSupport_sameExactCutSignature
      same.support same.exactCuts
  unfold separatorInitialNormalList
  rw [same.initials, skeletonEq]

/-- Endpoint capping and the support-component interval induction normalize
one exact-cut gap to the restriction of the global first-occurrence order. -/
theorem listDerivesExactCutGapInitial
    (word : Word Nat) (segment : S5_441.ExactCutSegment)
    (segmentMember :
      segment ∈
        S5_441.exactCutDecomposition word.toList) :
    S5_107.ListDerives basis
      (uniqueSeparatorEndpointCap segment.gap)
      (renderInitialGap
        (firstOccurrenceSequence word.toList)
        (S5_441.exactCutSupportSegment segment)) := by
  have gapDerivation :=
    listDerivesEndpointCapToInitialGapNormal
      word segment segmentMember
  have restricted :=
    firstOccurrenceSequence_restrict_exactCutGap
      word segment segmentMember
  simpa [renderInitialGap, segmentInitialOrder,
    initialGapNormalList, restricted] using gapDerivation

private theorem renderExactCutSegments_derives_initial
    (word : Word Nat) :
    ∀ segments : List S5_441.ExactCutSegment,
      (∀ segment, segment ∈ segments →
        segment ∈
          S5_441.exactCutDecomposition word.toList) →
      S5_107.ListDerives basis
        (S5_441.renderExactCutSegments segments)
        ((S5_441.exactCutSupportSegments segments).flatMap
          (renderInitialSegment
            (firstOccurrenceSequence word.toList)))
  | [], _ =>
      S5_107.ListDerives.empty
  | segment :: remaining, allMembers => by
      have segmentMember :
          segment ∈
            S5_441.exactCutDecomposition word.toList :=
        allMembers segment (by simp)
      have remainingMembers :
          ∀ candidate, candidate ∈ remaining →
            candidate ∈
              S5_441.exactCutDecomposition word.toList := by
        intro candidate candidateMember
        exact allMembers candidate (by simp [candidateMember])
      have remainingDerivation :=
        renderExactCutSegments_derives_initial
          word remaining remainingMembers
      by_cases omitted :
          segment.gap = [] ∧ segment.separator = none
      · simpa [S5_441.renderExactCutSegments,
          S5_441.ExactCutSegment.render,
          S5_441.exactCutSupportSegments,
          S5_441.exactCutSupportSegment?, omitted] using
          remainingDerivation
      · have gapDerivation :
            S5_107.ListDerives basis segment.gap
              (renderInitialGap
                (firstOccurrenceSequence word.toList)
                (S5_441.exactCutSupportSegment segment)) :=
          (listDerivesEndpointCap segment.gap).trans
            (listDerivesExactCutGapInitial
              word segment segmentMember)
        have segmentDerivation :
            S5_107.ListDerives basis segment.render
              (renderInitialSegment
                (firstOccurrenceSequence word.toList)
                (S5_441.exactCutSupportSegment segment)) := by
          simpa [S5_441.ExactCutSegment.render,
            renderInitialSegment,
            S5_441.exactCutSupportSegment] using
            gapDerivation.append segment.separator.toList
        have headStep :=
          segmentDerivation.append
            (S5_441.renderExactCutSegments remaining)
        have tailStep :=
          remainingDerivation.prepend
            (renderInitialSegment
              (firstOccurrenceSequence word.toList)
              (S5_441.exactCutSupportSegment segment))
        simpa [S5_441.renderExactCutSegments,
          S5_441.exactCutSupportSegments,
          S5_441.exactCutSupportSegment?, omitted,
          List.append_assoc] using
          headStep.trans tailStep

/-- Every word derives to the explicit separator/initial support-skeleton
render. -/
theorem listDerivesSeparatorInitialNormal
    (word : Word Nat) :
    S5_107.ListDerives basis word.toList
      (separatorInitialNormalList word) := by
  have derivation :=
    renderExactCutSegments_derives_initial
      word
      (S5_441.exactCutDecomposition word.toList)
      (fun _ segmentMember => segmentMember)
  rw [S5_441.render_exactCutDecomposition] at derivation
  simpa [separatorInitialNormalList,
    S5_441.exactCutSupportSkeleton] using derivation

/-- Syntactic completeness of the separator/initial signature. -/
theorem derives_of_sameSeparatorInitialSignature
    {left right : Word Nat}
    (same :
      S5_788Invariant.SameSeparatorInitialSignature left right) :
    Derives basis left right := by
  have leftNormal :=
    listDerivesSeparatorInitialNormal left
  have rightNormal :=
    listDerivesSeparatorInitialNormal right
  have normalListsEqual :=
    separatorInitialNormalList_eq_of_sameSignature same
  rw [normalListsEqual] at leftNormal
  have combined := leftNormal.trans rightNormal.symm
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact S5_107.ListDerives.toWord combined

end SemigroupBasis.CoRoots.S5_788
