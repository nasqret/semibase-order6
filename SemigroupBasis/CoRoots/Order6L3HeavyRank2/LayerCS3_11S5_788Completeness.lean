import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_11S5_788AnchoredGaps
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon
import SemigroupBasis.CoRoots.S5_788GapNormalization

/-!
# Unrestricted C2 completeness for `S3_11 × S5_788`

Every exact-cut gap is normalized through the eighteen-law anchored calculus;
global first-occurrence order and occurrence parity are localized with the
existing scanner ownership theorems.  No bounded validity or stronger-factor
signature occurs in the public derivation.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_11S5_788

open SemigroupBasis
open SemigroupBasis.Examples

private theorem firstOccurrenceSequence_filter_gapSupport
    (gap : List Nat) :
    (firstOccurrenceSequence gap).filter
      (fun selected => decide
        (selected ∈ connectedComponentSortedSupport gap)) =
      firstOccurrenceSequence gap := by
  apply List.filter_eq_self.mpr
  intro selected member
  simp only [decide_eq_true_eq]
  exact
    (connectedComponentSortedSupport_mem_iff selected gap).mpr
      ((mem_firstOccurrenceSequence_iff selected gap).mp member)

private theorem gapParityPayload_eq
    (word : Word Nat)
    (segment : SemigroupBasis.CoRoots.S5_441.ExactCutSegment)
    (segmentMember :
      segment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition word.toList)
    (remaining : List Nat)
    (allMembers : ∀ letter ∈ remaining, letter ∈ segment.gap) :
    remaining.flatMap
        (parityMultiplicityBlock
          (fun letter => word.toList.count letter % 2)) =
      remaining.flatMap
        (parityMultiplicityBlock
          (fun letter => segment.gap.count letter % 2)) := by
  induction remaining with
  | nil =>
      rfl
  | cons letter rest ih =>
      have member : letter ∈ segment.gap :=
        allMembers letter (by simp)
      have countEq :=
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_count_eq_gap_count
          segmentMember member
      have tailMembers : ∀ selected ∈ rest, selected ∈ segment.gap := by
        intro selected selectedMember
        exact allMembers selected (by simp [selectedMember])
      simp only [List.flatMap_cons]
      rw [parityMultiplicityBlock, parityMultiplicityBlock, countEq,
        ih tailMembers]

private theorem renderExactCutGap_eq_local
    (word : Word Nat)
    (segment : SemigroupBasis.CoRoots.S5_441.ExactCutSegment)
    (segmentMember :
      segment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition word.toList) :
    renderParitySeparatorInitialGap
        (firstOccurrenceSequence word.toList)
        (fun letter => word.toList.count letter % 2)
        (SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment segment) =
      renderParitySeparatorInitialGap
        (firstOccurrenceSequence segment.gap)
        (fun letter => segment.gap.count letter % 2)
        ⟨connectedComponentSortedSupport segment.gap, none⟩ := by
  have restricted :=
    SemigroupBasis.CoRoots.S5_788.firstOccurrenceSequence_restrict_exactCutGap
      word segment segmentMember
  have localRestricted :=
    firstOccurrenceSequence_filter_gapSupport segment.gap
  unfold renderParitySeparatorInitialGap
  rw [restricted, localRestricted]
  cases initials : firstOccurrenceSequence segment.gap with
  | nil =>
      rfl
  | cons anchor remaining =>
      have anchorMember : anchor ∈ segment.gap := by
        apply (mem_firstOccurrenceSequence_iff anchor segment.gap).mp
        simp [initials]
      have anchorCount :=
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_count_eq_gap_count
          segmentMember anchorMember
      have remainingMembers :
          ∀ letter ∈ remaining, letter ∈ segment.gap := by
        intro letter member
        apply (mem_firstOccurrenceSequence_iff letter segment.gap).mp
        simp [initials, member]
      have payload := gapParityPayload_eq word segment segmentMember
        remaining remainingMembers
      simp only [initials]
      simp [anchorCount, payload]

/-- Normalize one arbitrary exact-cut gap using the global C2 coordinates. -/
theorem listDerivesExactCutGapParityInitial
    (word : Word Nat)
    (segment : SemigroupBasis.CoRoots.S5_441.ExactCutSegment)
    (segmentMember :
      segment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition word.toList) :
    SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis segment.gap
      (renderParitySeparatorInitialGap
        (firstOccurrenceSequence word.toList)
        (fun letter => word.toList.count letter % 2)
        (SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment segment)) := by
  rw [renderExactCutGap_eq_local word segment segmentMember]
  by_cases empty : segment.gap = []
  · simp [empty, renderParitySeparatorInitialGap,
      firstOccurrenceSequence,
      connectedComponentSortedSupport,
      connectedComponentDistinctSupport]
    exact .empty
  · exact
      listDerivesGapToParitySeparatorInitialNormal empty
        (SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_gap_no_exactCut
          segmentMember)

private theorem renderExactCutSegments_derives_parityInitial
    (word : Word Nat) :
    ∀ segments : List SemigroupBasis.CoRoots.S5_441.ExactCutSegment,
      (∀ segment, segment ∈ segments →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition word.toList) →
      SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis
        (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments segments)
        ((SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments segments).flatMap
          (renderParitySeparatorInitialSegment
            (firstOccurrenceSequence word.toList)
            (fun letter => word.toList.count letter % 2)))
  | [], _ =>
      SemigroupBasis.CoRoots.S5_107.ListDerives.empty
  | segment :: remaining, allMembers => by
      have segmentMember :
          segment ∈
            SemigroupBasis.CoRoots.S5_441.exactCutDecomposition word.toList :=
        allMembers segment (by simp)
      have remainingMembers :
          ∀ candidate, candidate ∈ remaining →
            candidate ∈
              SemigroupBasis.CoRoots.S5_441.exactCutDecomposition word.toList := by
        intro candidate candidateMember
        exact allMembers candidate (by simp [candidateMember])
      have remainingDerivation :=
        renderExactCutSegments_derives_parityInitial
          word remaining remainingMembers
      by_cases omitted : segment.gap = [] ∧ segment.separator = none
      · simpa [SemigroupBasis.CoRoots.S5_441.renderExactCutSegments,
          SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment?, omitted] using
          remainingDerivation
      · have gapDerivation :=
          listDerivesExactCutGapParityInitial word segment segmentMember
        have segmentDerivation :
            SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis
              segment.render
              (renderParitySeparatorInitialSegment
                (firstOccurrenceSequence word.toList)
                (fun letter => word.toList.count letter % 2)
                (SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment
                  segment)) := by
          simpa [SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
            renderParitySeparatorInitialSegment,
            SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment] using
            gapDerivation.append segment.separator.toList
        have headStep :=
          segmentDerivation.append
            (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments remaining)
        have tailStep :=
          remainingDerivation.prepend
            (renderParitySeparatorInitialSegment
              (firstOccurrenceSequence word.toList)
              (fun letter => word.toList.count letter % 2)
              (SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment segment))
        simpa [SemigroupBasis.CoRoots.S5_441.renderExactCutSegments,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment?, omitted,
          List.append_assoc] using
          headStep.trans tailStep

/-- Every arbitrary nonempty word reaches the repaired anchored C2 render. -/
theorem listDerivesParitySeparatorInitialNormal
    (word : Word Nat) :
    SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis word.toList
      (paritySeparatorInitialNormalList word) := by
  have derivation :=
    renderExactCutSegments_derives_parityInitial
      word
      (SemigroupBasis.CoRoots.S5_441.exactCutDecomposition word.toList)
      (fun _ member => member)
  rw [SemigroupBasis.CoRoots.S5_441.render_exactCutDecomposition]
    at derivation
  simpa [paritySeparatorInitialNormalList,
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton] using
    derivation

/-- The repaired deterministic candidate preserves the complete exact-cut
support skeleton for every word; no reachability premise is assumed. -/
theorem paritySeparatorInitialNormalList_preserves_exactCutSkeleton
    (word : Word Nat) :
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton
        (paritySeparatorInitialNormalList word) =
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton word.toList := by
  cases word with
  | mk head tail =>
      obtain ⟨normalHead, normalTail, normalShape, derivation⟩ :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.from_cons
          (listDerivesParitySeparatorInitialNormal (Word.mk head tail))
      have preserved := exactCutSupportSkeleton_eq_of_target_derives
        derivation
      simpa [normalShape,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons, Word.toList] using
        preserved.symm

/-- The exact C2 factor signature is syntactically complete over all words. -/
theorem derives_of_sameParitySeparatorInitialSignature
    {left right : Word Nat}
    (same : SameParitySeparatorInitialSignature left right) :
    Derives targetBasis left right := by
  have leftNormal := listDerivesParitySeparatorInitialNormal left
  have rightNormal := listDerivesParitySeparatorInitialNormal right
  have normalListsEqual :=
    paritySeparatorInitialNormalList_eq_of_sameSignature same
  rw [normalListsEqual] at leftNormal
  have combined := leftNormal.trans rightNormal.symm
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord combined

/-- Both factor theories imply a genuine derivation from the exact eighteen
displayed laws, with no bounded oracle or circular separation premise. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_11.table.semigroup)
    (rightValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup) :
    Derives targetBasis identity.lhs identity.rhs :=
  derives_of_sameParitySeparatorInitialSignature
    (sameSignature_of_factor_valid identity leftValid rightValid)

/-- The unrestricted displayed-law derivation ensures that the deterministic
list normal form always represents a genuine nonempty semigroup word. -/
theorem paritySeparatorInitialNormalList_ne_nil
    (word : Word Nat) :
    paritySeparatorInitialNormalList word ≠ [] := by
  cases word with
  | mk head tail =>
      exact
        SemigroupBasis.CoRoots.S5_107.ListDerives.target_ne_nil
          (listDerivesParitySeparatorInitialNormal (Word.mk head tail))

/-- Word-valued packaging of the exact anchored list normal form.  The
default head is unreachable because of the preceding nonemptiness theorem. -/
def paritySeparatorInitialNormalWord (word : Word Nat) : Word Nat :=
  ⟨(paritySeparatorInitialNormalList word).headD 0,
    (paritySeparatorInitialNormalList word).tail⟩

theorem paritySeparatorInitialNormalWord_toList
    (word : Word Nat) :
    (paritySeparatorInitialNormalWord word).toList =
      paritySeparatorInitialNormalList word := by
  cases shape : paritySeparatorInitialNormalList word with
  | nil =>
      exact False.elim
        (paritySeparatorInitialNormalList_ne_nil word shape)
  | cons head tail =>
      simp [paritySeparatorInitialNormalWord, shape, Word.toList]

/-- The certified seed's first unrestricted field. -/
theorem derives_paritySeparatorInitialNormalWord
    (word : Word Nat) :
    Derives targetBasis word (paritySeparatorInitialNormalWord word) := by
  cases word with
  | mk head tail =>
      cases shape : paritySeparatorInitialNormalList (Word.mk head tail) with
      | nil =>
          exact False.elim
            (paritySeparatorInitialNormalList_ne_nil
              (Word.mk head tail) shape)
      | cons normalHead normalTail =>
          have derivation :
              SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis
                (head :: tail) (normalHead :: normalTail) := by
            simpa [shape, Word.toList] using
              listDerivesParitySeparatorInitialNormal (Word.mk head tail)
          have asWord :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord derivation
          simpa [paritySeparatorInitialNormalWord, shape,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons] using asWord

/-- The certified seed's second unrestricted field, proved from the actual
two-factor semantic signature rather than a quotient or finite window. -/
theorem paritySeparatorInitialNormalWord_eq_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_11.table.semigroup)
    (rightValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup) :
    paritySeparatorInitialNormalWord identity.lhs =
      paritySeparatorInitialNormalWord identity.rhs := by
  apply Word.toList_injective
  rw [paritySeparatorInitialNormalWord_toList,
    paritySeparatorInitialNormalWord_toList]
  exact paritySeparatorInitialNormalList_eq_of_factor_valid
    identity leftValid rightValid

/-- Genuine reviewed-API seed for the isolated C2 pair. -/
def intersectionNormalizer :
    IntersectionNormalizer
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup
      targetBasis where
  normal := paritySeparatorInitialNormalWord
  derives_normal := derives_paritySeparatorInitialNormalWord
  normal_eq_of_factor_valid :=
    paritySeparatorInitialNormalWord_eq_of_factor_valid

/-- The exact eighteen displayed laws form the unrestricted intersection
basis for the two C2 factor theories. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup
      targetBasis :=
  intersectionNormalizer.toIntersectionBasis
    targetModelsLeft targetModelsRight

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_11S5_788
