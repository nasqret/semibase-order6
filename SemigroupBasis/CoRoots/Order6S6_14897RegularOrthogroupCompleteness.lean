import SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupNormalizationSyntax
import SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupSemantics

namespace SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev ListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

/-- Transport blockwise permutation-equivalent affine segment profiles when
the fixed leftContext contains every letter of the source profile. -/
theorem listDerivesAffineSegmentsPermWithLeftGuard
    (leftContext : List Nat) :
    forall {left right : List AffineParitySegment},
      AffineParitySegmentsPerm left right ->
      AffineParitySegmentsNormal left ->
      AffineParitySegmentsNormal right ->
      (forall letter, letter ∈ affineParityRender left ->
        letter ∈ leftContext) ->
      ListDerives
        (leftContext ++ affineParityRender left)
        (leftContext ++ affineParityRender right)
  | [], [], AffineParitySegmentsPerm.nil,
      AffineParitySegmentsNormal.nil,
      AffineParitySegmentsNormal.nil, _ =>
        by
          simpa [affineParityRender] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
              (basis := basis) leftContext)
  | ⟨leftBlock, marker⟩ :: leftRest,
      ⟨rightBlock, .(marker)⟩ :: rightRest,
      AffineParitySegmentsPerm.cons blockPermutation restPermutation,
      AffineParitySegmentsNormal.cons
        leftNodup leftFresh leftBlockGuard leftRestNormal,
      AffineParitySegmentsNormal.cons
        rightNodup rightFresh rightBlockGuard rightRestNormal,
      profileLeftGuard => by
        have blockLeftGuard :
            forall letter, letter ∈ leftBlock ->
              letter ∈ leftContext := by
          intro letter member
          apply profileLeftGuard letter
          simp only [affineParityRender, List.mem_append,
            List.mem_cons]
          exact Or.inl member
        have blockRightGuard :
            forall letter, letter ∈ leftBlock ->
              letter ∈ marker :: affineParityRender leftRest := by
          intro letter member
          rcases leftBlockGuard letter member with equal | markerMember
          · simpa [equal]
          · exact List.Mem.tail marker <|
              affineParityMarker_mem_render markerMember
        have blockStep :=
          listDerivesTwoSidedGuardedPermutation
            leftContext
            (marker :: affineParityRender leftRest)
            blockLeftGuard blockRightGuard blockPermutation
        have restLeftGuard :
            forall letter, letter ∈ affineParityRender leftRest ->
              letter ∈ leftContext ++ rightBlock ++ [marker] := by
          intro letter member
          have sourceMember :
              letter ∈
                affineParityRender
                  (⟨leftBlock, marker⟩ :: leftRest) := by
            simp only [affineParityRender, List.mem_append,
              List.mem_cons]
            exact Or.inr (Or.inr member)
          exact List.mem_append.mpr <| Or.inl <|
            List.mem_append.mpr <| Or.inl <|
              profileLeftGuard letter sourceMember
        have restStep :=
          listDerivesAffineSegmentsPermWithLeftGuard
            (leftContext ++ rightBlock ++ [marker])
            restPermutation leftRestNormal rightRestNormal
            restLeftGuard
        have blockStep' : ListDerives
            (leftContext ++ leftBlock ++ [marker] ++
              affineParityRender leftRest)
            (leftContext ++ rightBlock ++ [marker] ++
              affineParityRender leftRest) := by
          simpa [List.append_assoc] using blockStep
        have restStep' : ListDerives
            (leftContext ++ rightBlock ++ [marker] ++
              affineParityRender leftRest)
            (leftContext ++ rightBlock ++ [marker] ++
              affineParityRender rightRest) := by
          simpa [List.append_assoc] using restStep
        simpa [affineParityRender, List.append_assoc] using
          blockStep'.trans restStep'

/-- Dual blockwise transport with a fixed right guard. -/
theorem listDerivesReverseAffineSegmentsPermWithRightGuard
    (suffix : List Nat)
    {left right : List AffineParitySegment}
    (permutation : AffineParitySegmentsPerm left right)
    (leftNormal : AffineParitySegmentsNormal left)
    (rightNormal : AffineParitySegmentsNormal right)
    (rightGuard :
      forall letter, letter ∈ affineParityRender left ->
        letter ∈ suffix) :
    ListDerives
      ((affineParityRender left).reverse ++ suffix)
      ((affineParityRender right).reverse ++ suffix) := by
  have reversedGuard :
      forall letter, letter ∈ affineParityRender left ->
        letter ∈ suffix.reverse := by
    intro letter member
    have suffixMember := rightGuard letter member
    simpa using suffixMember
  have forward :=
    listDerivesAffineSegmentsPermWithLeftGuard
      suffix.reverse permutation leftNormal rightNormal reversedGuard
  have reversed := listDerivesReverse forward
  simpa [List.reverse_append, List.append_assoc] using reversed

theorem content_iff_of_affineSegmentsPerm
    {left right : List Nat}
    (permutation :
      AffineParitySegmentsPerm
        (affineParityNormalSegments left)
        (affineParityNormalSegments right))
    (letter : Nat) :
    Iff (letter ∈ left) (letter ∈ right) := by
  have markers :=
    SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupSemantics.markers_eq_of_segmentsPerm
      permutation
  change affineBarrierSequence left =
    affineBarrierSequence right at markers
  constructor
  · intro member
    apply (mem_lastOccurrenceSequence_iff
      letter right).mp
    rw [← affineBarrierSequence_eq_lastOccurrenceSequence,
      ← markers]
    rw [affineBarrierSequence_eq_lastOccurrenceSequence]
    exact (mem_lastOccurrenceSequence_iff
      letter left).mpr member
  · intro member
    apply (mem_lastOccurrenceSequence_iff
      letter left).mp
    rw [← affineBarrierSequence_eq_lastOccurrenceSequence,
      markers]
    rw [affineBarrierSequence_eq_lastOccurrenceSequence]
    exact (mem_lastOccurrenceSequence_iff
      letter right).mpr member

/-- Three semantic permutation witnesses connect the complete normal forms.
The forward affine block is transported first, then the parity residue, and
finally the reversed affine block. -/
theorem listDerivesRegularOrthogroupNormalOfPerms
    {left right : List Nat}
    (forwardPermutation :
      AffineParitySegmentsPerm
        (affineParityNormalSegments left)
        (affineParityNormalSegments right))
    (reversedPermutation :
      AffineParitySegmentsPerm
        (affineParityNormalSegments left.reverse)
        (affineParityNormalSegments right.reverse))
    (parityPermutation :
      (parityReduce left).Perm (parityReduce right)) :
    ListDerives
      (regularOrthogroupNormalList left)
      (regularOrthogroupNormalList right) := by
  have leftForwardNormal :=
    affineParityNormalSegments_normal left
  have rightForwardNormal :=
    affineParityNormalSegments_normal right
  have leftReverseNormal :=
    affineParityNormalSegments_normal left.reverse
  have rightReverseNormal :=
    affineParityNormalSegments_normal right.reverse
  have rightRaw :=
    listDerivesAffineSegmentsPermWithLeftGuard
      (reverseAffineNormalList left ++ parityReduce left)
      forwardPermutation leftForwardNormal rightForwardNormal
      (fun letter member => by
        have sourceMember :
            letter ∈ left :=
          (mem_affineNormalList_iff
            letter left).mp <| by
              simpa [affineNormalList] using member
        exact List.mem_append.mpr <| Or.inl <|
          mem_reverseAffineNormalList_of_mem sourceMember)
  have rightStep :
      ListDerives
        (regularOrthogroupNormalList left)
        (reverseAffineNormalList left ++
          parityReduce left ++ affineNormalList right) := by
    simpa [regularOrthogroupNormalList, oddParitySupport,
      affineNormalList, List.append_assoc] using rightRaw
  have middleStep :=
    listDerivesTwoSidedGuardedPermutation
      (reverseAffineNormalList left)
      (affineNormalList right)
      (fun _ member =>
        mem_reverseAffineNormalList_of_mem <|
          source_mem_of_parityReduce_mem member)
      (fun letter member => by
        have targetParity :
            letter ∈ parityReduce right :=
          parityPermutation.mem_iff.mp member
        exact mem_affineNormalList_of_mem <|
          source_mem_of_parityReduce_mem targetParity)
      parityPermutation
  have leftRaw :=
    listDerivesReverseAffineSegmentsPermWithRightGuard
      (parityReduce right ++ affineNormalList right)
      reversedPermutation leftReverseNormal rightReverseNormal
      (fun letter member => by
        have reversedSource :
            letter ∈ left.reverse :=
          (mem_affineNormalList_iff
            letter left.reverse).mp <| by
              simpa [affineNormalList] using member
        have sourceMember : letter ∈ left := by
          simpa using reversedSource
        have targetMember : letter ∈ right :=
          (content_iff_of_affineSegmentsPerm
            forwardPermutation letter).mp sourceMember
        exact List.mem_append.mpr <| Or.inr <|
          mem_affineNormalList_of_mem targetMember)
  have leftStep :
      ListDerives
        (reverseAffineNormalList left ++
          parityReduce right ++ affineNormalList right)
        (regularOrthogroupNormalList right) := by
    simpa [regularOrthogroupNormalList, oddParitySupport,
      reverseAffineNormalList, List.append_assoc] using leftRaw
  exact rightStep.trans <| middleStep.trans leftStep

/-- The complete normal forms of two target-valid words are connected by the
three segment/parity signatures recovered from the subdirect factors. -/
theorem listDerivesNormalFormsOfTargetValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.table.semigroup) :
    ListDerives
      (regularOrthogroupNormalList identity.lhs.toList)
      (regularOrthogroupNormalList identity.rhs.toList) := by
  have profiles :=
    SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupSemantics.bidirectionalSegmentsPerm_of_target_valid
      identity valid
  have signature :=
    SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupSemantics.sequenceParitySignature_of_target_valid
      identity valid
  have reversedProfile :
      AffineParitySegmentsPerm
        (affineParityNormalSegments identity.lhs.toList.reverse)
        (affineParityNormalSegments identity.rhs.toList.reverse) := by
    simpa only [Word.toList_reverse] using profiles.2
  exact listDerivesRegularOrthogroupNormalOfPerms
    profiles.1 reversedProfile signature.2.2

theorem basis_complete :
    BasisFor
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.table.semigroup
      basis := by
  refine ⟨basis_models, ?_⟩
  intro identity valid
  have leftNormal :=
    listDerivesRegularOrthogroupNormal identity.lhs.toList
  have normalBridge :=
    listDerivesNormalFormsOfTargetValid identity valid
  have rightNormal :=
    listDerivesRegularOrthogroupNormal identity.rhs.toList
  have completeList :=
    leftNormal.trans <| normalBridge.trans rightNormal.symm
  cases identity with
  | mk left right =>
      cases left with
      | mk leftHead leftTail =>
          cases right with
          | mk rightHead rightTail =>
              exact
                SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
                  completeList

end SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup
