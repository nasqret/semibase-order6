import SemigroupBasis.CoRoots.Order6SporadicSection13Semantics
import SemigroupBasis.CoRoots.Order6SporadicSection13Signature
import SemigroupBasis.CoRoots.S5_345Normalization
import SemigroupBasis.CoRoots.S5_870Invariant

namespace SemigroupBasis.CoRoots.Order6SporadicSection13

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_870

/-! ## Reversed affine presentation of the canonical word -/

private def paritySegment
    (block : FirstOccurrenceGapBlock) : AffineParitySegment :=
  ⟨(parityBlock block.seconds).reverse, block.marker⟩

private def reverseParitySegments
    (blocks : List FirstOccurrenceGapBlock) :
    List AffineParitySegment :=
  blocks.reverse.map paritySegment

private def canonicalSegments
    (final : Nat) (blocks : List FirstOccurrenceGapBlock) :
    List AffineParitySegment :=
  ⟨[], final⟩ :: reverseParitySegments blocks

@[simp]
private theorem reverseParitySegments_cons
    (block : FirstOccurrenceGapBlock)
    (rest : List FirstOccurrenceGapBlock) :
    reverseParitySegments (block :: rest) =
      reverseParitySegments rest ++ [paritySegment block] := by
  simp [reverseParitySegments]

private theorem affineParityRender_append
    (left right : List AffineParitySegment) :
    affineParityRender (left ++ right) =
      affineParityRender left ++ affineParityRender right := by
  induction left with
  | nil => rfl
  | cons segment rest induction =>
      simp [affineParityRender, induction, List.append_assoc]

private theorem affineParityMarkers_append
    (left right : List AffineParitySegment) :
    affineParityMarkers (left ++ right) =
      affineParityMarkers left ++ affineParityMarkers right := by
  induction left with
  | nil => rfl
  | cons segment rest induction =>
      simp [affineParityMarkers, induction]

private theorem render_reverseParitySegments
    (blocks : List FirstOccurrenceGapBlock) :
    affineParityRender (reverseParitySegments blocks) =
      (renderParityGapBlocks blocks).reverse := by
  induction blocks with
  | nil => rfl
  | cons block rest induction =>
      rw [reverseParitySegments_cons, affineParityRender_append,
        induction]
      simp [paritySegment, affineParityRender, renderParityGapBlocks,
        List.reverse_append, List.append_assoc]

private theorem markers_reverseParitySegments
    (blocks : List FirstOccurrenceGapBlock) :
    affineParityMarkers (reverseParitySegments blocks) =
      (gapBlockMarkers blocks).reverse := by
  induction blocks with
  | nil => rfl
  | cons block rest induction =>
      rw [reverseParitySegments_cons, affineParityMarkers_append,
        induction]
      simp [paritySegment, affineParityMarkers, gapBlockMarkers]

private theorem render_canonicalSegments
    (final : Nat) (blocks : List FirstOccurrenceGapBlock) :
    affineParityRender (canonicalSegments final blocks) =
      (renderParityGapBlocks blocks ++ [final]).reverse := by
  simp [canonicalSegments, affineParityRender,
    render_reverseParitySegments, List.reverse_append]

private theorem markers_canonicalSegments
    (final : Nat) (blocks : List FirstOccurrenceGapBlock) :
    affineParityMarkers (canonicalSegments final blocks) =
      final :: (gapBlockMarkers blocks).reverse := by
  simp [canonicalSegments, affineParityMarkers,
    markers_reverseParitySegments]

private theorem gapBlockMarker_mem_render
    {selected : Nat} :
    ∀ {blocks : List FirstOccurrenceGapBlock},
      selected ∈ gapBlockMarkers blocks →
        selected ∈ renderGapBlocks blocks
  | [], member => by
      simp [gapBlockMarkers] at member
  | block :: rest, member => by
      simp only [gapBlockMarkers, List.map_cons,
        FirstOccurrenceGapBlock.marker, List.mem_cons] at member
      simp only [renderGapBlocks, List.mem_cons, List.mem_append]
      rcases member with atMarker | inRest
      · exact Or.inl atMarker
      · exact Or.inr <| Or.inr <|
          gapBlockMarker_mem_render inRest

private theorem reverseParitySegments_acc_normal
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    {tailSegments : List AffineParitySegment}
    (formed : GapBlocksWellFormed seen blocks)
    (tailNormal : AffineParitySegmentsNormal tailSegments)
    (tailMarkers : affineParityMarkers tailSegments = seen) :
    AffineParitySegmentsNormal
      (reverseParitySegments blocks ++ tailSegments) := by
  induction formed generalizing tailSegments with
  | nil =>
      simpa [reverseParitySegments] using tailNormal
  | cons seen block rest markerFresh secondsSeen tailFormed induction =>
      have blockNodup :
          (paritySegment block).parity.Nodup := by
        change (parityBlock block.seconds).reverse.Nodup
        change (parityBlock block.seconds).reverse.Pairwise
          (fun left right : Nat => left ≠ right)
        rw [List.pairwise_reverse]
        exact (parityBlock_nodup block.seconds).imp
          (fun different => Ne.symm different)
      have markerFreshInTail :
          block.marker ∉ affineParityMarkers tailSegments := by
        simpa [tailMarkers] using markerFresh
      have blockGuard :
          ∀ selected, selected ∈ (paritySegment block).parity →
            selected = block.marker ∨
              selected ∈ affineParityMarkers tailSegments := by
        intro selected member
        have inParityBlock :
            selected ∈ parityBlock block.seconds := by
          simpa [paritySegment] using member
        rcases List.mem_cons.mp
            (secondsSeen selected
              (mem_of_mem_parityBlock inParityBlock)) with
          atMarker | inSeen
        · exact Or.inl atMarker
        · exact Or.inr <| by
            simpa [tailMarkers] using inSeen
      have currentNormal :
          AffineParitySegmentsNormal
            (paritySegment block :: tailSegments) :=
        AffineParitySegmentsNormal.cons blockNodup
          markerFreshInTail blockGuard tailNormal
      have currentMarkers :
          affineParityMarkers
              (paritySegment block :: tailSegments) =
            block.marker :: seen := by
        simp [affineParityMarkers, paritySegment, tailMarkers]
      have restNormal :=
        induction currentNormal currentMarkers
      simpa [List.append_assoc] using restNormal

private theorem canonicalSegments_normal
    {final : Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed [] blocks)
    (finalAbsent : final ∉ renderGapBlocks blocks) :
    AffineParitySegmentsNormal
      (canonicalSegments final blocks) := by
  have reversedNormal :
      AffineParitySegmentsNormal (reverseParitySegments blocks) := by
    simpa using
      (reverseParitySegments_acc_normal formed
        AffineParitySegmentsNormal.nil rfl)
  have finalNotMarker : final ∉ gapBlockMarkers blocks := by
    intro member
    exact finalAbsent (gapBlockMarker_mem_render member)
  have finalFresh :
      final ∉ affineParityMarkers (reverseParitySegments blocks) := by
    rw [markers_reverseParitySegments]
    simpa using finalNotMarker
  exact AffineParitySegmentsNormal.cons List.nodup_nil
    finalFresh (by simp) reversedNormal

private theorem canonicalSegments_reverse_sorted
    (final : Nat) (blocks : List FirstOccurrenceGapBlock) :
    ∀ segment, segment ∈ canonicalSegments final blocks →
      segment.parity.reverse.Pairwise (· ≤ ·) := by
  intro segment member
  rcases List.mem_cons.mp member with atFinal | inBlocks
  · subst segment
    simp [canonicalSegments]
  · unfold reverseParitySegments at inBlocks
    obtain ⟨block, _, rfl⟩ := List.mem_map.mp inBlocks
    simpa [paritySegment] using
      S5_254.canonicalGapParityResidue_pairwise block.seconds

private theorem reverse_perm
    {left right : List Nat} (permutation : left.Perm right) :
    left.reverse.Perm right.reverse := by
  rw [List.perm_iff_count] at permutation ⊢
  intro selected
  simpa using permutation selected

private theorem affineParitySegments_eq_of_perm_and_reverse_sorted
    {left right : List AffineParitySegment}
    (permutation : AffineParitySegmentsPerm left right)
    (leftSorted : ∀ segment, segment ∈ left →
      segment.parity.reverse.Pairwise (· ≤ ·))
    (rightSorted : ∀ segment, segment ∈ right →
      segment.parity.reverse.Pairwise (· ≤ ·)) :
    left = right := by
  induction permutation with
  | nil => rfl
  | @cons leftBlock rightBlock marker leftRest rightRest
      blockPermutation restPermutation induction =>
      have leftBlockSorted :
          leftBlock.reverse.Pairwise (· ≤ ·) := by
        simpa using leftSorted ⟨leftBlock, marker⟩ (by simp)
      have rightBlockSorted :
          rightBlock.reverse.Pairwise (· ≤ ·) := by
        simpa using rightSorted ⟨rightBlock, marker⟩ (by simp)
      have reversedEqual : leftBlock.reverse = rightBlock.reverse :=
        List.Perm.eq_of_pairwise
          (fun _ _ _ _ leftLe rightLe =>
            Nat.le_antisymm leftLe rightLe)
          leftBlockSorted rightBlockSorted
          (reverse_perm blockPermutation)
      have blockEqual : leftBlock = rightBlock :=
        List.reverse_inj.mp reversedEqual
      have restEqual : leftRest = rightRest :=
        induction
          (fun segment member =>
            leftSorted segment (List.Mem.tail _ member))
          (fun segment member =>
            rightSorted segment (List.Mem.tail _ member))
      subst rightBlock
      rw [restEqual]

/-! ## Simple-final canonical uniqueness -/

private theorem final_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).final = final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

private theorem split_final_and_absent_of_simple
    {word : Word Nat} {final : Nat}
    (simple : S5_345.simpleFinalVariable word = some final) :
    (splitPrefixFinal word).2 = final ∧
      final ∉ (splitPrefixFinal word).1 := by
  have simpleSpec :=
    (S5_345.simpleFinalVariable_eq_some_iff word final).1 simple
  have splitFinal :
      (splitPrefixFinal word).2 = word.final := by
    have reconstructed :=
      congrArg Word.final (wordOfPrefixFinal_split word)
    rw [final_wordOfPrefixFinal] at reconstructed
    exact reconstructed
  have splitFinalEq : (splitPrefixFinal word).2 = final :=
    splitFinal.trans simpleSpec.2
  have countOne := simpleSpec.1
  unfold S5_107.SimpleIn at countOne
  rw [toList_eq_splitPrefixFinal, splitFinalEq,
    List.count_append] at countOne
  have prefixZero :
      (splitPrefixFinal word).1.count final = 0 := by
    simp only [List.count_singleton_self] at countOne
    omega
  exact ⟨splitFinalEq, List.count_eq_zero.mp prefixZero⟩

private theorem jModelsBasis :
    Models Generated.S3_6.table.semigroup basis := by
  intro identity member
  exact S6_10203.jEmbedding.pullback_identity identity
    (S6_10203.publishedModels identity member)

private theorem oModelsBasis :
    Models Generated.S4_96.table.semigroup.opposite basis := by
  intro identity member
  exact S6_10203.oEmbedding.pullback_identity identity
    (S6_10203.publishedModels identity member)

private def canonicalIdentity (identity : Identity Nat) : Identity Nat :=
  ⟨canonicalWord identity.lhs, canonicalWord identity.rhs⟩

private theorem canonicalIdentity_valid
    {S : Type u} (semigroup : Semigroup S)
    (models : Models semigroup basis)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy semigroup) :
    (canonicalIdentity identity).SatisfiedBy semigroup := by
  intro valuation
  exact
    ((derivesCanonicalWord identity.lhs).sound models valuation).symm.trans <|
      (valid valuation).trans
        ((derivesCanonicalWord identity.rhs).sound models valuation)

/-- In the simple-final branch of Proposition 13.1, the two normalized words
are literally equal.  The proof reconstructs their reversed affine segments
from the marker order and the parity coordinates supplied by `J` and `O`. -/
theorem canonicalWord_eq_of_factors_of_simpleFinal
    (identity : Identity Nat)
    (jValid : identity.SatisfiedBy Generated.S3_6.table.semigroup)
    (oValid :
      identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite)
    {final : Nat}
    (leftSimple :
      S5_345.simpleFinalVariable identity.lhs = some final) :
    canonicalWord identity.lhs = canonicalWord identity.rhs := by
  have simpleEqual := jValid_simpleFinalVariable_eq identity jValid
  have rightSimple :
      S5_345.simpleFinalVariable identity.rhs = some final :=
    simpleEqual.symm.trans leftSimple
  obtain ⟨leftFinal, leftAbsent⟩ :=
    split_final_and_absent_of_simple leftSimple
  obtain ⟨rightFinal, rightAbsent⟩ :=
    split_final_and_absent_of_simple rightSimple
  let leftPrefix := (splitPrefixFinal identity.lhs).1
  let rightPrefix := (splitPrefixFinal identity.rhs).1
  let leftBlocks := gapBlocksList leftPrefix
  let rightBlocks := gapBlocksList rightPrefix
  let leftSegments := canonicalSegments final leftBlocks
  let rightSegments := canonicalSegments final rightBlocks
  have firstOccurrences :=
    oValid_firstOccurrenceSequence_eq identity oValid
  rw [toList_eq_splitPrefixFinal, toList_eq_splitPrefixFinal,
    leftFinal, rightFinal] at firstOccurrences
  simp only [S5_345.firstOccurrenceSequence_append_final,
    leftAbsent, rightAbsent, if_false] at firstOccurrences
  have prefixFirstOccurrences :
      firstOccurrenceSequence leftPrefix =
        firstOccurrenceSequence rightPrefix := by
    exact List.append_cancel_right firstOccurrences
  have blockMarkers :
      gapBlockMarkers leftBlocks = gapBlockMarkers rightBlocks := by
    simpa [leftBlocks, rightBlocks,
      gapBlockMarkers_gapBlocksList,
      firstOccurrenceSequenceList_eq_firstOccurrenceSequence] using
        prefixFirstOccurrences
  have segmentMarkers :
      affineParityMarkers leftSegments =
        affineParityMarkers rightSegments := by
    simp [leftSegments, rightSegments,
      markers_canonicalSegments, blockMarkers]
  have leftNormal : AffineParitySegmentsNormal leftSegments := by
    apply canonicalSegments_normal
      (gapBlocksList_wellFormed leftPrefix)
    simpa [leftBlocks, render_gapBlocksList] using leftAbsent
  have rightNormal : AffineParitySegmentsNormal rightSegments := by
    apply canonicalSegments_normal
      (gapBlocksList_wellFormed rightPrefix)
    simpa [rightBlocks, render_gapBlocksList] using rightAbsent
  have leftRender :
      affineParityRender leftSegments =
        (canonicalWord identity.lhs).toList.reverse := by
    rw [show leftSegments = canonicalSegments final leftBlocks by rfl,
      render_canonicalSegments, canonicalWord_toList]
    simp [leftBlocks, leftPrefix, canonicalPrefix, leftFinal]
  have rightRender :
      affineParityRender rightSegments =
        (canonicalWord identity.rhs).toList.reverse := by
    rw [show rightSegments = canonicalSegments final rightBlocks by rfl,
      render_canonicalSegments, canonicalWord_toList]
    simp [rightBlocks, rightPrefix, canonicalPrefix, rightFinal]
  have canonicalJValid :
      (canonicalIdentity identity).SatisfiedBy
        Generated.S3_6.table.semigroup :=
    canonicalIdentity_valid Generated.S3_6.table.semigroup
      jModelsBasis identity jValid
  have canonicalOValid :
      (canonicalIdentity identity).SatisfiedBy
        Generated.S4_96.table.semigroup.opposite :=
    canonicalIdentity_valid
      Generated.S4_96.table.semigroup.opposite
      oModelsBasis identity oValid
  have canonicalSignature :=
    joinSignature_eq_of_factors
      (canonicalIdentity identity) canonicalJValid canonicalOValid
  have totalCoordinates :=
    congrArg JoinSignature.totalParity canonicalSignature
  have totalParity : ∀ tested,
      (affineParityRender leftSegments).count tested % 2 =
        (affineParityRender rightSegments).count tested % 2 := by
    intro tested
    have coordinate := congrFun totalCoordinates tested
    change
      (canonicalWord identity.lhs).toList.count tested % 2 =
        (canonicalWord identity.rhs).toList.count tested % 2 at coordinate
    rw [leftRender, rightRender]
    simpa using coordinate
  have pairCoordinates :=
    congrArg JoinSignature.pairParity canonicalSignature
  have suffixParity : ∀ tested marker, tested ≠ marker →
      affineParitySuffixParity tested marker
          (affineParityRender leftSegments) =
        affineParitySuffixParity tested marker
          (affineParityRender rightSegments) := by
    intro tested marker different
    have coordinate :=
      congrFun (congrFun pairCoordinates tested) marker
    change
      pairParity (canonicalWord identity.lhs) tested marker =
        pairParity (canonicalWord identity.rhs) tested marker at coordinate
    rw [leftRender, rightRender]
    simpa [pairParity, different] using coordinate
  have segmentPermutation :=
    affineParitySegmentsPerm_of_invariants
      leftNormal rightNormal segmentMarkers totalParity suffixParity
  have segmentEqual : leftSegments = rightSegments :=
    affineParitySegments_eq_of_perm_and_reverse_sorted
      segmentPermutation
      (canonicalSegments_reverse_sorted final leftBlocks)
      (canonicalSegments_reverse_sorted final rightBlocks)
  have renderedEqual := congrArg affineParityRender segmentEqual
  rw [leftRender, rightRender] at renderedEqual
  apply Word.toList_injective
  exact List.reverse_inj.mp renderedEqual

/-- Proposition 13.1 is complete for identities whose left final variable is
globally simple.  Validity in `J` forces the same simple final on the right. -/
theorem derives_of_factors_of_simpleFinal
    (identity : Identity Nat)
    (jValid : identity.SatisfiedBy Generated.S3_6.table.semigroup)
    (oValid :
      identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite)
    {final : Nat}
    (leftSimple :
      S5_345.simpleFinalVariable identity.lhs = some final) :
    Derives basis identity.lhs identity.rhs := by
  have canonicalEqual :=
    canonicalWord_eq_of_factors_of_simpleFinal
      identity jValid oValid leftSimple
  exact (derivesCanonicalWord identity.lhs).trans <| by
    rw [canonicalEqual]
    exact (derivesCanonicalWord identity.rhs).symm

end SemigroupBasis.CoRoots.Order6SporadicSection13
