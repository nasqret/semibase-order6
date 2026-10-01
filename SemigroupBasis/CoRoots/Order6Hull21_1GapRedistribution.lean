import SemigroupBasis.CoRoots.Order6Hull21_1SweepReadiness

/-!
# Hull 21.1 gap redistribution

This module closes the constructive block-redistribution stage of the
Hull 21.1 joint normalizer.  The parser view exposes either literal equality
or a final nonempty gap.  In the active case, boundary-anchor preparation is
followed by the already verified forward sweep over the blocks strictly
between the anchor block and the final nonempty gap.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull21_1GapRedistribution

open Order6Hull21_1BlockFacts
open Order6Hull21_1BoundaryAnchor
open Order6Hull21_1ForwardSweep
open Order6Hull21_1ProfileCountNormalization
open Order6Hull21_1SweepReadiness

abbrev GapBlock :=
  SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock

abbrev HullListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.HullListDerives

/-- The block-level Lee--Zhang redistribution required by the joint
profile-count normalizer. -/
theorem blockGapRedistribution :
    BlockGapRedistribution := by
  intro blocks formed _
  have view := sweptCoreView formed
  cases view with
  | same sourceTargetShape =>
      rw [← sourceTargetShape]
      exact
        SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis :=
            SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.publishedBasis)
          _
  | active simpleBlocks anchorBlock beforeFinal lastBlock suffixBlocks
      blocksShape anchorPosition simpleWellFormed activeWellFormed
      simpleSecondsEmpty lastNonempty suffixSecondsEmpty sourceShape
      targetShape finalDebtWitnessed boundaryAnchorAvailable
      historicalCoverage =>
      have boundaryPrepared :=
        hullListDerivesPrepareBoundaryAnchor
          (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
            SemigroupBasis.CoRoots.S5_870.renderGapBlocks beforeFinal ++
            [lastBlock.marker])
          lastBlock.seconds
          (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers suffixBlocks)
          anchorBlock.marker
          lastNonempty finalDebtWitnessed boundaryAnchorAvailable
      rw [targetShape, sourceShape]
      rcases anchorPosition with
        ⟨beforeEmpty, lastIsAnchor⟩ |
          ⟨remainingBeforeFinal, beforeShape⟩
      · subst beforeFinal
        subst lastBlock
        simpa [renderSweptCorePrefix,
          SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
          SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
          List.append_assoc] using boundaryPrepared
      · subst beforeFinal
        have activeWellFormedAssoc :
            SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed
              (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                simpleBlocks).reverse
              ((anchorBlock :: remainingBeforeFinal) ++
                (lastBlock :: suffixBlocks)) := by
          simpa [List.append_assoc] using activeWellFormed
        obtain ⟨beforeWellFormed, _⟩ :=
          gapBlocksWellFormed_append activeWellFormedAssoc
        have anchorSecondsSeen :
            ∀ letter, letter ∈ anchorBlock.seconds →
              letter ∈
                anchorBlock.marker ::
                  (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                    simpleBlocks).reverse := by
          cases beforeWellFormed with
          | cons _ _ _ _ secondsSeen _ =>
              exact secondsSeen
        have remainingWellFormed :
            SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed
              (anchorBlock.marker ::
                (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                  simpleBlocks).reverse)
              remainingBeforeFinal := by
          cases beforeWellFormed with
          | cons _ _ _ _ _ tail =>
              exact tail
        have prefixSecondsInActive :
            ∀ {letter},
              letter ∈
                  SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                    (anchorBlock :: remainingBeforeFinal) →
                letter ∈
                  SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                    ((anchorBlock :: remainingBeforeFinal) ++
                      [lastBlock] ++ suffixBlocks) := by
          intro letter member
          rw [List.append_assoc]
          rw [gapBlockSeconds_append
            (anchorBlock :: remainingBeforeFinal)
            ([lastBlock] ++ suffixBlocks)]
          exact List.mem_append.mpr (Or.inl member)
        have anchorSecondsInActive :
            ∀ {letter}, letter ∈ anchorBlock.seconds →
              letter ∈
                SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                  ((anchorBlock :: remainingBeforeFinal) ++
                    [lastBlock] ++ suffixBlocks) := by
          intro letter member
          apply prefixSecondsInActive
          simp only [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
            List.flatMap_cons, List.mem_append]
          exact Or.inl member
        have remainingSecondsInActive :
            ∀ {letter},
              letter ∈
                  SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                    remainingBeforeFinal →
                letter ∈
                  SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                    ((anchorBlock :: remainingBeforeFinal) ++
                      [lastBlock] ++ suffixBlocks) := by
          intro letter member
          apply prefixSecondsInActive
          simp only [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
            List.flatMap_cons, List.mem_append]
          exact Or.inr member
        have anchorGapOld :
            ∀ letter, letter ∈ anchorBlock.seconds →
              letter ∈ anchorBlock.marker :: [] := by
          intro letter member
          have inHistory := anchorSecondsSeen letter member
          have equalAnchor :=
            historicalCoverage letter inHistory
              (anchorSecondsInActive member)
          subst letter
          simp
        have remainingReady :
            ∀ dynamic : List Nat,
              ForwardSweepReady anchorBlock.marker dynamic
                remainingBeforeFinal := by
          intro dynamic
          apply forwardSweepReady_of_wellFormed remainingWellFormed
          intro letter inHistory inRemainingSeconds
          have equalAnchor :=
            historicalCoverage letter inHistory
              (remainingSecondsInActive inRemainingSeconds)
          subst letter
          simp
        by_cases anchorGapEmpty : anchorBlock.seconds = []
        · have sweepRemaining :=
            hullListDerivesForwardSweepReverse
              (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks)
              anchorBlock.marker lastBlock.marker
              (lastBlock.seconds ++
                SemigroupBasis.CoRoots.S5_870.gapBlockMarkers suffixBlocks)
              (remainingReady [])
          have preparedForSweep :
              HullListDerives
                (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
                  SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                    (anchorBlock :: remainingBeforeFinal) ++
                  [lastBlock.marker] ++ lastBlock.seconds ++
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers suffixBlocks)
                (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
                  [anchorBlock.marker] ++ [] ++
                  SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                    remainingBeforeFinal ++
                  [lastBlock.marker, anchorBlock.marker] ++
                  lastBlock.seconds ++
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                    suffixBlocks) := by
            simpa [SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
              anchorGapEmpty, List.append_assoc] using boundaryPrepared
          have sweepRemaining' :
              HullListDerives
                (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
                  [anchorBlock.marker] ++ [] ++
                  SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                    remainingBeforeFinal ++
                  [lastBlock.marker, anchorBlock.marker] ++
                  lastBlock.seconds ++
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                    suffixBlocks)
                (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
                  [anchorBlock.marker] ++ [] ++
                  renderSweptCorePrefix anchorBlock.marker
                    remainingBeforeFinal ++
                  [lastBlock.marker, anchorBlock.marker] ++
                  reverseBlockDebt remainingBeforeFinal ++
                  lastBlock.seconds ++
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                    suffixBlocks) := by
            simpa [List.append_assoc] using sweepRemaining
          simpa [renderSweptCorePrefix, reverseBlockDebt,
            SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
            List.flatMap_append, List.reverse_cons, anchorGapEmpty,
            List.append_assoc] using
              preparedForSweep.trans sweepRemaining'
        · have moveAnchorGap :=
            hullListDerivesMoveSeenGapToDebt
              (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks)
              (lastBlock.seconds ++
                SemigroupBasis.CoRoots.S5_870.gapBlockMarkers suffixBlocks)
              []
              (SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                remainingBeforeFinal ++ [lastBlock.marker])
              anchorBlock.seconds anchorBlock.marker
              anchorGapEmpty anchorGapOld
          have movedForSweep :
              HullListDerives
                (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
                  SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                    (anchorBlock :: remainingBeforeFinal) ++
                  [lastBlock.marker] ++ [anchorBlock.marker] ++
                  lastBlock.seconds ++
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers suffixBlocks)
                (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
                  [anchorBlock.marker] ++ [anchorBlock.marker] ++
                  SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                    remainingBeforeFinal ++
                  [lastBlock.marker, anchorBlock.marker] ++
                  anchorBlock.seconds ++ lastBlock.seconds ++
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                    suffixBlocks) := by
            simpa [SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
              List.append_assoc] using moveAnchorGap
          have preparedForSweep :
              HullListDerives
                (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
                  SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                    (anchorBlock :: remainingBeforeFinal) ++
                  [lastBlock.marker] ++ lastBlock.seconds ++
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers suffixBlocks)
                (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
                  [anchorBlock.marker] ++ [anchorBlock.marker] ++
                  SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                    remainingBeforeFinal ++
                  [lastBlock.marker, anchorBlock.marker] ++
                  anchorBlock.seconds ++ lastBlock.seconds ++
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                    suffixBlocks) := by
            have boundaryThenMove :=
              boundaryPrepared.trans movedForSweep
            simpa [SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
              List.append_assoc] using boundaryThenMove
          have sweepRemaining :=
            hullListDerivesForwardSweepReverse
              (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks)
              anchorBlock.marker lastBlock.marker
              (anchorBlock.seconds ++ lastBlock.seconds ++
                SemigroupBasis.CoRoots.S5_870.gapBlockMarkers suffixBlocks)
              (remainingReady [anchorBlock.marker])
          have sweepRemaining' :
              HullListDerives
                (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
                  [anchorBlock.marker] ++ [anchorBlock.marker] ++
                  SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                    remainingBeforeFinal ++
                  [lastBlock.marker, anchorBlock.marker] ++
                  anchorBlock.seconds ++ lastBlock.seconds ++
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                    suffixBlocks)
                (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
                  [anchorBlock.marker] ++ [anchorBlock.marker] ++
                  renderSweptCorePrefix anchorBlock.marker
                    remainingBeforeFinal ++
                  [lastBlock.marker, anchorBlock.marker] ++
                  reverseBlockDebt remainingBeforeFinal ++
                  anchorBlock.seconds ++ lastBlock.seconds ++
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                    suffixBlocks) := by
            simpa [List.append_assoc] using sweepRemaining
          simpa [renderSweptCorePrefix, reverseBlockDebt,
            SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
            List.flatMap_append, List.reverse_cons, anchorGapEmpty,
            List.append_assoc] using
              preparedForSweep.trans sweepRemaining'

/-- Unconditional profile-count normalization for the Hull 21.1 basis. -/
theorem profileCountNormalization :
    SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.ProfileCountNormalization :=
  profileCountNormalization_of_block_sweeps
    blockGapRedistribution blockFinalDebtNormalization

/-- Complete derivational obligation for the `S5_831 × S3_8` hull. -/
theorem h831DerivationalObligation :
    SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.DerivationalObligation :=
  SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.h831DerivationalObligation_of_profileCountNormalization
    profileCountNormalization

/-- Complete derivational obligation for the sibling `S5_832 × S3_8` hull. -/
theorem h832DerivationalObligation :
    SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.DerivationalObligation :=
  SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.h832DerivationalObligation_of_profileCountNormalization
    profileCountNormalization

/-- Unconditional intersection-basis package for `S5_831 × S3_8`. -/
def h831IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.G
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.H
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.publishedBasis :=
  SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.h831IntersectionBasis_of_profileCountNormalization
    profileCountNormalization

/-- Unconditional intersection-basis package for `S5_832 × S3_8`. -/
def h832IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.G
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.H
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.publishedBasis :=
  SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.h832IntersectionBasis_of_profileCountNormalization
    profileCountNormalization

/-- Complete basis for the first product hull. -/
theorem h831ProductBasisFor :
    BasisFor
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.P
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.publishedBasis :=
  SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.h831ProductBasisFor_of_profileCountNormalization
    profileCountNormalization

/-- Complete basis for the sibling product hull. -/
theorem h832ProductBasisFor :
    BasisFor
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.P
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.publishedBasis :=
  SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.h832ProductBasisFor_of_profileCountNormalization
    profileCountNormalization

#print axioms blockGapRedistribution
#print axioms profileCountNormalization
#print axioms h831ProductBasisFor
#print axioms h832ProductBasisFor

end Order6Hull21_1GapRedistribution
end CoRoots
end SemigroupBasis
