import SemigroupBasis.CoRoots.Order6S6_14897AffineInvariants
import SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupNormalForm
import SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupSyntax
import SemigroupBasis.CoRoots.Order6S6_14897Subdirect

namespace SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupSemantics

open SemigroupBasis
open SemigroupBasis.Examples

theorem leftFactor_models :
    Models affineParityFour.semigroup
      SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.basis := by
  intro identity member
  exact
    (SemigroupBasis.CoRoots.Order6S6_14897Subdirect.ontoLeft).pushforwardIdentity
      identity
      (SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.basis_models
        identity member)

theorem rightFactor_models :
    Models affineParityFour.semigroup.opposite
      SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.basis := by
  intro identity member
  exact
    (SemigroupBasis.CoRoots.Order6S6_14897Subdirect.ontoRight).pushforwardIdentity
      identity
      (SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.basis_models
        identity member)

theorem forwardSegmentsPerm_of_left_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy affineParityFour.semigroup) :
    AffineParitySegmentsPerm
      (affineParityNormalSegments identity.lhs.toList)
      (affineParityNormalSegments identity.rhs.toList) :=
  SemigroupBasis.CoRoots.Order6S6_14897AffineInvariants.affineParityNormalSegmentsPerm_of_valid
    identity valid

theorem reversedSegmentsPerm_of_right_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy affineParityFour.semigroup.opposite) :
    AffineParitySegmentsPerm
      (affineParityNormalSegments identity.lhs.reverse.toList)
      (affineParityNormalSegments identity.rhs.reverse.toList) := by
  have reversedValid :
      identity.reversed.SatisfiedBy affineParityFour.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity affineParityFour.semigroup).mp valid
  simpa [Identity.reversed] using
    SemigroupBasis.CoRoots.Order6S6_14897AffineInvariants.affineParityNormalSegmentsPerm_of_valid
      identity.reversed reversedValid

theorem markers_eq_of_segmentsPerm
    {left right : List AffineParitySegment}
    (permutation : AffineParitySegmentsPerm left right) :
    affineParityMarkers left = affineParityMarkers right := by
  induction permutation with
  | nil =>
      rfl
  | cons _ _ induction =>
      simp [affineParityMarkers, induction]

theorem lastOccurrenceSequence_eq_of_left_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy affineParityFour.semigroup) :
    SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence identity.lhs.toList =
      SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence
        identity.rhs.toList := by
  have markers :=
    markers_eq_of_segmentsPerm
      (forwardSegmentsPerm_of_left_valid identity valid)
  change
    SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.affineBarrierSequence
        identity.lhs.toList =
      SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.affineBarrierSequence
        identity.rhs.toList at markers
  simpa only
    [SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.affineBarrierSequence_eq_lastOccurrenceSequence]
    using markers

theorem firstOccurrenceSequence_eq_of_right_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy affineParityFour.semigroup.opposite) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList := by
  have markers :=
    markers_eq_of_segmentsPerm
      (reversedSegmentsPerm_of_right_valid identity valid)
  simp only [Word.toList_reverse] at markers
  change
    SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.affineBarrierSequence
        identity.lhs.toList.reverse =
      SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.affineBarrierSequence
        identity.rhs.toList.reverse at markers
  have reversedLast :
      SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence
          identity.lhs.toList.reverse =
        SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence
          identity.rhs.toList.reverse := by
    simpa only
      [SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.affineBarrierSequence_eq_lastOccurrenceSequence]
      using markers
  have reversedFirst :
      (firstOccurrenceSequence identity.lhs.toList).reverse =
        (firstOccurrenceSequence identity.rhs.toList).reverse := by
    simpa [
      SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence]
      using reversedLast
  have restored := congrArg List.reverse reversedFirst
  simpa using restored

theorem parityReduce_perm_of_left_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy affineParityFour.semigroup) :
    (parityReduce identity.lhs.toList).Perm
      (parityReduce identity.rhs.toList) :=
  parityReduce_perm_of_parity_eq
    (affineParityValid_totalParity identity valid)

/-- A target-valid identity has matching affine segment profiles from both
directions. The first coordinate records suffix barriers; the opposite
coordinate records prefix barriers after word reversal. -/
theorem bidirectionalSegmentsPerm_of_target_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.table.semigroup) :
    And
      (AffineParitySegmentsPerm
        (affineParityNormalSegments identity.lhs.toList)
        (affineParityNormalSegments identity.rhs.toList))
      (AffineParitySegmentsPerm
        (affineParityNormalSegments identity.lhs.reverse.toList)
        (affineParityNormalSegments identity.rhs.reverse.toList)) := by
  have factorValid :=
    (SemigroupBasis.CoRoots.Order6S6_14897Subdirect.subdirectPair.satisfiedBy_iff
      identity).mp valid
  exact
    And.intro
      (forwardSegmentsPerm_of_left_valid identity factorValid.1)
      (reversedSegmentsPerm_of_right_valid identity factorValid.2)

/-- A useful coarse corollary of the full bidirectional segment signature.
First occurrences, last occurrences, and total parity determine support and
the middle block, but the segment permutations above are still required for
the two outer affine blocks. -/
theorem sequenceParitySignature_of_target_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.table.semigroup) :
    And
      (firstOccurrenceSequence identity.lhs.toList =
        firstOccurrenceSequence identity.rhs.toList)
      (And
        (SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence
            identity.lhs.toList =
          SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence
            identity.rhs.toList)
        ((parityReduce identity.lhs.toList).Perm
          (parityReduce identity.rhs.toList))) := by
  have factorValid :=
    (SemigroupBasis.CoRoots.Order6S6_14897Subdirect.subdirectPair.satisfiedBy_iff
      identity).mp valid
  exact
    And.intro
      (firstOccurrenceSequence_eq_of_right_valid
        identity factorValid.2)
      (And.intro
        (lastOccurrenceSequence_eq_of_left_valid
          identity factorValid.1)
        (parityReduce_perm_of_left_valid
          identity factorValid.1))

end SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupSemantics
