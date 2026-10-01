import SemigroupBasis.CoRoots.Order6SporadicSection11
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.Examples.CommutativeExponentFour

namespace SemigroupBasis.CoRoots.Order6SporadicSection11

open SemigroupBasis
open SemigroupBasis.Examples

private theorem signature_ext
    {left right : Signature}
    (firstOccurrences : left.firstOccurrences = right.firstOccurrences)
    (cappedCounts : left.cappedCounts = right.cappedCounts)
    (terminal : left.terminal = right.terminal) :
    left = right := by
  cases left
  cases right
  simp_all

/-- The three published factors recover every field of the Section 11
signature. -/
theorem signature_eq_of_factor_semantics
    (identity : Identity Nat)
    (firstOccurrencesValid :
      identity.SatisfiedBy leftRegularBandThree.semigroup)
    (cappedCountsValid :
      identity.SatisfiedBy commutativeExponentFour.semigroup)
    (terminalValid :
      identity.SatisfiedBy finalMarkerThree.semigroup) :
    signature identity.lhs = signature identity.rhs := by
  apply signature_ext
  · change
      firstOccurrenceSequenceList identity.lhs.toList =
        firstOccurrenceSequenceList identity.rhs.toList
    simpa [firstOccurrenceSequenceList] using
      S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
        identity firstOccurrencesValid
  · change
      cappedCountsList identity.lhs.toList =
        cappedCountsList identity.rhs.toList
    unfold cappedCountsList
    have firstOccurrences :
        firstOccurrenceSequenceList identity.lhs.toList =
          firstOccurrenceSequenceList identity.rhs.toList := by
      simpa [firstOccurrenceSequenceList] using
        S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
          identity firstOccurrencesValid
    rw [firstOccurrences]
    apply List.map_congr_left
    intro letter _
    exact exponentFourValid_capped_count_eq
      identity cappedCountsValid letter
  · change
      terminalStatusOfOption
          (SemigroupBasis.CoRoots.S5_345.simpleFinalVariable identity.lhs) =
        terminalStatusOfOption
          (SemigroupBasis.CoRoots.S5_345.simpleFinalVariable identity.rhs)
    exact congrArg terminalStatusOfOption <|
      S5_345Factors.finalMarkerThreeValid_simpleFinalVariable_eq
        identity terminalValid

namespace S6_5614

def finalMarkerQuotient :
    SplitSurjection table.semigroup finalMarkerThree.semigroup where
  toFun := fun (a : Fin 6) => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun (b : Fin 3) => if b = 0 then (0 : Fin 6) else if b = 1 then (2 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

def leftRegularBandQuotient :
    SplitSurjection table.semigroup leftRegularBandThree.semigroup where
  toFun := fun (a : Fin 6) => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (2 : Fin 3) else (1 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun (b : Fin 3) => if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else (4 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

def commutativeExponentQuotient :
    SplitSurjection table.semigroup commutativeExponentFour.semigroup where
  toFun := fun (a : Fin 6) => if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (0 : Fin 4) else (3 : Fin 4)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun (b : Fin 4) => if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_finalMarkerThree
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy finalMarkerThree.semigroup :=
  finalMarkerQuotient.pushforwardIdentity identity valid

theorem valid_leftRegularBandThree
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy leftRegularBandThree.semigroup :=
  leftRegularBandQuotient.pushforwardIdentity identity valid

theorem valid_commutativeExponentFour
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy commutativeExponentFour.semigroup :=
  commutativeExponentQuotient.pushforwardIdentity identity valid

theorem signatureSeparation : SignatureSeparation table where
  separate := by
    intro identity valid
    exact signature_eq_of_factor_semantics identity
      (valid_leftRegularBandThree identity valid)
      (valid_commutativeExponentFour identity valid)
      (valid_finalMarkerThree identity valid)

theorem basisFor_of_completeness
    (completeness : SignatureDerivationCompleteness) :
    BasisFor table.semigroup basis :=
  basisFor_of_obligations signatureSeparation completeness

theorem oppositeBasisFor_of_completeness
    (completeness : SignatureDerivationCompleteness) :
    BasisFor table.semigroup.opposite oppositeBasis :=
  oppositeBasisFor_of_obligations signatureSeparation completeness

end S6_5614

namespace S6_9582

def finalMarkerQuotient :
    SplitSurjection table.semigroup finalMarkerThree.semigroup where
  toFun := fun (a : Fin 6) => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (1 : Fin 3) else (2 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun (b : Fin 3) => if b = 0 then (0 : Fin 6) else if b = 1 then (4 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

def leftRegularBandQuotient :
    SplitSurjection table.semigroup leftRegularBandThree.semigroup where
  toFun := fun (a : Fin 6) => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (2 : Fin 3) else if a = 4 then (2 : Fin 3) else (1 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun (b : Fin 3) => if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else (3 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

def commutativeExponentQuotient :
    SplitSurjection table.semigroup commutativeExponentFour.semigroup where
  toFun := fun (a : Fin 6) => if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (2 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (0 : Fin 4) else (3 : Fin 4)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun (b : Fin 4) => if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_finalMarkerThree
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy finalMarkerThree.semigroup :=
  finalMarkerQuotient.pushforwardIdentity identity valid

theorem valid_leftRegularBandThree
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy leftRegularBandThree.semigroup :=
  leftRegularBandQuotient.pushforwardIdentity identity valid

theorem valid_commutativeExponentFour
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy commutativeExponentFour.semigroup :=
  commutativeExponentQuotient.pushforwardIdentity identity valid

theorem signatureSeparation : SignatureSeparation table where
  separate := by
    intro identity valid
    exact signature_eq_of_factor_semantics identity
      (valid_leftRegularBandThree identity valid)
      (valid_commutativeExponentFour identity valid)
      (valid_finalMarkerThree identity valid)

theorem basisFor_of_completeness
    (completeness : SignatureDerivationCompleteness) :
    BasisFor table.semigroup basis :=
  basisFor_of_obligations signatureSeparation completeness

theorem oppositeBasisFor_of_completeness
    (completeness : SignatureDerivationCompleteness) :
    BasisFor table.semigroup.opposite oppositeBasis :=
  oppositeBasisFor_of_obligations signatureSeparation completeness

end S6_9582

namespace S6_5622

def finalMarkerQuotient :
    SplitSurjection table.semigroup finalMarkerThree.semigroup where
  toFun := fun (a : Fin 6) => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun (b : Fin 3) => if b = 0 then (0 : Fin 6) else if b = 1 then (2 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

def leftRegularBandQuotient :
    SplitSurjection table.semigroup leftRegularBandThree.semigroup where
  toFun := fun (a : Fin 6) => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (2 : Fin 3) else (1 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun (b : Fin 3) => if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else (4 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

def commutativeExponentQuotient :
    SplitSurjection table.semigroup commutativeExponentFour.semigroup where
  toFun := fun (a : Fin 6) => if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (0 : Fin 4) else (3 : Fin 4)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun (b : Fin 4) => if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_finalMarkerThree
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy finalMarkerThree.semigroup :=
  finalMarkerQuotient.pushforwardIdentity identity valid

theorem valid_leftRegularBandThree
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy leftRegularBandThree.semigroup :=
  leftRegularBandQuotient.pushforwardIdentity identity valid

theorem valid_commutativeExponentFour
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy commutativeExponentFour.semigroup :=
  commutativeExponentQuotient.pushforwardIdentity identity valid

theorem signatureSeparation : SignatureSeparation table where
  separate := by
    intro identity valid
    exact signature_eq_of_factor_semantics identity
      (valid_leftRegularBandThree identity valid)
      (valid_commutativeExponentFour identity valid)
      (valid_finalMarkerThree identity valid)

theorem basisFor_of_completeness
    (completeness : SignatureDerivationCompleteness) :
    BasisFor table.semigroup basis :=
  basisFor_of_obligations signatureSeparation completeness

theorem oppositeBasisFor_of_completeness
    (completeness : SignatureDerivationCompleteness) :
    BasisFor table.semigroup.opposite oppositeBasis :=
  oppositeBasisFor_of_obligations signatureSeparation completeness

end S6_5622

namespace S6_9451

def finalMarkerQuotient :
    SplitSurjection table.semigroup finalMarkerThree.semigroup where
  toFun := fun (a : Fin 6) => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun (b : Fin 3) => if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

def leftRegularBandQuotient :
    SplitSurjection table.semigroup leftRegularBandThree.semigroup where
  toFun := fun (a : Fin 6) => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (2 : Fin 3) else (1 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun (b : Fin 3) => if b = 0 then (0 : Fin 6) else if b = 1 then (5 : Fin 6) else (4 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

def commutativeExponentQuotient :
    SplitSurjection table.semigroup commutativeExponentFour.semigroup where
  toFun := fun (a : Fin 6) => if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (2 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (0 : Fin 4) else (3 : Fin 4)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun (b : Fin 4) => if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_finalMarkerThree
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy finalMarkerThree.semigroup :=
  finalMarkerQuotient.pushforwardIdentity identity valid

theorem valid_leftRegularBandThree
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy leftRegularBandThree.semigroup :=
  leftRegularBandQuotient.pushforwardIdentity identity valid

theorem valid_commutativeExponentFour
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy commutativeExponentFour.semigroup :=
  commutativeExponentQuotient.pushforwardIdentity identity valid

theorem signatureSeparation : SignatureSeparation table where
  separate := by
    intro identity valid
    exact signature_eq_of_factor_semantics identity
      (valid_leftRegularBandThree identity valid)
      (valid_commutativeExponentFour identity valid)
      (valid_finalMarkerThree identity valid)

theorem basisFor_of_completeness
    (completeness : SignatureDerivationCompleteness) :
    BasisFor table.semigroup basis :=
  basisFor_of_obligations signatureSeparation completeness

theorem oppositeBasisFor_of_completeness
    (completeness : SignatureDerivationCompleteness) :
    BasisFor table.semigroup.opposite oppositeBasis :=
  oppositeBasisFor_of_obligations signatureSeparation completeness

end S6_9451

end SemigroupBasis.CoRoots.Order6SporadicSection11
