import SemigroupBasis.CoRoots.S5_1146
import SemigroupBasis.CoRoots.S5_217
import SemigroupBasis.Examples.CommutativePeriodThreeFromTwoOrderFive
import SemigroupBasis.Examples.CommutativePeriodTwoFromThreeOrderFive
import SemigroupBasis.Examples.HeadSortedCappedFour
import SemigroupBasis.Examples.HeadSortedPeriodThreeFromTwo
import SemigroupBasis.Examples.HeadSortedPeriodTwoFromThree
import SemigroupBasis.Examples.LeftNormalBandFifteen
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6HeadSortedFactorIntersections

open SemigroupBasis
open SemigroupBasis.Examples

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem cappedFourExponent_eq_min (n : Nat) :
    headSortedCappedFourExponent n = min n 4 := by
  unfold headSortedCappedFourExponent
  by_cases below : n < 4
  · rw [if_pos below, Nat.min_eq_left (by omega)]
  · rw [if_neg below, Nat.min_eq_right (by omega)]

private theorem cappedFourSeparates
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.CoRoots.S5_217.table.semigroup) :
    ∀ letter,
      headSortedCappedFourExponent
          (identity.lhs.toList.count letter) =
        headSortedCappedFourExponent
          (identity.rhs.toList.count letter) := by
  intro letter
  rw [cappedFourExponent_eq_min, cappedFourExponent_eq_min]
  exact SemigroupBasis.CoRoots.S5_217.valid_capped_count
    identity valid letter

def cappedFourS3_13S5_217 :
    IntersectionBasis leftNormalBandThree.semigroup
      SemigroupBasis.CoRoots.S5_217.table.semigroup
      headSortedCappedFourBasis where
  leftModels := FiniteCertificate.checkModels_sound
    leftNormalBandThree headSortedCappedFourBasis toFinThree (by decide)
  rightModels := FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.S5_217.table headSortedCappedFourBasis
      toFinThree (by decide)
  complete := by
    intro identity leftValid rightValid
    exact headSortedCappedFourDerivesOfInvariantEq
      identity.lhs identity.rhs
      (leftNormalBandValid_head_eq identity leftValid)
      (cappedFourSeparates identity rightValid)

def cappedFourS3_15S5_217 :
    IntersectionBasis leftNormalBandFifteen.semigroup
      SemigroupBasis.CoRoots.S5_217.table.semigroup
      headSortedCappedFourBasis where
  leftModels := FiniteCertificate.checkModels_sound
    leftNormalBandFifteen headSortedCappedFourBasis toFinThree (by decide)
  rightModels := FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.S5_217.table headSortedCappedFourBasis
      toFinThree (by decide)
  complete := by
    intro identity leftValid rightValid
    exact headSortedCappedFourDerivesOfInvariantEq
      identity.lhs identity.rhs
      (leftNormalBandFifteenValid_head_eq identity leftValid)
      (cappedFourSeparates identity rightValid)

def indexThreePeriodTwoS3_15S5_223 :
    IntersectionBasis leftNormalBandFifteen.semigroup s5_223.semigroup
      headSortedPeriodTwoFromThreeBasis where
  leftModels := FiniteCertificate.checkModels_sound
    leftNormalBandFifteen headSortedPeriodTwoFromThreeBasis
      toFinThree (by decide)
  rightModels := FiniteCertificate.checkModels_sound
    s5_223 headSortedPeriodTwoFromThreeBasis toFinThree (by decide)
  complete := by
    intro identity leftValid rightValid
    exact headSortedPeriodTwoFromThreeDerivesOfInvariantEq
      identity.lhs identity.rhs
      (leftNormalBandFifteenValid_head_eq identity leftValid)
      (s5_223Separates identity rightValid)

def indexThreePeriodTwoS3_15S5_226 :
    IntersectionBasis leftNormalBandFifteen.semigroup s5_226.semigroup
      headSortedPeriodTwoFromThreeBasis where
  leftModels := FiniteCertificate.checkModels_sound
    leftNormalBandFifteen headSortedPeriodTwoFromThreeBasis
      toFinThree (by decide)
  rightModels := FiniteCertificate.checkModels_sound
    s5_226 headSortedPeriodTwoFromThreeBasis toFinThree (by decide)
  complete := by
    intro identity leftValid rightValid
    exact headSortedPeriodTwoFromThreeDerivesOfInvariantEq
      identity.lhs identity.rhs
      (leftNormalBandFifteenValid_head_eq identity leftValid)
      (s5_226Separates identity rightValid)

def indexThreePeriodTwoS3_13S5_514 :
    IntersectionBasis leftNormalBandThree.semigroup s5_514.semigroup
      headSortedPeriodTwoFromThreeBasis where
  leftModels := FiniteCertificate.checkModels_sound
    leftNormalBandThree headSortedPeriodTwoFromThreeBasis
      toFinThree (by decide)
  rightModels := FiniteCertificate.checkModels_sound
    s5_514 headSortedPeriodTwoFromThreeBasis toFinThree (by decide)
  complete := by
    intro identity leftValid rightValid
    exact headSortedPeriodTwoFromThreeDerivesOfInvariantEq
      identity.lhs identity.rhs
      (leftNormalBandValid_head_eq identity leftValid)
      (s5_514Separates identity rightValid)

def periodThreeS5_1146S5_1001 :
    IntersectionBasis
      SemigroupBasis.CoRoots.S5_1146.S5_1146.table.semigroup
      s5_1001.semigroup headSortedPeriodThreeFromTwoBasis where
  leftModels := FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.S5_1146.S5_1146.table
      headSortedPeriodThreeFromTwoBasis toFinThree (by decide)
  rightModels := FiniteCertificate.checkModels_sound
    s5_1001 headSortedPeriodThreeFromTwoBasis toFinThree (by decide)
  complete := by
    intro identity leftValid rightValid
    exact headSortedPeriodThreeFromTwoDerivesOfInvariantEq
      identity.lhs identity.rhs
      (SemigroupBasis.CoRoots.S5_1146.S5_1146.valid_head_eq
        identity leftValid)
      (s5_1001Separates identity rightValid)

def periodThreeS5_1152S5_1004 :
    IntersectionBasis
      SemigroupBasis.CoRoots.S5_1146.S5_1152.table.semigroup
      s5_1004.semigroup headSortedPeriodThreeFromTwoBasis where
  leftModels := FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.S5_1146.S5_1152.table
      headSortedPeriodThreeFromTwoBasis toFinThree (by decide)
  rightModels := FiniteCertificate.checkModels_sound
    s5_1004 headSortedPeriodThreeFromTwoBasis toFinThree (by decide)
  complete := by
    intro identity leftValid rightValid
    exact headSortedPeriodThreeFromTwoDerivesOfInvariantEq
      identity.lhs identity.rhs
      (SemigroupBasis.CoRoots.S5_1146.S5_1152.valid_head_eq
        identity leftValid)
      (s5_1004Separates identity rightValid)

def periodThreeS5_1152S5_1156 :
    IntersectionBasis
      SemigroupBasis.CoRoots.S5_1146.S5_1152.table.semigroup
      s5_1156.semigroup headSortedPeriodThreeFromTwoBasis where
  leftModels := FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.S5_1146.S5_1152.table
      headSortedPeriodThreeFromTwoBasis toFinThree (by decide)
  rightModels := FiniteCertificate.checkModels_sound
    s5_1156 headSortedPeriodThreeFromTwoBasis toFinThree (by decide)
  complete := by
    intro identity leftValid rightValid
    exact headSortedPeriodThreeFromTwoDerivesOfInvariantEq
      identity.lhs identity.rhs
      (SemigroupBasis.CoRoots.S5_1146.S5_1152.valid_head_eq
        identity leftValid)
      (s5_1156Separates identity rightValid)

end SemigroupBasis.CoRoots.Order6HeadSortedFactorIntersections
