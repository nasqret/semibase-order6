import SemigroupBasis.Examples.AffineParityFour

namespace SemigroupBasis.CoRoots.Order6S6_14897AffineInvariants

open SemigroupBasis
open SemigroupBasis.Examples

/-- Validity in `S4_96` determines its affine normal segments blockwise, up
to permutation. This exposes the semantic half of the affine completeness
proof for factor-intersection normalizers. -/
theorem affineParityNormalSegmentsPerm_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy affineParityFour.semigroup) :
    AffineParitySegmentsPerm
      (affineParityNormalSegments identity.lhs.toList)
      (affineParityNormalSegments identity.rhs.toList) := by
  have leftDerivation :=
    affineParityDerivesNormal identity.lhs
  have rightDerivation :=
    affineParityDerivesNormal identity.rhs
  have leftSegmentsNormal :=
    affineParityNormalSegments_normal identity.lhs.toList
  have rightSegmentsNormal :=
    affineParityNormalSegments_normal identity.rhs.toList
  cases leftEq :
      affineParityNormalSegments identity.lhs.toList with
  | nil =>
      exact False.elim <|
        affineParityNormalSegments_cons_ne_nil
          identity.lhs.head identity.lhs.tail (by
            simpa [Word.toList] using leftEq)
  | cons leftHead leftRest =>
      rw [leftEq] at leftDerivation leftSegmentsNormal
      cases rightEq :
          affineParityNormalSegments identity.rhs.toList with
      | nil =>
          exact False.elim <|
            affineParityNormalSegments_cons_ne_nil
              identity.rhs.head identity.rhs.tail (by
                simpa [Word.toList] using rightEq)
      | cons rightHead rightRest =>
          rw [rightEq] at rightDerivation rightSegmentsNormal
          have normalEval :
              ∀ valuation : Nat → Fin 4,
                affineParityListEval valuation
                    (affineParityRender (leftHead :: leftRest)) =
                  affineParityListEval valuation
                    (affineParityRender (rightHead :: rightRest)) := by
            intro valuation
            have leftSound :=
              leftDerivation.sound
                affineParityFourBasis_models valuation
            have rightSound :=
              rightDerivation.sound
                affineParityFourBasis_models valuation
            have evaluated :=
              leftSound.symm.trans <|
                (valid valuation).trans rightSound
            rw [affineParityEval_eq_listEval,
              affineParityEval_eq_listEval,
              affineParityRenderWord_toList,
              affineParityRenderWord_toList] at evaluated
            exact evaluated
          have markerEq :=
            affineParityMarkers_eq_of_eval_eq
              leftSegmentsNormal rightSegmentsNormal normalEval
          have totalParity :
              ∀ tested,
                (affineParityRender
                    (leftHead :: leftRest)).count tested % 2 =
                  (affineParityRender
                    (rightHead :: rightRest)).count tested % 2 := by
            intro tested
            have evaluated :=
              normalEval (affineParityTotalValuation tested)
            have bitEquality :=
              congrArg affineParityTranslationBit evaluated
            simpa [affineParityListEval_total_bit] using bitEquality
          have suffixParity :
              ∀ tested marker, tested ≠ marker →
                affineParitySuffixParity tested marker
                    (affineParityRender (leftHead :: leftRest)) =
                  affineParitySuffixParity tested marker
                    (affineParityRender (rightHead :: rightRest)) := by
            intro tested marker different
            have evaluated :=
              normalEval
                (affineParitySuffixValuation tested marker)
            have bitEquality :=
              congrArg affineParityTranslationBit evaluated
            simpa [affineParityListEval_suffix_bit] using bitEquality
          exact affineParitySegmentsPerm_of_invariants
            leftSegmentsNormal rightSegmentsNormal markerEq
            totalParity suffixParity

end SemigroupBasis.CoRoots.Order6S6_14897AffineInvariants
