import SemigroupBasis.CoRoots.S5_415MinimalCounterexample
import SemigroupBasis.CoRoots.S5_415Completeness
import SemigroupBasis.CoRoots.S5_415TermModelSeparation

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-- Every right Schutzenberger quotient at a regular element of the presented
term semigroup satisfies every identity of the catalogue Brandt semigroup. -/
def RightSchutzenbergerBrandtValidity : Prop :=
  forall z : TermSemigroup basis,
    (termSemigroup basis).IsRegular z ->
      forall identity : Identity Nat,
        identity.SatisfiedBy
            Generated.Catalogue.S5_415.table.semigroup ->
          identity.SatisfiedBy
            (Semigroup.rightSchutzenbergerCongruence
              (termSemigroup basis) z).quotientSemigroup

/-- The regular right-Schutzenberger quotient validity statement closes the
published minimal-counterexample reduction. -/
theorem derivationalCompleteness_of_rightSchutzenbergerBrandtValidity
    (quotientValidity : RightSchutzenbergerBrandtValidity) :
    BrandtDerivationalCompleteness := by
  classical
  intro left right same
  have completeAtSupport :
      forall bound left right,
        brandtSupportCard left = bound ->
          SameBrandtSignature left right ->
            Derives basis left right := by
    intro bound
    induction bound using Nat.strongRecOn
    rename_i currentBound induction
    intro currentLeft currentRight supportEq currentSame
    apply Decidable.byContradiction
    intro notDerivable
    have smallerDerivable :
        forall {smallerLeft smallerRight : Word Nat},
          SameBrandtSignature smallerLeft smallerRight ->
            brandtSupportCard smallerLeft <
                brandtSupportCard currentLeft ->
              Derives basis smallerLeft smallerRight := by
      intro smallerLeft smallerRight smallerSame smallerSupport
      have smallerSupport' :
          brandtSupportCard smallerLeft < currentBound := by
        simpa [supportEq] using smallerSupport
      exact induction (brandtSupportCard smallerLeft) smallerSupport'
        smallerLeft smallerRight rfl smallerSame
    obtain ⟨leftRepeated, rightRepeated⟩ :=
      minimalCounterexample_repeated currentSame notDerivable
        smallerDerivable
    have tableValid :
        (⟨currentLeft, currentRight⟩ : Identity Nat).SatisfiedBy
          Generated.Catalogue.S5_415.table.semigroup :=
      valid_of_sameBrandtSignature currentSame
    rcases distinctRepeatedTermClasses_projection_separation
        leftRepeated rightRepeated notDerivable with
      leftSeparated | rightSeparated
    · let projection :=
        (Semigroup.rightSchutzenbergerCongruence
          (termSemigroup basis)
          (termClass basis currentLeft)).projection
      have evaluated :=
        quotientValidity (termClass basis currentLeft)
          (repeatedTermClass_isRegular leftRepeated)
          (⟨currentLeft, currentRight⟩ : Identity Nat) tableValid
          (fun letter =>
            projection.toFun
              (termClass basis (Word.singleton letter)))
      apply leftSeparated
      calc
        projection.toFun (termClass basis currentLeft) =
            projection.toFun
              ((termSemigroup basis).eval
                (fun letter =>
                  termClass basis (Word.singleton letter))
                currentLeft) := by
          rw [termSemigroup_eval_singletonClass]
        _ =
            (Semigroup.rightSchutzenbergerCongruence
              (termSemigroup basis)
              (termClass basis currentLeft)).quotientSemigroup.eval
                (fun letter =>
                  projection.toFun
                    (termClass basis (Word.singleton letter)))
                currentLeft :=
          projection.map_eval
            (fun letter => termClass basis (Word.singleton letter))
            currentLeft
        _ =
            (Semigroup.rightSchutzenbergerCongruence
              (termSemigroup basis)
              (termClass basis currentLeft)).quotientSemigroup.eval
                (fun letter =>
                  projection.toFun
                    (termClass basis (Word.singleton letter)))
                currentRight :=
          evaluated
        _ =
            projection.toFun
              ((termSemigroup basis).eval
                (fun letter =>
                  termClass basis (Word.singleton letter))
                currentRight) :=
          (projection.map_eval
            (fun letter => termClass basis (Word.singleton letter))
            currentRight).symm
        _ = projection.toFun (termClass basis currentRight) := by
          rw [termSemigroup_eval_singletonClass]
    · let projection :=
        (Semigroup.rightSchutzenbergerCongruence
          (termSemigroup basis)
          (termClass basis currentRight)).projection
      have evaluated :=
        quotientValidity (termClass basis currentRight)
          (repeatedTermClass_isRegular rightRepeated)
          (⟨currentLeft, currentRight⟩ : Identity Nat) tableValid
          (fun letter =>
            projection.toFun
              (termClass basis (Word.singleton letter)))
      apply rightSeparated
      calc
        projection.toFun (termClass basis currentLeft) =
            projection.toFun
              ((termSemigroup basis).eval
                (fun letter =>
                  termClass basis (Word.singleton letter))
                currentLeft) := by
          rw [termSemigroup_eval_singletonClass]
        _ =
            (Semigroup.rightSchutzenbergerCongruence
              (termSemigroup basis)
              (termClass basis currentRight)).quotientSemigroup.eval
                (fun letter =>
                  projection.toFun
                    (termClass basis (Word.singleton letter)))
                currentLeft :=
          projection.map_eval
            (fun letter => termClass basis (Word.singleton letter))
            currentLeft
        _ =
            (Semigroup.rightSchutzenbergerCongruence
              (termSemigroup basis)
              (termClass basis currentRight)).quotientSemigroup.eval
                (fun letter =>
                  projection.toFun
                    (termClass basis (Word.singleton letter)))
                currentRight :=
          evaluated
        _ =
            projection.toFun
              ((termSemigroup basis).eval
                (fun letter =>
                  termClass basis (Word.singleton letter))
                currentRight) :=
          (projection.map_eval
            (fun letter => termClass basis (Word.singleton letter))
            currentRight).symm
        _ = projection.toFun (termClass basis currentRight) := by
          rw [termSemigroup_eval_singletonClass]
  exact completeAtSupport
    (brandtSupportCard left) left right rfl same

end SemigroupBasis.CoRoots.S5_415
