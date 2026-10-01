import SemigroupBasis.CoRoots.S5_415SchutzenbergerStructure
import SemigroupBasis.SchutzenbergerImage
import SemigroupBasis.StableRegularity
import SemigroupBasis.ZeroSimple

namespace SemigroupBasis
namespace Semigroup

/-- Surjectivity from the principal sandwich makes the right Schutzenberger
quotient zero-simple. A nonzero source class cannot be represented by an
element of `I_z`; hence `z` lies in its principal sandwich. Composing this
factorization with a principal representative of the target gives the
required quotient factorization. -/
theorem rightSchutzenbergerQuotient_zeroSimple_of_imageCondition
    {G : Semigroup S} {z : S}
    (imageCondition : G.RightSchutzenbergerImageCondition z) :
    (rightSchutzenbergerCongruence G z).quotientSemigroup.ZeroSimple := by
  let C := rightSchutzenbergerCongruence G z
  let Q := C.quotientSemigroup
  change Q.ZeroSimple
  intro source sourceNonzero target
  rcases C.projection_surjective source with ⟨x, sourceEq⟩
  rcases C.projection_surjective target with ⟨t, targetEq⟩
  subst source
  subst target
  have xNotInIdeal : ¬ (x ∈ I_z G z) := by
    intro xInIdeal
    apply sourceNonzero
    exact rightSchutzenberger_classOf_isZero_of_mem_I_z xInIdeal
  have zInSourceSandwich : G.PrincipalSandwichMem x z :=
    principalSandwichMem_of_not_mem_I_z xNotInIdeal
  rcases
      every_rightSchutzenberger_class_has_principalRepresentative_of_imageCondition
        G z imageCondition (C.classOf t) with
    ⟨y, yInZSandwich, yClass⟩
  rcases yInZSandwich.trans zInSourceSandwich with
    ⟨left, right, yFactor⟩
  refine ⟨C.classOf left, C.classOf right, ?_⟩
  change C.classOf t = C.classOf (G.mul (G.mul left x) right)
  exact yClass.symm.trans (congrArg C.classOf yFactor)

/-- At a regular element of a Brandt-law semigroup, the exact image condition
makes the right Schutzenberger quotient regular. If the projected `z` is zero,
every principal representative, and hence every class, collapses to it.
Otherwise zero-simplicity transfers regularity from the projected `z`. -/
theorem rightSchutzenbergerQuotient_regularSemigroup_of_imageCondition_brandtLaws
    {G : Semigroup S} {z : S} (laws : G.BrandtLaws)
    (zRegular : G.IsRegular z)
    (imageCondition : G.RightSchutzenbergerImageCondition z) :
    (rightSchutzenbergerCongruence G z).quotientSemigroup.RegularSemigroup := by
  let C := rightSchutzenbergerCongruence G z
  let Q := C.quotientSemigroup
  change Q.RegularSemigroup
  have zeroSimple : Q.ZeroSimple :=
    rightSchutzenbergerQuotient_zeroSimple_of_imageCondition
      (G := G) (z := z) imageCondition
  have zClassRegular : Q.IsRegular (C.classOf z) := by
    simpa only [C, Q] using
      rightSchutzenberger_classOf_isRegular zRegular
  by_cases zClassZero : Q.IsZero (C.classOf z)
  · intro target
    have targetEq : target = C.classOf z := by
      rcases
          every_rightSchutzenberger_class_has_principalRepresentative_of_imageCondition
            G z imageCondition target with
        ⟨y, yInZSandwich, yClass⟩
      rcases yInZSandwich with ⟨left, right, yFactor⟩
      calc
        target = C.classOf y := yClass.symm
        _ = C.classOf (G.mul (G.mul left z) right) :=
          congrArg C.classOf yFactor
        _ = Q.mul (Q.mul (C.classOf left) (C.classOf z))
            (C.classOf right) := rfl
        _ = Q.mul (C.classOf z) (C.classOf right) := by
          rw [zClassZero.2 (C.classOf left)]
        _ = C.classOf z := zClassZero.1 (C.classOf right)
    rw [targetEq]
    exact zClassRegular
  · exact zeroSimple.regularSemigroup_of_regular_nonzero
      (by
        simpa only [C, Q] using
          (laws.congruenceQuotient
            (rightSchutzenbergerCongruence G z)).squareEqualsCube)
      zClassZero zClassRegular

/-- Zero-simplicity and the inherited Brandt laws make distinct quotient
idempotents orthogonal. Regularity is not needed for this step. -/
theorem rightSchutzenbergerQuotient_idempotentsOrthogonal_of_imageCondition
    {G : Semigroup S} {z : S} (laws : G.BrandtLaws)
    (imageCondition : G.RightSchutzenbergerImageCondition z) :
    (rightSchutzenbergerCongruence G z).quotientSemigroup.IdempotentsOrthogonal :=
  ZeroSimple.idempotentsOrthogonal
    (rightSchutzenbergerQuotient_zeroSimple_of_imageCondition
      (G := G) (z := z) imageCondition)
    (laws.congruenceQuotient
      (rightSchutzenbergerCongruence G z)).squareEqualsCube
    (laws.congruenceQuotient
      (rightSchutzenbergerCongruence G z)).idempotentsCommute

end Semigroup

namespace CoRoots.S5_415

open SemigroupBasis

/-- The exact unresolved term-model statement: every regular term class has
surjective principal-sandwich image in its right Schutzenberger quotient. -/
def RightSchutzenbergerImageCompleteness : Prop :=
  forall z : TermSemigroup basis,
    (termSemigroup basis).IsRegular z ->
      (termSemigroup basis).RightSchutzenbergerImageCondition z

/-- The image condition supplies both components of the matrix-unit structure
at every regular element of a Brandt-law semigroup. -/
theorem rightSchutzenbergerMatrixUnitStructure_of_imageCondition
    {G : Semigroup S} {z : S} (laws : G.BrandtLaws)
    (zRegular : G.IsRegular z)
    (imageCondition : G.RightSchutzenbergerImageCondition z) :
    RightSchutzenbergerMatrixUnitStructure G z :=
  ⟨Semigroup.rightSchutzenbergerQuotient_regularSemigroup_of_imageCondition_brandtLaws
      laws zRegular imageCondition,
    Semigroup.rightSchutzenbergerQuotient_idempotentsOrthogonal_of_imageCondition
      laws imageCondition⟩

/-- The exact term-model image residual implies catalogue-Brandt validity in
all regular right Schutzenberger quotients. -/
theorem rightSchutzenbergerBrandtValidity_of_imageCompleteness
    (imageComplete : RightSchutzenbergerImageCompleteness) :
    RightSchutzenbergerBrandtValidity :=
  rightSchutzenbergerBrandtValidity_of_matrixUnitStructure
    (fun z zRegular =>
      rightSchutzenbergerMatrixUnitStructure_of_imageCondition
        termSemigroup_brandtLaws zRegular (imageComplete z zRegular))

/-- Thus the exact term-model image residual closes the published
minimal-counterexample reduction. -/
theorem derivationalCompleteness_of_imageCompleteness
    (imageComplete : RightSchutzenbergerImageCompleteness) :
    BrandtDerivationalCompleteness :=
  derivationalCompleteness_of_rightSchutzenbergerBrandtValidity
    (rightSchutzenbergerBrandtValidity_of_imageCompleteness imageComplete)

end CoRoots.S5_415
end SemigroupBasis
