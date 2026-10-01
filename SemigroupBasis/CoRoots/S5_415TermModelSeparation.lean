import SemigroupBasis.CoRoots.S5_415CellFactorization
import SemigroupBasis.CoRoots.S5_415PublishedLaws
import SemigroupBasis.CoRoots.S5_415QuotientRegularity
import SemigroupBasis.HomomorphicImage
import SemigroupBasis.KublanovskiiSeparation

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-- The free term semigroup presented by the three `S5_415` laws models those
laws by construction. -/
theorem termSemigroup_modelsBasis :
    Models (termSemigroup basis) basis :=
  termSemigroup_models basis

/-- The presented term semigroup satisfies the pointwise Brandt laws used by
the published separation argument. -/
theorem termSemigroup_brandtLaws :
    (termSemigroup basis).BrandtLaws :=
  brandtLaws_of_models termSemigroup_modelsBasis

/-- Idempotents commute in the presented term semigroup. -/
theorem termSemigroup_idempotentsCommute :
    (termSemigroup basis).IdempotentsCommute :=
  termSemigroup_brandtLaws.idempotentsCommute

/-- Every right Schutzenberger quotient of the presented term semigroup still
models the three basis identities. -/
theorem rightSchutzenbergerQuotient_modelsBasis
    (z : TermSemigroup basis) :
    Models
      (Semigroup.rightSchutzenbergerCongruence
        (termSemigroup basis) z).quotientSemigroup
      basis :=
  (Semigroup.rightSchutzenbergerCongruence
      (termSemigroup basis) z).quotient_models
    termSemigroup_modelsBasis

/-- Consequently every such quotient satisfies the pointwise Brandt laws. -/
theorem rightSchutzenbergerQuotient_brandtLaws
    (z : TermSemigroup basis) :
    (Semigroup.rightSchutzenbergerCongruence
      (termSemigroup basis) z).quotientSemigroup.BrandtLaws :=
  brandtLaws_of_models (rightSchutzenbergerQuotient_modelsBasis z)

/-- Every term class represented by a repeated word is regular. This is the
term-model form of Volkov's Lemma 7. -/
theorem repeatedTermClass_isRegular
    {word : Word Nat} (repeated : RepeatedWord word) :
    (termSemigroup basis).IsRegular (termClass basis word) :=
  (repeatedWord_inverseWitness repeated).termClass_isRegular

/-- Distinct classes represented by repeated words are separated by one of
the two canonical right Schutzenberger quotient projections. -/
theorem distinctRepeatedTermClasses_projection_separation
    {left right : Word Nat}
    (leftRepeated : RepeatedWord left)
    (rightRepeated : RepeatedWord right)
    (notDerivable : ¬ Derives basis left right) :
    let G := termSemigroup basis
    let leftClass := termClass basis left
    let rightClass := termClass basis right
    (Semigroup.rightSchutzenbergerCongruence G leftClass).projection.toFun
          leftClass ≠
        (Semigroup.rightSchutzenbergerCongruence G leftClass).projection.toFun
          rightClass ∨
      (Semigroup.rightSchutzenbergerCongruence G rightClass).projection.toFun
          leftClass ≠
        (Semigroup.rightSchutzenbergerCongruence G rightClass).projection.toFun
          rightClass := by
  dsimp
  have classesDifferent :
      termClass basis left ≠ termClass basis right := by
    intro equalClasses
    exact notDerivable ((termClass_eq_iff_derives basis).mp equalClasses)
  exact
    Semigroup.distinct_regular_rightSchutzenberger_projection_separation
      termSemigroup_idempotentsCommute
      (repeatedTermClass_isRegular leftRepeated)
      (repeatedTermClass_isRegular rightRepeated)
      classesDifferent

end SemigroupBasis.CoRoots.S5_415
