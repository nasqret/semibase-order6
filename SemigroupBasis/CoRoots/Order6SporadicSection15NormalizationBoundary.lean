import SemigroupBasis.CoRoots.Order6SporadicSection15Derivations
import SemigroupBasis.CoRoots.Order6SporadicSection15TargetUniqueness

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis

/-- The sole remaining global proof obligation after semantic uniqueness:
every nonempty word has an actual word representative of the deterministic
canonical list, reached by the Section 15 basis. -/
structure CanonicalNormalization : Prop where
  normalize :
    ∀ word : Word Nat,
      ∃ normalized : Word Nat,
        Derives basis word normalized ∧
          normalized.toList = CanonicalData.canonicalList word.toList

theorem derives_of_normalization
    (normalization : CanonicalNormalization)
    {left right : Word Nat}
    (canonicalEqual :
      CanonicalData.canonicalList left.toList =
        CanonicalData.canonicalList right.toList) :
    Derives basis left right := by
  obtain ⟨leftNormal, leftDerives, leftShape⟩ :=
    normalization.normalize left
  obtain ⟨rightNormal, rightDerives, rightShape⟩ :=
    normalization.normalize right
  have normalLists : leftNormal.toList = rightNormal.toList :=
    leftShape.trans (canonicalEqual.trans rightShape.symm)
  have normalWords : leftNormal = rightNormal :=
    Word.toList_injective normalLists
  subst rightNormal
  exact leftDerives.trans rightDerives.symm

/-- Canonical normalization plus target semantic separation inhabits the
foundation's completeness interface. The factor arguments in that interface
remain available but are already consumed by `invariants`. -/
theorem completeness_of_normalization
    {S : Type u} (candidate : Semigroup S)
    (invariants :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy candidate →
          Lemma15_2Invariants identity.lhs identity.rhs)
    (normalization : CanonicalNormalization) :
    Completeness candidate where
  derives := by
    intro identity valid _countValid _finalValid _initialValid
    exact derives_of_normalization normalization
      ((invariants identity valid).canonicalList_eq)

namespace S6_2771

theorem publishedBasisFor_of_normalization
    (normalization : CanonicalNormalization) :
    BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_completeness <|
    completeness_of_normalization publishedSemigroup lemma15_2 normalization

end S6_2771

namespace S6_2772

theorem publishedBasisFor_of_normalization
    (normalization : CanonicalNormalization) :
    BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_completeness <|
    completeness_of_normalization publishedSemigroup lemma15_2 normalization

end S6_2772

namespace S6_2773

theorem publishedBasisFor_of_normalization
    (normalization : CanonicalNormalization) :
    BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_completeness <|
    completeness_of_normalization publishedSemigroup lemma15_2 normalization

end S6_2773

namespace S6_5240

theorem publishedBasisFor_of_normalization
    (normalization : CanonicalNormalization) :
    BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_completeness <|
    completeness_of_normalization publishedSemigroup lemma15_2 normalization

end S6_5240

namespace S6_5241

theorem publishedBasisFor_of_normalization
    (normalization : CanonicalNormalization) :
    BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_completeness <|
    completeness_of_normalization publishedSemigroup lemma15_2 normalization

end S6_5241

namespace S6_9313

theorem publishedBasisFor_of_normalization
    (normalization : CanonicalNormalization) :
    BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_completeness <|
    completeness_of_normalization publishedSemigroup lemma15_2 normalization

end S6_9313

end SemigroupBasis.CoRoots.Order6SporadicSection15
