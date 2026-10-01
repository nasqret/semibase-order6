import SemigroupBasis.CoRoots.Order6SporadicSection15AlphaNormalization
import SemigroupBasis.CoRoots.Order6SporadicSection15BetaNormalization
import SemigroupBasis.CoRoots.Order6SporadicSection15NormalizationAssembly

/-!
# Lee--Zhang Section 15: unconditional completeness

The alpha and beta branch normalizers assemble into the total canonical
normalizer.  The target-specific instances of Lemma 15.2 then discharge the
semantic uniqueness hypothesis at the normalization boundary.
-/

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis

/-- Every nonempty word derives to its deterministic Section 15 canonical
representative. -/
theorem canonicalNormalization : CanonicalNormalization :=
  canonicalNormalization_of_branches
    AlphaNormalization.listDerivesCanonical_of_branch_alpha
    BetaNormalization.listDerivesCanonical_of_branch_beta

namespace S6_2771

theorem completeness : Completeness publishedSemigroup :=
  completeness_of_normalization publishedSemigroup lemma15_2
    canonicalNormalization

theorem publishedBasisFor : BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_completeness completeness

theorem representativeBasisFor : BasisFor table.semigroup basis :=
  representativeBasisFor_of_completeness completeness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis :=
  representativeOppositeBasisFor_of_completeness completeness

end S6_2771

namespace S6_2772

theorem completeness : Completeness publishedSemigroup :=
  completeness_of_normalization publishedSemigroup lemma15_2
    canonicalNormalization

theorem publishedBasisFor : BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_completeness completeness

theorem representativeBasisFor : BasisFor table.semigroup basis :=
  representativeBasisFor_of_completeness completeness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis :=
  representativeOppositeBasisFor_of_completeness completeness

end S6_2772

namespace S6_2773

theorem completeness : Completeness publishedSemigroup :=
  completeness_of_normalization publishedSemigroup lemma15_2
    canonicalNormalization

theorem publishedBasisFor : BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_completeness completeness

theorem representativeBasisFor : BasisFor table.semigroup basis :=
  representativeBasisFor_of_completeness completeness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis :=
  representativeOppositeBasisFor_of_completeness completeness

end S6_2773

namespace S6_5240

theorem completeness : Completeness publishedSemigroup :=
  completeness_of_normalization publishedSemigroup lemma15_2
    canonicalNormalization

theorem publishedBasisFor : BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_completeness completeness

theorem representativeBasisFor : BasisFor table.semigroup basis :=
  representativeBasisFor_of_completeness completeness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis :=
  representativeOppositeBasisFor_of_completeness completeness

end S6_5240

namespace S6_5241

theorem completeness : Completeness publishedSemigroup :=
  completeness_of_normalization publishedSemigroup lemma15_2
    canonicalNormalization

theorem publishedBasisFor : BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_completeness completeness

theorem representativeBasisFor : BasisFor table.semigroup basis :=
  representativeBasisFor_of_completeness completeness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis :=
  representativeOppositeBasisFor_of_completeness completeness

end S6_5241

namespace S6_9313

theorem completeness : Completeness publishedSemigroup :=
  completeness_of_normalization publishedSemigroup lemma15_2
    canonicalNormalization

theorem publishedBasisFor : BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_completeness completeness

theorem representativeBasisFor : BasisFor table.semigroup basis :=
  representativeBasisFor_of_completeness completeness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis :=
  representativeOppositeBasisFor_of_completeness completeness

end S6_9313

end SemigroupBasis.CoRoots.Order6SporadicSection15
