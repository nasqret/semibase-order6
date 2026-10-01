import SemigroupBasis.CoRoots.Order6SporadicSection14CanonicalUniqueness
import SemigroupBasis.CoRoots.Order6SporadicSection14Semantics

namespace SemigroupBasis.CoRoots.Order6SporadicSection14

open SemigroupBasis

private theorem betaDerives_of_canonical_eq
    (identity : Identity Nat)
    (canonicalEq :
      betaCanonicalWord identity.lhs =
        betaCanonicalWord identity.rhs) :
    Derives betaBasis identity.lhs identity.rhs := by
  exact (Beta.derivesCanonicalWord identity.lhs).trans <| by
    rw [canonicalEq]
    exact (Beta.derivesCanonicalWord identity.rhs).symm

namespace S6_12198

def completeness : BetaCompleteness publishedSemigroup where
  derives identity valid := by
    have firstOccurrences :=
      lrbValid_firstOccurrenceSequence_eq identity
        (valid_l identity valid)
    have canonicalValid :=
      betaCanonicalIdentity_valid publishedSemigroup publishedModels
        identity valid
    have canonicalFinal :=
      rightZeroValid_final_eq (betaCanonicalIdentity identity)
        (valid_r (betaCanonicalIdentity identity) canonicalValid)
    apply betaDerives_of_canonical_eq identity
    exact betaCanonicalWord_eq_of_invariants
      gapSeparator unarySeparator identity firstOccurrences
      canonicalValid canonicalFinal

theorem publishedBasisFor : BasisFor publishedSemigroup betaBasis :=
  publishedBasisFor_of_completeness completeness

theorem representativeBasisFor : BasisFor table.semigroup betaBasis :=
  representativeBasisFor_of_completeness completeness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBetaBasis :=
  representativeOppositeBasisFor_of_completeness completeness

end S6_12198

namespace S6_12526

def completeness : BetaCompleteness publishedSemigroup where
  derives identity valid := by
    have firstOccurrences :=
      lrbValid_firstOccurrenceSequence_eq identity
        (valid_l identity valid)
    have canonicalValid :=
      betaCanonicalIdentity_valid publishedSemigroup publishedModels
        identity valid
    have canonicalFinal :=
      rightZeroValid_final_eq (betaCanonicalIdentity identity)
        (valid_r (betaCanonicalIdentity identity) canonicalValid)
    apply betaDerives_of_canonical_eq identity
    exact betaCanonicalWord_eq_of_invariants
      gapSeparator unarySeparator identity firstOccurrences
      canonicalValid canonicalFinal

theorem publishedBasisFor : BasisFor publishedSemigroup betaBasis :=
  publishedBasisFor_of_completeness completeness

theorem representativeBasisFor : BasisFor table.semigroup betaBasis :=
  representativeBasisFor_of_completeness completeness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBetaBasis :=
  representativeOppositeBasisFor_of_completeness completeness

end S6_12526

namespace S6_14467

def completeness : BetaCompleteness publishedSemigroup where
  derives identity valid := by
    have firstOccurrences :=
      lrbValid_firstOccurrenceSequence_eq identity
        (valid_l identity valid)
    have canonicalValid :=
      betaCanonicalIdentity_valid publishedSemigroup publishedModels
        identity valid
    have canonicalFinal :=
      rightZeroValid_final_eq (betaCanonicalIdentity identity)
        (valid_r (betaCanonicalIdentity identity) canonicalValid)
    apply betaDerives_of_canonical_eq identity
    exact betaCanonicalWord_eq_of_invariants
      gapSeparator unarySeparator identity firstOccurrences
      canonicalValid canonicalFinal

theorem publishedBasisFor : BasisFor publishedSemigroup betaBasis :=
  publishedBasisFor_of_completeness completeness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite betaBasis :=
  representativeOppositeBasisFor_of_completeness completeness

theorem representativeBasisFor :
    BasisFor table.semigroup oppositeBetaBasis :=
  representativeBasisFor_of_completeness completeness

end S6_14467

end SemigroupBasis.CoRoots.Order6SporadicSection14
