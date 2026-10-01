import SemigroupBasis.CoRoots.Order6SporadicSection14CanonicalUniqueness
import SemigroupBasis.CoRoots.Order6SporadicSection14Semantics

namespace SemigroupBasis.CoRoots.Order6SporadicSection14

open SemigroupBasis

private theorem alphaDerives_of_canonical_eq
    (identity : Identity Nat)
    (canonicalEq :
      alphaCanonicalWord identity.lhs =
        alphaCanonicalWord identity.rhs) :
    Derives alphaBasis identity.lhs identity.rhs := by
  exact (Alpha.derivesCanonicalWord identity.lhs).trans <| by
    rw [canonicalEq]
    exact (Alpha.derivesCanonicalWord identity.rhs).symm

namespace S6_12399

def completeness : AlphaCompleteness publishedSemigroup where
  derives identity valid := by
    have firstOccurrences :=
      lrbValid_firstOccurrenceSequence_eq identity
        (valid_l identity valid)
    have canonicalValid :=
      alphaCanonicalIdentity_valid publishedSemigroup publishedModels
        identity valid
    have canonicalFinal :=
      rightZeroValid_final_eq (alphaCanonicalIdentity identity)
        (valid_r (alphaCanonicalIdentity identity) canonicalValid)
    have canonicalSimpleFinal :=
      finalMarkerValid_simpleFinalVariable_eq
        (alphaCanonicalIdentity identity)
        (valid_j (alphaCanonicalIdentity identity) canonicalValid)
    apply alphaDerives_of_canonical_eq identity
    exact alphaCanonicalWord_eq_of_invariants
      gapSeparator identity firstOccurrences canonicalValid
      canonicalFinal canonicalSimpleFinal

theorem publishedBasisFor : BasisFor publishedSemigroup alphaBasis :=
  publishedBasisFor_of_completeness completeness

theorem representativeBasisFor : BasisFor table.semigroup alphaBasis :=
  representativeBasisFor_of_completeness completeness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeAlphaBasis :=
  representativeOppositeBasisFor_of_completeness completeness

end S6_12399

end SemigroupBasis.CoRoots.Order6SporadicSection14
