import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon
import SemigroupBasis.DerivationQuotient

/-!
# Unrestricted quotient representatives as proof-producing normal words

This module supplies a common refinement used by the Layer-C pair-specific
sections.  It chooses one word in every derivability class.  The construction
ranges over arbitrary nonempty words and uses neither the Layer-A oracle cases
nor a finite-rank projection.

The input `IntersectionBasis` is deliberately explicit: the chosen
representative does not manufacture completeness.  It only turns an already
proved unrestricted pair-specific derivation theorem into the reviewed
`IntersectionNormalizer` interface.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon

open SemigroupBasis

/-- The representative selected by the canonical projection from words to
their derivability quotient. -/
noncomputable def quotientNormal
    (basis : List (Identity alpha)) (word : Word alpha) : Word alpha :=
  (derivationCongruence basis).projectionSplitSurjection.preimage
    (termClass basis word)

/-- The selected representative belongs to the input word's exact
derivability class. -/
theorem derives_quotientNormal
    (basis : List (Identity alpha)) (word : Word alpha) :
    Derives basis word (quotientNormal basis word) := by
  apply (termClass_eq_iff_derives basis).mp
  exact
    ((derivationCongruence basis).projectionSplitSurjection.right_inverse
      (termClass basis word)).symm

/-- Equal derivability classes select literally equal representatives. -/
theorem quotientNormal_eq_of_derives
    {basis : List (Identity alpha)} {left right : Word alpha}
    (derivation : Derives basis left right) :
    quotientNormal basis left = quotientNormal basis right := by
  apply congrArg
    (derivationCongruence basis).projectionSplitSurjection.preimage
  exact (termClass_eq_iff_derives basis).mpr derivation

/-- Refine an unrestricted pair-specific completeness theorem to the public
proof-producing normalizer API. -/
noncomputable def IntersectionBasis.toQuotientNormalizer
    {B : Type v} {C : Type w} {alpha : Type z}
    {H : Semigroup B} {K : Semigroup C}
    {basis : List (Identity alpha)}
    (intersection : IntersectionBasis H K basis) :
    IntersectionNormalizer H K basis where
  normal := quotientNormal basis
  derives_normal := derives_quotientNormal basis
  normal_eq_of_factor_valid := by
    intro identity leftValid rightValid
    exact quotientNormal_eq_of_derives
      (intersection.complete identity leftValid rightValid)

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon
