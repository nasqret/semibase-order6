import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon

/-!
# Parametric transport of an already-certified intersection normalizer

This is the common component approved by `msg-0273`.  It does not construct
an unrestricted seed, infer factor separation from finite tables, or invoke
quotient normality.  Every required derivation and unrestricted semantic
implication remains an explicit theorem argument.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon

open SemigroupBasis

/-- Transport a certified intersection normalizer across displayed-law
derivations and unrestricted implications from the new factors to the seed
factors.  The transported normal word is exactly the seed normal word. -/
def transportNormalizer
    {A : Type u} {B : Type v} {C : Type w} {D : Type z}
    {H : Semigroup A} {K : Semigroup B}
    {H' : Semigroup C} {K' : Semigroup D}
    {sourceBasis targetBasis : List (Identity Nat)}
    (seed : IntersectionNormalizer H K sourceBasis)
    (sourceToTarget :
      ∀ law : Identity Nat,
        law ∈ sourceBasis → Derives targetBasis law.lhs law.rhs)
    (leftTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy H' → identity.SatisfiedBy H)
    (rightTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy K' → identity.SatisfiedBy K) :
    IntersectionNormalizer H' K' targetBasis where
  normal := seed.normal
  derives_normal := by
    intro word
    have sourceDerivation :
        Derives sourceBasis word (seed.normal word) :=
      seed.derives_normal word
    exact Derives.transport sourceToTarget sourceDerivation
  normal_eq_of_factor_valid := by
    intro identity leftValid rightValid
    have sourceLeftValid : identity.SatisfiedBy H :=
      leftTheory identity leftValid
    have sourceRightValid : identity.SatisfiedBy K :=
      rightTheory identity rightValid
    exact
      seed.normal_eq_of_factor_valid identity sourceLeftValid sourceRightValid

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon
