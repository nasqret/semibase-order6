import SemigroupBasis.Subdirect

namespace SemigroupBasis

/-- A proof-producing normal form for the intersection of two semigroup
identity theories. -/
structure IntersectionNormalizer {B : Type v} {C : Type w} {alpha : Type z}
    (H : Semigroup B) (K : Semigroup C)
    (basis : List (Identity alpha)) where
  normal : Word alpha -> Word alpha
  derives_normal :
    forall word : Word alpha, Derives basis word (normal word)
  normal_eq_of_factor_valid :
    forall identity : Identity alpha,
      identity.SatisfiedBy H ->
        identity.SatisfiedBy K ->
          normal identity.lhs = normal identity.rhs

namespace IntersectionNormalizer

/-- A proof-producing intersection normalizer gives a complete basis once the
displayed basis is valid in both factors. -/
def toIntersectionBasis
    {B : Type v} {C : Type w} {alpha : Type z}
    {H : Semigroup B} {K : Semigroup C}
    {basis : List (Identity alpha)}
    (normalizer : IntersectionNormalizer H K basis)
    (leftModels : Models H basis)
    (rightModels : Models K basis) :
    IntersectionBasis H K basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := by
    intro identity leftValid rightValid
    have normalEqual :=
      normalizer.normal_eq_of_factor_valid identity leftValid rightValid
    exact Derives.trans (normalizer.derives_normal identity.lhs) <| by
      rw [normalEqual]
      exact Derives.symm (normalizer.derives_normal identity.rhs)

/-- A proof-producing intersection normalizer gives the same basis to every
semigroup represented subdirectly by its two factors. -/
theorem basisFor
    {A : Type u} {B : Type v} {C : Type w} {alpha : Type z}
    {G : Semigroup A} {H : Semigroup B} {K : Semigroup C}
    {basis : List (Identity alpha)}
    (normalizer : IntersectionNormalizer H K basis)
    (leftModels : Models H basis)
    (rightModels : Models K basis)
    (pair : SubdirectPair G H K) :
    BasisFor G basis :=
  IntersectionBasis.basisFor
    (normalizer.toIntersectionBasis leftModels rightModels) pair

end IntersectionNormalizer

end SemigroupBasis
