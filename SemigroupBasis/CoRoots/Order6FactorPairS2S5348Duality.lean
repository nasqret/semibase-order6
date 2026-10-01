import SemigroupBasis.CoRoots.S5_348Factors
import SemigroupBasis.CoRoots.S5_381Factors
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.Order6FactorPairS2S5348Duality

open SemigroupBasis

private def s2_2OppositeEmbedding :
    Embedding
      Generated.S2_2.table.semigroup.opposite
      Generated.S2_2.table.semigroup where
  toFun := id
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := Function.injective_id

/-- Validity in the cyclic order-two factor is preserved by reversing both
words. -/
theorem s2_2_reversed_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy Generated.S2_2.table.semigroup) :
    identity.reversed.SatisfiedBy
      Generated.S2_2.table.semigroup := by
  apply
    (Identity.satisfiedBy_opposite_iff_reversed
      identity Generated.S2_2.table.semigroup).mp
  exact s2_2OppositeEmbedding.pullback_identity identity valid

/-- The certified factor descriptions dualize `S5_348` validity into
`S5_381` validity of the reversed identity. -/
theorem s5_381_reversed_valid_of_s5_348_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_348.table.semigroup) :
    identity.reversed.SatisfiedBy
      Generated.Catalogue.S5_381.table.semigroup := by
  have factors :=
    (S5_348Factors.S5_348.valid_iff_factors identity).mp valid
  apply
    (S5_381Factors.S5_381.valid_iff_factors identity.reversed).mpr
  constructor
  · exact
      (Identity.satisfiedBy_opposite_iff_reversed
        identity Generated.S4_71.table.semigroup).mp factors.1
  · apply
      (Identity.satisfiedBy_opposite_iff_reversed
        identity.reversed
        SemigroupBasis.Examples.finalMarkerThree.semigroup).mpr
    simpa using factors.2

/-- Reverse a derivation between reversed words and recover a derivation
between the original words from the reversed basis. -/
theorem reverse_derivation_back
    {basis : List (Identity α)} {left right : Word α}
    (derivation : Derives basis left.reverse right.reverse) :
    Derives (reversedBasis basis) left right := by
  simpa using derivation.reverse

end SemigroupBasis.CoRoots.Order6FactorPairS2S5348Duality
